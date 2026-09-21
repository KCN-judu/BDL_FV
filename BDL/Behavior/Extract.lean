import BDL.Behavior.Boundary
import BDL.Behavior.System

/-!
# Extract — "Package as Component" (Phase 8b)

Given a finite design `D` and a member list `G`, extraction produces

* the **component** `comp`: the members' declarations, unchanged, plus one
  unresolved copy of each crossing-in declaration (its required ports);
  its provided ports are the crossing-out members; every clock of `D` is a
  clock parameter; concepts stay shared; sinks stay external and their
  drive edges stay with the members that drive them;
* the **residual** `resid`: the non-members' declarations, unchanged, plus
  one unresolved copy of each crossing-out member (its required ports);
  its provided ports are the crossing-in declarations;
* the **system**: instance 0 = residual, instance 1 = component, with the
  clock parameters mapped identically, and one direct binding per crossing
  declaration reconnecting the two sides.

Both templates are *restrictions* of `D` to a kept set plus a port set
(`restrict`); the same construction serves both sides.

Identity policy (§20 of the brief).  Before packaging, grouping changes
no identity.  The two *templates* keep the original identities (all below
the width `W`).  After packaging, the flattened system carries Phase-8a
fresh identities: an original `n` lives at `W + n` in the residual and at
`2W + n` in the component; the crossing declarations additionally have a
port copy on the other side.  A future second instance of the component
receives identities `3W + n`, and so on — component identity is instance
identity, never the group's.

Nothing here is semantic: the component body is the original members'
declarations, and the reconnection is Phase-1 realization (Phase 8a
binding).
-/

namespace BDL
open BDL.Output (OutputId OutputSpec)
open BDL.Clock (ClockEnv)
open Boundary

namespace Extract

def unresolve (h : DesignDecl) : DesignDecl := ⟨h.id, h.interface, none⟩

/-! ## Restriction of a design to a kept set plus a port set -/

/-- Keep the declarations satisfying `keep` as they are; keep those
    satisfying `port` (and not `keep`) as unresolved copies; drop the rest. -/
def restrictΔ (D : Design) (keep port : DeclId → Bool) : DeclEnv := fun d =>
  if keep d then D.Δ d else if port d then (D.Δ d).map unresolve else none

def restrictΚ (D : Design) (keep port : DeclId → Bool) : ClockEnv := fun d =>
  if keep d || port d then D.Κ d else none

def restrictβ (D : Design) (keep : DeclId → Bool) : Output.DriveEnv := fun d =>
  if keep d then D.β d else none

def restrict (D : Design) (keep port : DeclId → Bool) : Design :=
  ⟨restrictΔ D keep port, D.Θ, restrictΚ D keep port, D.Ω, restrictβ D keep⟩

/-- The port a declaration presents: its own interface and clock. -/
def portOf (D : Design) (d : DeclId) : Port :=
  ⟨d, (match D.Δ d with | some h => h.interface | none => ⟨.nat, []⟩), D.Κ d⟩

/-- A template: a restriction of `D` with the given required and provided
    port lists and every clock of `D` as a parameter. -/
def template (D : Design) (keep port : DeclId → Bool) (required provided : List DeclId)
    (clocks : List ClockId) (W : Nat) : BehaviorComponent :=
  { iface :=
      { required := required.map (portOf D)
        provided := provided.map (portOf D)
        params := []
        clockParams := clocks }
    design := restrict D keep port
    width := W
    internalConcept := fun _ => false
    internalOut := fun _ => false }

/-! ## The extraction input and its two templates -/

/-- The input of an extraction. -/
structure Input where
  D : Design
  ids : List DeclId
  G : List DeclId
  /-- Clock-parameter candidates: every clock the design uses. -/
  clocks : List ClockId
  /-- The system width: above every identity of `D`. -/
  W : Nat

namespace Input

variable (X : Input)

def isMember (d : DeclId) : Bool := X.G.contains d
def isCrossIn (d : DeclId) : Bool := (crossIn X.D X.ids X.G).contains d
def isCrossOut (d : DeclId) : Bool := (crossOut X.D X.ids X.G).contains d
def isOutside (d : DeclId) : Bool := X.ids.contains d && !X.G.contains d

/-- The extracted component: members kept, crossing-in as required ports,
    crossing-out as provided ports. -/
def comp : BehaviorComponent :=
  template X.D X.isMember X.isCrossIn (crossIn X.D X.ids X.G) (crossOut X.D X.ids X.G) X.clocks X.W

/-- The residual: non-members kept, crossing-out as required ports,
    crossing-in as provided ports. -/
def resid : BehaviorComponent :=
  template X.D X.isOutside X.isCrossOut (crossOut X.D X.ids X.G) (crossIn X.D X.ids X.G) X.clocks X.W

/-! ## The system: residual (instance 0) + one instance of the component (instance 1) -/

def bindings : List Binding :=
  (crossIn X.D X.ids X.G).map (fun r => ⟨.port 0 r, 1, r, none⟩) ++
  (crossOut X.D X.ids X.G).map (fun p => ⟨.port 1 p, 0, p, none⟩)

def system : BehaviorSystem :=
  { W := X.W
    insts := [⟨X.resid, fun c => c⟩, ⟨X.comp, fun c => c⟩]
    bindings := X.bindings
    Θg := X.D.Θ
    Ωg := X.D.Ω }

/-- The result of "Package as Component". -/
structure Result where
  component : BehaviorComponent
  residual : BehaviorComponent
  system : BehaviorSystem

def extract : Result := ⟨X.comp, X.resid, X.system⟩

/-- The extracted-and-flattened design. -/
def flat : Design := X.system.flatten

/-! ## Identity correspondence -/

/-- Where an original declaration lives in the flattened system: members
    in the component instance, non-members in the residual instance. -/
def home (d : DeclId) : DeclId :=
  if X.isMember d then X.system.declOf 1 d else X.system.declOf 0 d

/-- The identities that belong to the component *template* (before any
    instantiation): the original member identities and the crossing-in
    port identities — all below `W`. -/
def templateIds : List DeclId := X.G ++ crossIn X.D X.ids X.G

theorem templateIds_bounded (h : ∀ d ∈ X.ids, d.n < X.W) (hG : ∀ d ∈ X.G, d ∈ X.ids) :
    ∀ d ∈ X.templateIds, d.n < X.W := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact h d (hG d hd)
  · exact h d ((mem_crossIn _ _ _).mp hd).1

/-! ## Membership lemmas -/

theorem isMember_iff {d : DeclId} : X.isMember d = true ↔ d ∈ X.G := by simp [isMember]
theorem isCrossIn_iff {d : DeclId} : X.isCrossIn d = true ↔ d ∈ crossIn X.D X.ids X.G := by simp [isCrossIn]
theorem isCrossOut_iff {d : DeclId} : X.isCrossOut d = true ↔ d ∈ crossOut X.D X.ids X.G := by simp [isCrossOut]
theorem isOutside_iff {d : DeclId} : X.isOutside d = true ↔ d ∈ X.ids ∧ d ∉ X.G := by simp [isOutside]

theorem crossIn_not_member {d : DeclId} (h : d ∈ crossIn X.D X.ids X.G) : X.isMember d = false := by
  have := ((mem_crossIn _ _ _).mp h).2.1
  simpa [isMember] using this

theorem crossOut_not_outside {d : DeclId} (h : d ∈ crossOut X.D X.ids X.G) : X.isOutside d = false := by
  have := ((mem_crossOut _ _ _).mp h).1
  simp [isOutside, this]

end Input
end Extract
end BDL
