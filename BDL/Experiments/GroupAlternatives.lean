import BDL.Behavior.ExtractPreservation

/-!
# Phase 8b — Grouping and extraction: worked example and counterexamples

§1 a small design, grouped, with its boundary projections computed and
its extraction executed against the original; §2–§7 the six negative
examples of the brief:

1. an internal dependency exposed as a required port;
2. an external dependency hidden;
3. a global clock captured as private instead of parameterized;
4. a physical output converted into a semantic port;
5. a tuple-return encoding forcing unrelated dependencies together;
6. an aggregate socket encoded as a fan-out edge, creating false
   dependencies.

All facts are on finite data, by `decide` or short proofs.
-/

namespace BDL.Experiments.Group
open BDL BDL.Reactive BDL.Clock BDL.Output Boundary BDL.Extract

/-! ## §1 The design: `a` (input), `f := a`, `g := f`, `u := g` -/

def a : DeclId := ⟨0⟩
def f : DeclId := ⟨1⟩
def g : DeclId := ⟨2⟩
def u : DeclId := ⟨3⟩
def c0 : ClockId := ⟨0⟩

def N : Ty := .q Dim.zero

def D : Design where
  Δ := .ofList [⟨a, ⟨N, []⟩, none⟩, ⟨f, ⟨N, []⟩, some (.declRef a)⟩,
                ⟨g, ⟨N, []⟩, some (.declRef f)⟩, ⟨u, ⟨N, []⟩, some (.declRef g)⟩]
  Θ := fun _ => none
  Κ := fun d => if d.n < 4 then some c0 else none
  Ω := fun _ => none
  β := fun _ => none

def ids : List DeclId := [a, f, g, u]
/-- The group: `f` and `g`. -/
def G : List DeclId := [f, g]

/-- Grouping is metadata: the grouped design erases to `D`. -/
theorem grouped_erases : (GroupedDesign.group ⟨D, []⟩ ⟨0⟩ G).eraseGroups = D := rfl

/-- **Boundary inference.**  `a` crosses in, `g` crosses out, `f` is private;
    the internal edge `g → f` creates no port. -/
theorem boundary :
    crossIn D ids G = [a] ∧ crossOut D ids G = [g] ∧ privateMembers D ids G = [f] ∧
    openMembers D G = [] ∧ externalInputs D ids G = [a] ∧ externalOutputs D ids G = [g] := by decide

theorem internal_edge : InternalEdge D G g f := ⟨by decide, by decide, by decide⟩

/-! ### Extraction, executed -/

def X : Extract.Input := ⟨D, ids, G, [c0], 8⟩

/-- The component's boundary: required `a`, provided `g`; the residual's
    boundary is the mirror image. -/
theorem comp_boundary :
    (X.comp.iface.required.map (·.id) = [a]) ∧ (X.comp.iface.provided.map (·.id) = [g]) ∧
    (X.resid.iface.required.map (·.id) = [g]) ∧ (X.resid.iface.provided.map (·.id) = [a]) := by decide

/-- The component template keeps `f`, `g` as they are and `a` as an
    unresolved port; it does not contain `u`. -/
theorem comp_template :
    X.comp.design.Δ f = some ⟨f, ⟨N, []⟩, some (.declRef a)⟩ ∧
    X.comp.design.Δ a = some ⟨a, ⟨N, []⟩, none⟩ ∧ X.comp.design.Δ u = none := by decide

/-- Identities after packaging: `home a = 8 + 0`, `home f = 16 + 1`, and
    the two port copies. -/
theorem flat_ids : X.home a = ⟨8⟩ ∧ X.home f = ⟨17⟩ ∧ X.home g = ⟨18⟩ ∧ X.home u = ⟨11⟩ := by decide

/-- The reconnection: the component's copy of `a` reads the residual's `a`;
    the residual's copy of `g` reads the component's `g`. -/
theorem flat_bindings :
    X.flat.Δ.realizationOf (X.system.declOf 1 a) = some (.declRef (X.home a)) ∧
    X.flat.Δ.realizationOf (X.system.declOf 0 g) = some (.declRef (X.home g)) := by decide

/-- Original bodies are carried unchanged (up to identity), and the input stays open. -/
theorem flat_bodies :
    X.flat.Δ.realizationOf (X.home f) = some (.declRef (X.system.declOf 1 a)) ∧
    X.flat.Δ.realizationOf (X.home u) = some (.declRef (X.system.declOf 0 g)) ∧
    X.flat.Δ.realizationOf (X.home a) = none := by decide

def I : Reactive.Input := fun d t => if d = a then .nat (t + 10) else .nat 0

def runOrig (d : DeclId) (t : Nat) : Option Nat := (evalF D.Δ I 32 t [] (.declRef d)).bind Value.toNat?
def runFlat (d : DeclId) (t : Nat) : Option Nat :=
  (evalF X.flat.Δ (X.liftInput I) 32 t [] (.declRef (X.home d))).bind Value.toNat?

/-- **Theorem R, executed.**  Every original declaration and its home copy
    agree, tick by tick. -/
theorem extraction_preserves_trace :
    [runOrig f 0, runOrig g 2, runOrig u 5] = [runFlat f 0, runFlat g 2, runFlat u 5] ∧
    [runOrig f 0, runOrig g 2, runOrig u 5] = [some 10, some 12, some 15] := by decide

/-! ## §2 Counterexample 1 — an internal dependency exposed as required -/

/-- A naive boundary: *every* reference of a member is a required input. -/
def naiveRequired : List DeclId := (G.map fun m => (D.Δ.realizationOf m).map Expr.refs |>.getD []).flatten

/-- `f` is a required input under the naive rule, though it is internal. -/
theorem naive_exposes_internal : f ∈ naiveRequired ∧ f ∉ crossIn D ids G := by decide

/-- The consequence is semantic: with `f` an open port, `g` no longer computes
    `a` but reads whatever the port is fed. -/
def naiveComp : DeclEnv := .ofList [⟨a, ⟨N, []⟩, none⟩, ⟨f, ⟨N, []⟩, none⟩, ⟨g, ⟨N, []⟩, some (.declRef f)⟩]
def Ibad : Reactive.Input := fun d t => if d = a then .nat (t + 10) else .nat 99

theorem naive_changes_behaviour :
    (evalF naiveComp Ibad 32 0 [] (.declRef g)).bind Value.toNat? = some 99 ∧
    (evalF D.Δ Ibad 32 0 [] (.declRef g)).bind Value.toNat? = some 10 := by decide

/-! ## §3 Counterexample 2 — an external dependency hidden -/

/-- A naive boundary that lists only the members' *own* open declarations
    as inputs forgets `a`: the template then has a dangling reference. -/
def hiddenComp : DeclEnv := .ofList [⟨f, ⟨N, []⟩, some (.declRef a)⟩, ⟨g, ⟨N, []⟩, some (.declRef f)⟩]

theorem hidden_dependency_ill_typed :
    hiddenComp.tyView a = none ∧
    ¬ HasType (fun _ => none) hiddenComp Grant.none [] (.declRef a) N := by decide

/-- The correct inference lists `a` (Theorem K). -/
theorem correct_lists_external : a ∈ crossIn D ids G := by decide

/-! ## §4 Counterexample 3 — a global clock captured as private -/

/-- The extracted component with *no* clock parameters: `c0` becomes an
    internal clock and is freshened at instantiation, so the component's
    ports run in a domain the residual cannot name. -/
def captured : BehaviorComponent := { X.comp with iface := { X.comp.iface with clockParams := [] } }

theorem captured_clock_mismatch :
    (Ren.inst captured 8 1 (fun c => c)).c c0 ≠ c0 ∧ (Ren.inst X.comp 8 1 (fun c => c)).c c0 = c0 ∧
    (Ren.inst X.resid 8 0 (fun c => c)).c c0 = c0 := by decide

/-- Hence the reconnecting binding `C.a := R.a` would fail its clock
    condition under the captured component, while it holds under the
    parameterized one. -/
theorem captured_binding_clock_fails :
    ¬ ((some c0).map (Ren.inst X.resid 8 0 (fun c => c)).c = none ∨
       (some c0).map (Ren.inst X.resid 8 0 (fun c => c)).c = (some c0).map (Ren.inst captured 8 1 (fun c => c)).c) ∧
    ((some c0).map (Ren.inst X.resid 8 0 (fun c => c)).c = (some c0).map (Ren.inst X.comp 8 1 (fun c => c)).c) := by
  decide

/-! ## §5 Counterexample 4 — a physical output converted into a semantic port -/

def light : OutputId := ⟨1⟩

/-- The same design, with `g` driving the light. -/
def D₂ : Design := { D with Ω := fun o => if o = light then some ⟨N, c0⟩ else none,
                            β := fun d => if d = g then some light else none }
def X₂ : Extract.Input := ⟨D₂, ids, G, [c0], 8⟩

/-- Correct extraction: the drive edge stays with the member's home copy;
    the light is complete in the flattened design. -/
theorem drive_kept :
    X₂.flat.β (X₂.home g) = some light ∧ X₂.flat.β (X₂.system.declOf 0 g) = none ∧
    CompleteOutputs X₂.flat.β [light] := by
  refine ⟨by decide, by decide, ?_⟩
  intro o ho
  simp only [List.mem_singleton] at ho; subst ho
  exact ⟨X₂.home g, by decide⟩

/-- The naive conversion: strip the drive from the component and let a
    residual pass-through port drive the light instead.  The *component*
    then describes a behaviour with no physical effect: instantiated on its
    own (or a second time), it drives nothing. -/
def converted : BehaviorComponent :=
  { X₂.comp with design := { X₂.comp.design with β := fun _ => none } }

def convertedAlone : BehaviorSystem :=
  { W := 8, insts := [⟨converted, fun c => c⟩], bindings := [], Θg := fun _ => none, Ωg := D₂.Ω }

theorem converted_loses_effect :
    converted.design.β g = none ∧ D₂.β g = some light ∧ ¬ CompleteOutputs convertedAlone.flatten.β [light] := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  obtain ⟨d, hd⟩ := h light (List.mem_singleton.mpr rfl)
  -- every drive edge of the flattened system comes from an instance, and the only instance drives nothing
  obtain ⟨k, I, n, o, hI, hβ, -, -, -⟩ := BehaviorSystem.unionβ_some hd
  cases k with
  | zero => cases hI; exact nomatch hβ
  | succ k => cases hI

/-! ## §6 Counterexample 5 — the tuple-return encoding -/

def b : DeclId := ⟨4⟩
def fg : DeclId := ⟨5⟩
def u' : DeclId := ⟨6⟩

/-- Two independent mappings `f := a`, `g := b` and a consumer of `f` only. -/
def D₃ : Design := { D with Δ := .ofList [⟨a, ⟨N, []⟩, none⟩, ⟨b, ⟨N, []⟩, none⟩,
    ⟨f, ⟨N, []⟩, some (.declRef a)⟩, ⟨g, ⟨N, []⟩, some (.declRef b)⟩, ⟨u, ⟨N, []⟩, some (.declRef f)⟩] }

/-- The "one tuple-returning function" encoding: a single declaration
    computing both from both inputs, and the consumer reading it. -/
def tupleBody : Expr := .app (.app (.prim (.add Dim.zero)) (.declRef a)) (.declRef b)
def D₃' : Design := { D with Δ := .ofList [⟨a, ⟨N, []⟩, none⟩, ⟨b, ⟨N, []⟩, none⟩,
    ⟨fg, ⟨N, []⟩, some tupleBody⟩, ⟨u', ⟨N, []⟩, some (.declRef fg)⟩] }

/-- In the atomic design the consumer of `f` does not depend on `b`; in the
    tuple encoding it does, instantaneously, through `fg`. -/
theorem tuple_forces_dependency :
    ¬ DependsOn D₃.Δ u b ∧ ¬ DependsOn D₃.Δ f b ∧
    InstDependsOn D₃'.Δ u' fg ∧ InstDependsOn D₃'.Δ fg b := by decide

/-- The correct extraction of `{f, g}` from `D₃` provides `f` and `g` as
    two independent ports and requires `a` and `b` independently. -/
def X₃ : Extract.Input := ⟨D₃, [a, b, f, g, u], G, [c0], 8⟩

theorem two_ports :
    X₃.comp.iface.provided.map (·.id) = [f] ∧ X₃.comp.iface.required.map (·.id) = [a, b] ∧
    ¬ DependsOn X₃.comp.design.Δ f b := by decide

/-! ## §7 Counterexample 6 — the aggregate socket as a fan-out edge -/

def c : DeclId := ⟨7⟩
def h : DeclId := ⟨8⟩
def agg : DeclId := ⟨9⟩

/-- Members `f := a` and `h := c`; the group's input socket is `{a, c}`. -/
def D₄ : Design := { D with Δ := .ofList [⟨a, ⟨N, []⟩, none⟩, ⟨c, ⟨N, []⟩, none⟩,
    ⟨f, ⟨N, []⟩, some (.declRef a)⟩, ⟨h, ⟨N, []⟩, some (.declRef c)⟩] }

/-- A fan-out encoding: a socket declaration `agg := a` that every member is
    wired to read (here `h` reads `agg` in a dead branch). -/
def D₄' : Design := { D with Δ := .ofList [⟨a, ⟨N, []⟩, none⟩, ⟨c, ⟨N, []⟩, none⟩,
    ⟨agg, ⟨N, []⟩, some (.declRef a)⟩,
    ⟨f, ⟨N, []⟩, some (.declRef agg)⟩,
    ⟨h, ⟨N, []⟩, some (.app (.app (.app (.prim (.ite N)) (.boolLit true)) (.declRef c)) (.declRef agg))⟩] }

/-- `h` never depended on `a`; under the fan-out encoding it does. -/
theorem fanout_false_dependency :
    ¬ DependsOn D₄.Δ h a ∧ InstDependsOn D₄'.Δ h agg ∧ InstDependsOn D₄'.Δ agg a := by decide

/-- The correct socket is a projection: `a` is in it because `f` needs it,
    and that says nothing about `h` (Theorem H). -/
theorem socket_is_projection :
    crossIn D₄ [a, c, f, h] [f, h] = [a, c] ∧ ¬ DependsOn D₄.Δ h a ∧ DependsOn D₄.Δ f a := by decide

end BDL.Experiments.Group
