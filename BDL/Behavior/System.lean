import BDL.Behavior.Instantiate

/-!
# System — instances, bindings, and flattening

A `BehaviorSystem` is a finite list of instances (position = instance
index), a list of port bindings, and the system-level environments for
shared concepts and external sinks.  Hierarchy is obtained by *packaging*:
a flattened system is again an ordinary design over identities below a
bound, hence again a component template (`toComponent`).

`flatten` produces an ordinary `Design`:

1. the **disjoint union** of the instances, each renamed by `Ren.inst`;
2. each **binding** realizes the (unresolved) destination port with a
   reference to the source port — directly, or through `sync` from the
   source's domain — or with a closed constant (parameters).

Step 2 is a sequence of Phase-1 *realization* steps on the union design:
binding is refinement, not a new mechanism.
-/

namespace BDL
open BDL.Output (OutputId OutputSpec OutputEnv DriveEnv)
open BDL.Clock (ClockEnv)

/-! ## Bindings -/

/-- The source of a binding: a provided port of some instance, or a closed
    constant (an elaboration-time parameter value). -/
inductive BindSrc where
  | port (inst : Nat) (id : DeclId)
  | const (e : Expr)

structure Binding where
  src : BindSrc
  dstInst : Nat
  dst : DeclId
  /-- `none`: a direct reference (same domain or agnostic source).
      `some init`: transport through `sync` from the source's domain, with
      the explicit initial value `init`. -/
  transport : Option Expr

/-! ## Systems -/

structure BehaviorSystem where
  /-- Width: strictly above every global identity and every template width. -/
  W : Nat
  insts : List Inst
  bindings : List Binding
  /-- Representations of the shared (global) concepts. -/
  Θg : ConceptEnv
  /-- External physical sinks. -/
  Ωg : OutputEnv

namespace BehaviorSystem

def instAt (S : BehaviorSystem) (k : Nat) : Option Inst := S.insts[k]?

/-- The renaming of instance `k`. -/
def ren (S : BehaviorSystem) (k : Nat) (I : Inst) : Ren := Ren.inst I.comp S.W k I.κ

/-- The flattened identity of local declaration `d` of instance `k`. -/
def declOf (S : BehaviorSystem) (k : Nat) (d : DeclId) : DeclId := ⟨fresh S.W k d.n⟩

/-! ### The disjoint union of the instances -/

def unionΔ (S : BehaviorSystem) : DeclEnv := fun id =>
  match decode S.W id.n with
  | some (k, n) =>
    match S.instAt k with
    | some I => (I.comp.design.Δ ⟨n⟩).map (DesignDecl.rename (S.ren k I))
    | none => none
  | none => none

def unionΘ (S : BehaviorSystem) : ConceptEnv := fun s =>
  match decode S.W s.n with
  | some (k, n) =>
    match S.instAt k with
    | some I =>
      if I.comp.internalSem ⟨n⟩ then (I.comp.design.Θ ⟨n⟩).map (Ty.rename (S.ren k I).s) else none
    | none => none
  | none => S.Θg s

def unionΚ (S : BehaviorSystem) : ClockEnv := fun d =>
  match decode S.W d.n with
  | some (k, n) =>
    match S.instAt k with
    | some I => (I.comp.design.Κ ⟨n⟩).map (S.ren k I).c
    | none => none
  | none => none

def OutputSpec.rename (r : Ren) (spec : OutputSpec) : OutputSpec :=
  ⟨spec.accepts.rename r.s, r.c spec.clock⟩

def unionΩ (S : BehaviorSystem) : OutputEnv := fun o =>
  match decode S.W o.n with
  | some (k, n) =>
    match S.instAt k with
    | some I =>
      if I.comp.internalOut ⟨n⟩ then (I.comp.design.Ω ⟨n⟩).map (OutputSpec.rename (S.ren k I)) else none
    | none => none
  | none => S.Ωg o

def unionβ (S : BehaviorSystem) : DriveEnv := fun d =>
  match decode S.W d.n with
  | some (k, n) =>
    match S.instAt k with
    | some I => (I.comp.design.β ⟨n⟩).map (S.ren k I).o
    | none => none
  | none => none

/-! ### Applying bindings -/

/-- The term a binding realizes its destination with. -/
def bindingBody (S : BehaviorSystem) (b : Binding) : Expr :=
  match b.src with
  | .const e => e
  | .port k id =>
    let src := S.declOf k id
    match b.transport with
    | none => .declRef src
    | some init =>
      match S.unionΚ src with
      | some c => .sync c init (.declRef src)
      | none => .declRef src

/-- Realize the destination port of `b` in `Δ` (a Phase-1 `realize` step). -/
def applyBinding (S : BehaviorSystem) (Δ : DeclEnv) (b : Binding) : DeclEnv :=
  match Δ (S.declOf b.dstInst b.dst) with
  | some h => Δ.update ⟨h.id, h.interface, some (S.bindingBody b)⟩
  | none => Δ

def flattenΔ (S : BehaviorSystem) : DeclEnv :=
  S.bindings.foldl (applyBinding S) S.unionΔ

/-- **Flattening**: an ordinary BDL design. -/
def flatten (S : BehaviorSystem) : Design :=
  ⟨S.flattenΔ, S.unionΘ, S.unionΚ, S.unionΩ, S.unionβ⟩

/-! ## Structural well-formedness of a composition -/

/-- Type, commitment, and clock compatibility of one binding, stated on the
    two *interfaces* (never on names): the destination is a required port
    or a parameter of its instance; a port source is a provided port of its
    instance with the same (renamed) type, at least the destination's
    commitments, and a compatible clock — equal, agnostic, or bridged by an
    explicit `sync` with a closed, well-typed initial value; a constant
    source is closed, delay-free, and typed at the port's type. -/
def BindingWF (ev : Evidence) (S : BehaviorSystem) (b : Binding) : Prop :=
  ∃ Id, S.instAt b.dstInst = some Id ∧
  ∃ pd ∈ Id.comp.iface.required ++ Id.comp.iface.params, pd.id = b.dst ∧
  match b.src with
  | .const e =>
    b.transport = none ∧ e.RefFree ∧ e.DelayFree ∧
    HasType S.unionΘ .empty Grant.none [] e (pd.iface.expectedType.rename (S.ren b.dstInst Id).s) ∧
    ∀ p ∈ pd.iface.commitments, ∀ Δ, ev Δ e p
  | .port k id =>
    ∃ Is, S.instAt k = some Is ∧
    ∃ ps ∈ Is.comp.iface.provided, ps.id = id ∧
    ps.iface.expectedType.rename (S.ren k Is).s = pd.iface.expectedType.rename (S.ren b.dstInst Id).s ∧
    pd.iface.commitments ⊆ ps.iface.commitments ∧
    match b.transport with
    | none =>
      ps.clock.map (S.ren k Is).c = none ∨ ps.clock.map (S.ren k Is).c = pd.clock.map (S.ren b.dstInst Id).c
    | some init =>
      (∃ cd, pd.clock = some cd) ∧ (∃ cs, ps.clock = some cs) ∧ init.RefFree ∧ init.DelayFree ∧
      HasType S.unionΘ .empty Grant.none [] init (pd.iface.expectedType.rename (S.ren b.dstInst Id).s) ∧
      (pd.iface.expectedType.rename (S.ren b.dstInst Id).s).Data

/-- Every instance is a valid template that fits the system's width, and
    its view of the shared concepts and external sinks agrees with the
    system's. -/
def InstsWF (ev : Evidence) (S : BehaviorSystem) : Prop :=
  ∀ k I, S.instAt k = some I →
    I.comp.Realizes ev ∧ I.comp.width ≤ S.W ∧
    (∀ c, I.comp.internalClock c = false → (I.κ c).n < S.W) ∧
    (∀ s R, I.comp.design.Θ s = some R → I.comp.internalSem s = false → s.n < S.W ∧ S.Θg s = some R) ∧
    (∀ o spec, I.comp.design.Ω o = some spec → I.comp.internalOut o = false →
      o.n < S.W ∧ S.Ωg o = some (OutputSpec.rename (S.ren k I) spec))

/-- At most one instance drives each external sink. -/
def ExternalSingleDriver (S : BehaviorSystem) : Prop :=
  ∀ k₁ I₁ d₁ k₂ I₂ d₂ o, S.instAt k₁ = some I₁ → S.instAt k₂ = some I₂ →
    I₁.comp.design.β d₁ = some o → I₁.comp.internalOut o = false →
    I₂.comp.design.β d₂ = some o → I₂.comp.internalOut o = false →
    k₁ = k₂ ∧ d₁ = d₂

/-- **Composition judgment** (`ComposeWF S`).  Open systems are allowed: a
    required port with no binding stays unresolved. -/
structure ComposeWF (ev : Evidence) (S : BehaviorSystem) : Prop where
  width : 0 < S.W
  insts : InstsWF ev S
  globalsWF : S.Θg.WF
  globalsBound : ∀ s R, S.Θg s = some R → s.n < S.W
  bindings : ∀ b ∈ S.bindings, BindingWF ev S b
  /-- Each destination port is bound at most once. -/
  dstNodup : (S.bindings.map fun b => S.declOf b.dstInst b.dst).Nodup
  external : ExternalSingleDriver S

/-! ## Open and closed systems -/

/-- The flattened identities of the required ports that no binding targets. -/
def OpenPorts (S : BehaviorSystem) (d : DeclId) : Prop :=
  (∃ k I p, S.instAt k = some I ∧ p ∈ I.comp.iface.required ++ I.comp.iface.params ∧ d = S.declOf k p.id) ∧
  ∀ b ∈ S.bindings, S.declOf b.dstInst b.dst ≠ d

/-- The inter-instance instantaneous dependency graph: `i → j` when some
    *direct* port binding takes a port of `i` from a port of `j`.  (A
    binding through `sync` is never instantaneous.)  Self-edges count:
    binding an instance's own provided port back into one of its required
    ports is treated conservatively as a cycle. -/
def InstDep (S : BehaviorSystem) (i j : Nat) : Prop :=
  ∃ b ∈ S.bindings, b.dstInst = i ∧ b.transport = none ∧ ∃ id, b.src = .port j id

/-- Acyclicity of the inter-instance graph, witnessed by a bounded rank,
    in the same style as `Causal`. -/
def InstAcyclic (S : BehaviorSystem) : Prop :=
  ∃ (irank : Nat → Nat) (R : Nat), (∀ k, irank k < R) ∧ ∀ i j, InstDep S i j → irank j < irank i

/-! ## Hierarchy: a flattened system is a component -/

/-- A bound above every identity of the flattened system: instance `k < N`
    uses identities `< W * (N + 1)`. -/
def flatWidth (S : BehaviorSystem) : Nat := S.W * (S.insts.length + 1)

/-- Package a flattened system as a component whose ports are chosen among
    the flattened identities.  Internal concepts and sinks of the package
    are those of its instances (fresh, `≥ W`); the shared ones stay shared. -/
def toComponent (S : BehaviorSystem) (iface : BehaviorInterface) : BehaviorComponent :=
  { iface := iface
    design := S.flatten
    width := S.flatWidth
    internalSem := fun s => decide (S.W ≤ s.n)
    internalOut := fun o => decide (S.W ≤ o.n) }

end BehaviorSystem

end BDL
