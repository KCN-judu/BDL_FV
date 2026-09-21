import BDL.Core.Interface

/-!
# Decl — design declarations, environments, and the structural lifecycle order

The kernel object is a **declaration with an optional realization**:

    DesignDecl = stable identity + public interface + optional realization

`realization = none` means the declaration exists and clients may refer to
its interface, but no body has been supplied yet.  It is *not* a syntactic
hole position; "hole" survives only as a surface metaphor (FVD-0015).  The
designer-facing reading of the realization state is production's derived role
— Source, Rule, Value (ADR-0032) — never a kernel kind.

* `DeclEnv` — the global map from ids to declarations that references are
  resolved against, and its *type view* `tyView`, which is all that typing
  is allowed to see.
* `DeclLeq` / `EnvRefines` — the purely **structural** monotone-refinement
  order (id frozen, interface refines, realization write-once), with *no*
  satisfaction condition.  Satisfaction is a separate global invariant
  (`GlobalWF` in `Env.lean`).  Separating the order from the invariant is
  what lets the typing-preservation theorem be stated under the weakest
  hypotheses.

Refinement vs edit.  `DeclLeq` is deliberately *not* an edit relation.
Changing the expected type, dropping a commitment, detaching or replacing a
realization, or changing the id are ordinary edits: they may invalidate
transitive dependents and require rechecking.  No general edit relation is
formalized; the counterexamples in `Experiments/` show what each edit breaks.
-/

namespace BDL

structure DesignDecl where
  id          : DeclId
  interface   : DeclInterface
  realization : Option Expr
  deriving DecidableEq, Repr

def DesignDecl.unresolved (id : DeclId) (S : DeclInterface) : DesignDecl := ⟨id, S, none⟩

/-! ## Environments -/

/-- Partial map from ids to declarations. -/
abbrev DeclEnv := DeclId → Option DesignDecl

def DeclEnv.empty : DeclEnv := fun _ => none

/-- Store (the new state of) declaration `h` under its own id. -/
def DeclEnv.update (Δ : DeclEnv) (h : DesignDecl) : DeclEnv :=
  fun id => if id = h.id then some h else Δ id

theorem DeclEnv.update_self (Δ : DeclEnv) (h : DesignDecl) :
    Δ.update h h.id = some h := by
  simp [DeclEnv.update]

theorem DeclEnv.update_other (Δ : DeclEnv) (h : DesignDecl) {id : DeclId}
    (hne : id ≠ h.id) : Δ.update h id = Δ id := by
  simp [DeclEnv.update, hne]

/-- Finite environments, for decidable examples.  First match wins. -/
def DeclEnv.ofList (l : List DesignDecl) : DeclEnv :=
  fun id => l.find? (·.id = id)

theorem DeclEnv.ofList_some {l : List DesignDecl} {id : DeclId} {h : DesignDecl}
    (hh : DeclEnv.ofList l id = some h) : h ∈ l ∧ h.id = id := by
  unfold DeclEnv.ofList at hh
  exact ⟨List.mem_of_find?_eq_some hh, by simpa using List.find?_some hh⟩

/-- **The type view.**  Typing may consult the environment only through this
    projection: the expected type of each declaration.  Commitments,
    realizations, and evidence are invisible to typing by construction. -/
def DeclEnv.tyView (Δ : DeclEnv) (h : DeclId) : Option Ty :=
  (Δ h).map (·.interface.expectedType)

/-- The realization of a declaration, if it is declared and realized. -/
def DeclEnv.realizationOf (Δ : DeclEnv) (h : DeclId) : Option Expr :=
  (Δ h).bind (·.realization)

/-! ## Concept environment (Phase 3)

Representation binding is a *witness* `Θ s = some R`: concept `s` is
represented by `R`.  It is a second, concept-level environment, separate
from `DeclEnv` (a concept is a type, a declaration is a value — Phase 2,
Model C).  Like a realization it is write-once (`ConceptRefines`). -/

abbrev ConceptEnv := ConceptId → Option Ty

def ConceptEnv.empty : ConceptEnv := fun _ => none

/-- Representation types must not be semantic — binding `Tilt ↦ MotorAngle`
    would make `rep` a hidden mapping
    (`Experiments.RepBinding.binding_to_semantic_type_is_hidden_mapping`) —
    and must be *data* (Phase 4): a Sem value may be delayed, and a
    function-typed representation would carry a closure across ticks. -/
def ConceptEnv.WF (Θ : ConceptEnv) : Prop :=
  ∀ s R, Θ s = some R → R.SemFree ∧ R.Data

/-- Binding more concepts (never rebinding) is a refinement. -/
def ConceptRefines (Θ₁ Θ₂ : ConceptEnv) : Prop :=
  ∀ s R, Θ₁ s = some R → Θ₂ s = some R

theorem ConceptRefines.refl (Θ : ConceptEnv) : ConceptRefines Θ Θ := fun _ _ h => h
theorem ConceptRefines.trans {Θ₀ Θ₁ Θ₂ : ConceptEnv}
    (a : ConceptRefines Θ₀ Θ₁) (b : ConceptRefines Θ₁ Θ₂) : ConceptRefines Θ₀ Θ₂ :=
  fun s R h => b s R (a s R h)

/-- Bind a representation to an (unbound) concept. -/
def ConceptEnv.bind (Θ : ConceptEnv) (s : ConceptId) (R : Ty) : ConceptEnv :=
  fun s' => if s' = s then some R else Θ s'

theorem ConceptRefines.bind {Θ : ConceptEnv} {s : ConceptId} (R : Ty) (h : Θ s = none) :
    ConceptRefines Θ (Θ.bind s R) := by
  intro s' R' h'
  unfold ConceptEnv.bind
  split
  · rename_i heq; subst heq; rw [h] at h'; exact nomatch h'
  · exact h'

/-! ## Construction grants (Phase 3)

`mk s` may be used only where the grant permits `s`.  A declaration's
realization is granted exactly the concepts in result position of its own
signature: the signature is the authority for crossing concept identities. -/

abbrev Grant := ConceptId → Prop

def Grant.none : Grant := fun _ => False
def Grant.all  : Grant := fun _ => True

instance : DecidablePred Grant.none := fun _ => inferInstanceAs (Decidable False)
instance : DecidablePred Grant.all  := fun _ => inferInstanceAs (Decidable True)

/-- Concepts in result position of a signature. -/
def Ty.grant : Ty → List ConceptId
  | .sem s => [s]
  | .arr _ b => b.grant
  | _ => []

/-- The grant a declaration of type `τ` receives for its realization. -/
def Grant.of (τ : Ty) : Grant := fun s => s ∈ τ.grant

instance (τ : Ty) : DecidablePred (Grant.of τ) := fun s => inferInstanceAs (Decidable (s ∈ τ.grant))

/-! ## Structural lifecycle order -/

/-- `DeclLeq h₁ h₂`: `h₂` is a later state of the *same* declaration under
    monotone refinement. -/
def DeclLeq (h₁ h₂ : DesignDecl) : Prop :=
  h₁.id = h₂.id ∧
  InterfaceRefines h₁.interface h₂.interface ∧
  ∀ e, h₁.realization = some e → h₂.realization = some e

instance (h₁ h₂ : DesignDecl) : Decidable (DeclLeq h₁ h₂) := by
  unfold DeclLeq
  have : Decidable (∀ e, h₁.realization = some e → h₂.realization = some e) := by
    cases h₁.realization with
    | none => exact isTrue fun _ h => nomatch h
    | some e =>
      if h : h₂.realization = some e then
        exact isTrue fun _ h' => Option.some.inj h' ▸ h
      else
        exact isFalse fun f => h (f e rfl)
  exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem DeclLeq.refl (h : DesignDecl) : DeclLeq h h :=
  ⟨rfl, InterfaceRefines.refl _, fun _ he => he⟩

theorem DeclLeq.trans {h₀ h₁ h₂ : DesignDecl} (a : DeclLeq h₀ h₁) (b : DeclLeq h₁ h₂) :
    DeclLeq h₀ h₂ :=
  ⟨a.1.trans b.1, a.2.1.trans b.2.1, fun e he => b.2.2 e (a.2.2 e he)⟩

theorem DeclLeq.id_eq {h₁ h₂ : DesignDecl} (h : DeclLeq h₁ h₂) : h₁.id = h₂.id := h.1
theorem DeclLeq.interface_refines {h₁ h₂ : DesignDecl} (h : DeclLeq h₁ h₂) : InterfaceRefines h₁.interface h₂.interface := h.2.1
theorem DeclLeq.expectedType_eq {h₁ h₂ : DesignDecl} (h : DeclLeq h₁ h₂) :
    h₁.interface.expectedType = h₂.interface.expectedType := h.2.1.1

/-- `EnvRefines Δ₁ Δ₂`: every declaration in `Δ₁` is in `Δ₂`, under the same
    id, in a later state.  New declarations may appear. -/
def EnvRefines (Δ₁ Δ₂ : DeclEnv) : Prop :=
  ∀ id h₁, Δ₁ id = some h₁ → ∃ h₂, Δ₂ id = some h₂ ∧ DeclLeq h₁ h₂

theorem EnvRefines.refl (Δ : DeclEnv) : EnvRefines Δ Δ :=
  fun _ h₁ h => ⟨h₁, h, DeclLeq.refl _⟩

theorem EnvRefines.trans {Δ₀ Δ₁ Δ₂ : DeclEnv}
    (a : EnvRefines Δ₀ Δ₁) (b : EnvRefines Δ₁ Δ₂) : EnvRefines Δ₀ Δ₂ := by
  intro id h₀ h
  obtain ⟨h₁, h₁eq, r₁⟩ := a id h₀ h
  obtain ⟨h₂, h₂eq, r₂⟩ := b id h₁ h₁eq
  exact ⟨h₂, h₂eq, r₁.trans r₂⟩

/-- Environment refinement never changes the type view of a declaration. -/
theorem EnvRefines.tyView {Δ₁ Δ₂ : DeclEnv} (er : EnvRefines Δ₁ Δ₂) {h : DeclId} {τ : Ty}
    (ht : Δ₁.tyView h = some τ) : Δ₂.tyView h = some τ := by
  unfold DeclEnv.tyView at *
  cases hh : Δ₁ h with
  | none => simp [hh] at ht
  | some dh =>
    obtain ⟨dh₂, hh₂, le⟩ := er h dh hh
    simp [hh] at ht
    simp [hh₂, ← le.expectedType_eq, ht]

/-- Realizations, once present, survive environment refinement. -/
theorem EnvRefines.realizationOf {Δ₁ Δ₂ : DeclEnv} (er : EnvRefines Δ₁ Δ₂) {h : DeclId} {e : Expr}
    (he : Δ₁.realizationOf h = some e) : Δ₂.realizationOf h = some e := by
  unfold DeclEnv.realizationOf at *
  cases hh : Δ₁ h with
  | none => simp [hh] at he
  | some dh =>
    obtain ⟨dh₂, hh₂, le⟩ := er h dh hh
    simp [hh] at he
    simp [hh₂, le.2.2 e he]

/-- **Where identity does its work.**  Stepping the declaration stored at
    `h₁.id` to `h₂` and writing it back is an environment refinement *because*
    `h₂.id = h₁.id` puts the write on the slot every reference resolves to —
    exactly what a declaration name does in any environment semantics. -/
theorem EnvRefines_update {Δ : DeclEnv} {h₁ h₂ : DesignDecl}
    (hstored : Δ h₁.id = some h₁) (le : DeclLeq h₁ h₂) :
    EnvRefines Δ (Δ.update h₂) := by
  intro id h hh
  by_cases dId : id = h₂.id
  · subst dId
    have : h = h₁ := by
      rw [← le.id_eq] at hh
      exact Option.some.inj (hh.symm.trans hstored)
    subst this
    exact ⟨h₂, Δ.update_self h₂, le⟩
  · exact ⟨h, (Δ.update_other h₂ dId).trans hh, DeclLeq.refl _⟩

end BDL
