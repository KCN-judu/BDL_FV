import PersistentHole.Syntax

/-!
# Spec — design specifications, refinement, and realization satisfaction

A specification is the *current commitment* attached to a design hole:
an expected type plus a finite set of abstract obligations.

Obligations are atomic and abstract on purpose: this experiment is about
the *structure of refinement*, not about deciding semantic properties.
Evidence that a term meets an obligation is an arbitrary relation
`Evidence : Expr → PropertyId → Prop` that every theorem quantifies over.
-/

namespace PersistentHole

/-- Atomic, decidable obligation identifiers.  Their meaning is supplied
    externally through an `Evidence` relation. -/
inductive PropertyId where
  | total
  | monotone
  | bounded
  deriving DecidableEq, Repr

/-- The commitment currently attached to a hole. -/
structure Spec where
  expectedType : Ty
  obligations  : List PropertyId
  deriving DecidableEq, Repr

/-! ## Refinement -/

/-- `Refines old new`: `new` is a valid refinement of `old`.

The expected type is frozen and obligations may only be *added*.
This is deliberately not "logical implication": it is a purely syntactic,
decidable relation.  `Refines_iff_semantic` below shows that it nevertheless
coincides with the semantic notion "every realization of `new` also realizes
`old`" once evidence is treated abstractly. -/
def Refines (old new : Spec) : Prop :=
  old.expectedType = new.expectedType ∧ old.obligations ⊆ new.obligations

instance : DecidableRel Refines := fun old new =>
  inferInstanceAs (Decidable (old.expectedType = new.expectedType ∧ _ ⊆ _))

theorem Refines.refl (S : Spec) : Refines S S :=
  ⟨rfl, List.Subset.refl _⟩

theorem Refines.trans {S₀ S₁ S₂ : Spec}
    (h₀₁ : Refines S₀ S₁) (h₁₂ : Refines S₁ S₂) : Refines S₀ S₂ :=
  ⟨h₀₁.1.trans h₁₂.1, List.Subset.trans h₀₁.2 h₁₂.2⟩

theorem Refines.expectedType_eq {S₀ S₁ : Spec} (h : Refines S₀ S₁) :
    S₀.expectedType = S₁.expectedType := h.1

theorem Refines.obligations_subset {S₀ S₁ : Spec} (h : Refines S₀ S₁) :
    S₀.obligations ⊆ S₁.obligations := h.2

/-- The canonical single refinement step: commit to one more obligation. -/
def Spec.addObligation (S : Spec) (p : PropertyId) : Spec :=
  { S with obligations := p :: S.obligations }

theorem Refines_addObligation (S : Spec) (p : PropertyId) :
    Refines S (S.addObligation p) :=
  ⟨rfl, List.subset_cons_self p S.obligations⟩

/-- Mutual refinement.  Because obligations are a list, this is *not*
    antisymmetric (see `Examples.specEquiv_not_antisymm`); it identifies
    specs with the same type and the same *set* of obligations. -/
def SpecEquiv (S₁ S₂ : Spec) : Prop :=
  Refines S₁ S₂ ∧ Refines S₂ S₁

instance : DecidableRel SpecEquiv := fun S₁ S₂ =>
  inferInstanceAs (Decidable (Refines S₁ S₂ ∧ Refines S₂ S₁))

theorem SpecEquiv_iff {S₁ S₂ : Spec} :
    SpecEquiv S₁ S₂ ↔
      S₁.expectedType = S₂.expectedType ∧
      ∀ p, p ∈ S₁.obligations ↔ p ∈ S₂.obligations := by
  constructor
  · rintro ⟨⟨ht, h₁₂⟩, ⟨_, h₂₁⟩⟩
    exact ⟨ht, fun p => ⟨fun hp => h₁₂ hp, fun hp => h₂₁ hp⟩⟩
  · rintro ⟨ht, hp⟩
    exact ⟨⟨ht, fun _ h => (hp _).1 h⟩, ⟨ht.symm, fun _ h => (hp _).2 h⟩⟩

/-! ## Realization satisfaction -/

/-- Abstract evidence: which terms are known to discharge which obligations.
    No solver is modelled; every result quantifies over an arbitrary `ev`. -/
abbrev Evidence := Expr → PropertyId → Prop

/-- `e` is a valid realization of `S` in context `Γ`. -/
def Satisfies (ev : Evidence) (Γ : Ctx) (e : Expr) (S : Spec) : Prop :=
  HasType Γ e S.expectedType ∧ ∀ p ∈ S.obligations, ev e p

instance (ev : Evidence) [∀ e p, Decidable (ev e p)] (Γ : Ctx) (e : Expr) (S : Spec) :
    Decidable (Satisfies ev Γ e S) :=
  inferInstanceAs (Decidable (HasType Γ e S.expectedType ∧ ∀ p ∈ S.obligations, ev e p))

/-- **Theorem 5 (two-step form).**  A realization of a refined spec is a
    realization of the original spec: adding commitments can only shrink the
    set of admissible realizations, never invalidate earlier commitments. -/
theorem Satisfies.of_refines {ev : Evidence} {Γ : Ctx} {e : Expr} {S₀ S₁ : Spec}
    (h : Refines S₀ S₁) (hs : Satisfies ev Γ e S₁) : Satisfies ev Γ e S₀ :=
  ⟨h.expectedType_eq ▸ hs.1, fun p hp => hs.2 p (h.obligations_subset hp)⟩

/-- **Completeness of `Refines`.**  With evidence abstract, the syntactic
    refinement relation is *exactly* the semantic one: `S₁` refines `S₀` iff
    every realization of `S₁` (under every evidence relation and context) is a
    realization of `S₀`.  So nothing is lost by choosing the small decidable
    relation over "arbitrary logical implication". -/
theorem Refines_iff_semantic (S₀ S₁ : Spec) :
    Refines S₀ S₁ ↔
      ∀ (ev : Evidence) (Γ : Ctx) (e : Expr), Satisfies ev Γ e S₁ → Satisfies ev Γ e S₀ := by
  constructor
  · intro h ev Γ e hs
    exact hs.of_refines h
  · intro h
    constructor
    · -- types: realize `S₁` by its canonical inhabitant under trivial evidence
      have hs := h (fun _ _ => True) [] S₁.expectedType.canon
        ⟨S₁.expectedType.canon_hasType [], fun _ _ => trivial⟩
      exact hs.1.unique (S₁.expectedType.canon_hasType [])
    · -- obligations: use evidence that discharges exactly `S₁`'s obligations
      intro p hp
      have hs := h (fun _ q => q ∈ S₁.obligations) [] S₁.expectedType.canon
        ⟨S₁.expectedType.canon_hasType [], fun _ hq => hq⟩
      exact hs.2 p hp

end PersistentHole
