import BDL.Core.Base

/-!
# Spec — design specifications and their refinement order

A specification is the *current commitment* attached to a design hole: an
expected type plus a finite set of atomic obligations.  Obligations are
abstract labels; what counts as evidence for them is supplied externally
(`Satisfaction.lean`).

Phase-0 result preserved here: `Refines` is a decidable preorder, frozen on
the type and monotone on obligations.
-/

namespace BDL

inductive PropertyId where
  | total
  | monotone
  | bounded
  deriving DecidableEq, Repr

structure Spec where
  expectedType : Ty
  obligations  : List PropertyId
  deriving DecidableEq, Repr

/-- `Refines old new`: `new` is a valid refinement of `old`. -/
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

/-- Mutual refinement.  Not antisymmetric on the list representation
    (`[total, total]` vs `[total]`); it identifies specs with the same type and
    the same *set* of obligations. -/
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

end BDL
