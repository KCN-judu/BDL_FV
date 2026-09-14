import BDL.Core.Base

/-!
# Interface — declaration interfaces and their refinement order

`DeclInterface` is the *public contract* of a design declaration: the part
clients may depend on.  It consists of

* `expectedType` — what typing sees (and the only thing typing sees;
  `Typing.lean`);
* `commitments`  — public promises dependents may rely on, as atomic labels.

Commitments vs obligations.  From the client's side these are commitments
(promises the declaration makes).  From the validation layer's side each
commitment gives rise to a proof *obligation* to be discharged by evidence
(`Satisfaction.lean`).  Phase 1 represents both by the same `PropertyId`;
no separate obligation datatype exists yet.

Phase-0 result preserved here: `InterfaceRefines` is a decidable preorder,
frozen on the type and monotone on commitments.  Refinement is the only
interface change the kernel treats as safe for dependents; anything else
(changing the type, dropping a commitment) is an *edit* — see
`DESIGN_DECISIONS.md` D-16.
-/

namespace BDL

inductive PropertyId where
  | total
  | monotone
  | bounded
  deriving DecidableEq, Repr

structure DeclInterface where
  expectedType : Ty
  commitments  : List PropertyId
  deriving DecidableEq, Repr

/-- `InterfaceRefines old new`: `new` is a monotone refinement of `old` —
    same expected type, every old commitment still present. -/
def InterfaceRefines (old new : DeclInterface) : Prop :=
  old.expectedType = new.expectedType ∧ old.commitments ⊆ new.commitments

instance : DecidableRel InterfaceRefines := fun old new =>
  inferInstanceAs (Decidable (old.expectedType = new.expectedType ∧ _ ⊆ _))

theorem InterfaceRefines.refl (S : DeclInterface) : InterfaceRefines S S :=
  ⟨rfl, List.Subset.refl _⟩

theorem InterfaceRefines.trans {S₀ S₁ S₂ : DeclInterface}
    (h₀₁ : InterfaceRefines S₀ S₁) (h₁₂ : InterfaceRefines S₁ S₂) : InterfaceRefines S₀ S₂ :=
  ⟨h₀₁.1.trans h₁₂.1, List.Subset.trans h₀₁.2 h₁₂.2⟩

theorem InterfaceRefines.expectedType_eq {S₀ S₁ : DeclInterface} (h : InterfaceRefines S₀ S₁) :
    S₀.expectedType = S₁.expectedType := h.1

theorem InterfaceRefines.commitments_subset {S₀ S₁ : DeclInterface} (h : InterfaceRefines S₀ S₁) :
    S₀.commitments ⊆ S₁.commitments := h.2

/-- The canonical single refinement step: make one more public commitment. -/
def DeclInterface.addCommitment (S : DeclInterface) (p : PropertyId) : DeclInterface :=
  { S with commitments := p :: S.commitments }

theorem InterfaceRefines_addCommitment (S : DeclInterface) (p : PropertyId) :
    InterfaceRefines S (S.addCommitment p) :=
  ⟨rfl, List.subset_cons_self p S.commitments⟩

/-- Mutual refinement.  Not antisymmetric on the list representation
    (`[total, total]` vs `[total]`); it identifies interfaces with the same
    type and the same *set* of commitments. -/
def InterfaceEquiv (S₁ S₂ : DeclInterface) : Prop :=
  InterfaceRefines S₁ S₂ ∧ InterfaceRefines S₂ S₁

instance : DecidableRel InterfaceEquiv := fun S₁ S₂ =>
  inferInstanceAs (Decidable (InterfaceRefines S₁ S₂ ∧ InterfaceRefines S₂ S₁))

theorem InterfaceEquiv_iff {S₁ S₂ : DeclInterface} :
    InterfaceEquiv S₁ S₂ ↔
      S₁.expectedType = S₂.expectedType ∧
      ∀ p, p ∈ S₁.commitments ↔ p ∈ S₂.commitments := by
  constructor
  · rintro ⟨⟨ht, h₁₂⟩, ⟨_, h₂₁⟩⟩
    exact ⟨ht, fun p => ⟨fun hp => h₁₂ hp, fun hp => h₂₁ hp⟩⟩
  · rintro ⟨ht, hp⟩
    exact ⟨⟨ht, fun _ h => (hp _).1 h⟩, ⟨ht.symm, fun _ h => (hp _).2 h⟩⟩

end BDL
