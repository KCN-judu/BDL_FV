import PersistentHole.Hole

/-!
# Refinement — the lifecycle of a persistent design hole

`HoleRefines ev Γ h₁ h₂` is a single lifecycle step.  Three things happen to
a hole over its life, and nothing else:

* `refine`     — an unresolved hole's spec is refined (`Refines S S'`);
* `realize`    — an unresolved hole receives a term satisfying its spec;
* `strengthen` — a realized hole's spec is refined *and the existing term is
                 re-verified against the new spec*.

Identity preservation is not a side condition: every constructor produces a
hole with the *same* `id` it consumed, so Theorem 1 is definitional.

The re-verification premise on `strengthen` is the invariant the Lean
experiment was run to discover (see `Examples.naive_breaks_wellformedness`):
without it, well-formedness is not preserved.
-/

namespace PersistentHole

inductive HoleRefines (ev : Evidence) (Γ : Ctx) : DesignHole → DesignHole → Prop where
  | refine {id : HoleId} {S S' : Spec}
      (h : Refines S S') :
      HoleRefines ev Γ ⟨id, S, none⟩ ⟨id, S', none⟩
  | realize {id : HoleId} {S : Spec} {e : Expr}
      (hs : Satisfies ev Γ e S) :
      HoleRefines ev Γ ⟨id, S, none⟩ ⟨id, S, some e⟩
  | strengthen {id : HoleId} {S S' : Spec} {e : Expr}
      (h : Refines S S') (hs : Satisfies ev Γ e S') :
      HoleRefines ev Γ ⟨id, S, some e⟩ ⟨id, S', some e⟩

section SingleStep
variable {ev : Evidence} {Γ : Ctx} {h₁ h₂ : DesignHole}

/-- **Theorem 1 — identity preservation.** -/
theorem HoleRefines.id_eq (h : HoleRefines ev Γ h₁ h₂) : h₁.id = h₂.id := by
  cases h <;> rfl

/-- Every step refines the specification. -/
theorem HoleRefines.spec_refines (h : HoleRefines ev Γ h₁ h₂) :
    Refines h₁.spec h₂.spec := by
  cases h with
  | refine h => exact h
  | realize _ => exact Refines.refl _
  | strengthen h _ => exact h

/-- **Theorem 2 — type commitment preservation.** -/
theorem HoleRefines.expectedType_eq (h : HoleRefines ev Γ h₁ h₂) :
    h₁.spec.expectedType = h₂.spec.expectedType :=
  h.spec_refines.expectedType_eq

/-- **Theorem 3 — obligation monotonicity** ("commitments are not forgotten"). -/
theorem HoleRefines.obligations_subset (h : HoleRefines ev Γ h₁ h₂) :
    h₁.spec.obligations ⊆ h₂.spec.obligations :=
  h.spec_refines.obligations_subset

/-- A realization, once supplied, is never removed or replaced. -/
theorem HoleRefines.realization_mono (h : HoleRefines ev Γ h₁ h₂) :
    ∀ e, h₁.realization = some e → h₂.realization = some e := by
  cases h with
  | refine _ => intro _ h; exact nomatch h
  | realize _ => intro _ h; exact nomatch h
  | strengthen _ _ => intro _ h; exact h

/-- **Theorem 4 — refinement preserves well-formedness.**

Note that the proof for `strengthen` uses its re-verification premise `hs`
and *nothing* about `h₁`; for `realize` likewise.  Only `refine` needs the
hypothesis `wf`, and there it is vacuous.  In other words, well-formedness of
the target is a consequence of the step's own premises — which is exactly why
the step must carry them (see `Examples.naive_breaks_wellformedness`). -/
theorem HoleRefines.preserves_wellFormed
    (wf : WellFormedHole ev Γ h₁) (h : HoleRefines ev Γ h₁ h₂) :
    WellFormedHole ev Γ h₂ := by
  cases h with
  | refine _ => exact WellFormedHole.unresolved ev Γ _ _
  | realize hs => exact WellFormedHole.realized hs
  | strengthen _ hs => exact WellFormedHole.realized hs

end SingleStep

/-! ## Reflexive–transitive closure -/

/-- Reflexive–transitive closure of a relation. -/
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl (a : α) : Star R a a
  | step {a b c : α} : R a b → Star R b c → Star R a c

namespace Star
variable {α : Type} {R : α → α → Prop}

theorem single {a b : α} (h : R a b) : Star R a b := .step h (.refl b)

theorem trans {a b c : α} (h₁ : Star R a b) (h₂ : Star R b c) : Star R a c := by
  induction h₁ with
  | refl _ => exact h₂
  | step hab _ ih => exact .step hab (ih h₂)

/-- Any reflexive-transitive relation absorbs its own closure. -/
theorem elim {S : α → α → Prop} (hrefl : ∀ a, S a a)
    (htrans : ∀ {a b c}, S a b → S b c → S a c) (hsub : ∀ {a b}, R a b → S a b)
    {a b : α} (h : Star R a b) : S a b := by
  induction h with
  | refl a => exact hrefl a
  | step hab _ ih => exact htrans (hsub hab) ih

end Star

/-- Multi-step specification refinement collapses to a single `Refines`. -/
theorem Refines.of_star {S₀ Sₙ : Spec} (h : Star Refines S₀ Sₙ) : Refines S₀ Sₙ :=
  h.elim Refines.refl Refines.trans id

/-- **Theorem 5 (n-step form).**  A realization of the last spec in a chain
    `S₀ ↝ S₁ ↝ ⋯ ↝ Sₙ` realizes every earlier spec. -/
theorem Satisfies.of_refines_star {ev : Evidence} {Γ : Ctx} {e : Expr} {S₀ Sₙ : Spec}
    (h : Star Refines S₀ Sₙ) (hs : Satisfies ev Γ e Sₙ) : Satisfies ev Γ e S₀ :=
  hs.of_refines (Refines.of_star h)

/-- **Theorem 6.**  Multi-step hole refinement. `HoleRefines` itself is not
    transitive (`refine` followed by `realize` has no single-step equivalent
    because `realize` keeps the spec fixed), so we take the closure. -/
abbrev HoleRefinesStar (ev : Evidence) (Γ : Ctx) : DesignHole → DesignHole → Prop :=
  Star (HoleRefines ev Γ)

section MultiStep
variable {ev : Evidence} {Γ : Ctx} {h₀ h₁ h₂ : DesignHole}

theorem HoleRefinesStar.of_two
    (a : HoleRefines ev Γ h₀ h₁) (b : HoleRefines ev Γ h₁ h₂) :
    HoleRefinesStar ev Γ h₀ h₂ :=
  .step a (.single b)

/-- Theorems 1–4 lift to the closure. -/
theorem HoleRefinesStar.id_eq (h : HoleRefinesStar ev Γ h₀ h₂) : h₀.id = h₂.id :=
  h.elim (S := fun a b => a.id = b.id) (fun _ => rfl) Eq.trans HoleRefines.id_eq

theorem HoleRefinesStar.spec_refines (h : HoleRefinesStar ev Γ h₀ h₂) :
    Refines h₀.spec h₂.spec :=
  h.elim (S := fun a b => Refines a.spec b.spec)
    (fun _ => Refines.refl _) Refines.trans HoleRefines.spec_refines

theorem HoleRefinesStar.expectedType_eq (h : HoleRefinesStar ev Γ h₀ h₂) :
    h₀.spec.expectedType = h₂.spec.expectedType :=
  h.spec_refines.expectedType_eq

theorem HoleRefinesStar.obligations_subset (h : HoleRefinesStar ev Γ h₀ h₂) :
    h₀.spec.obligations ⊆ h₂.spec.obligations :=
  h.spec_refines.obligations_subset

theorem HoleRefinesStar.realization_mono (h : HoleRefinesStar ev Γ h₀ h₂) :
    ∀ e, h₀.realization = some e → h₂.realization = some e := by
  induction h with
  | refl _ => exact fun _ he => he
  | step hab _ ih => exact fun e he => ih e (hab.realization_mono e he)

theorem HoleRefinesStar.preserves_wellFormed
    (wf : WellFormedHole ev Γ h₀) (h : HoleRefinesStar ev Γ h₀ h₂) :
    WellFormedHole ev Γ h₂ := by
  induction h with
  | refl _ => exact wf
  | step hab _ ih => exact ih (hab.preserves_wellFormed wf)

/-- **Theorem 5 at the hole level.**  Whatever term a hole is eventually
    realized by satisfies the specification it had at *every* earlier point
    in its life — in particular the original `S₀`. -/
theorem HoleRefinesStar.final_realization_satisfies_all
    (wf : WellFormedHole ev Γ h₀) (h : HoleRefinesStar ev Γ h₀ h₂)
    {e : Expr} (he : h₂.realization = some e) :
    Satisfies ev Γ e h₀.spec :=
  (h.preserves_wellFormed wf e he).of_refines h.spec_refines

end MultiStep

/-! ## Closed-form characterization of the closure

`HoleRefinesStar` is exactly the following preorder.  This is the most
informative structural fact about the model: the whole lifecycle *is* the
product of (fixed id) × (Spec preorder) × (write-once realization), subject
to the invariant that a present realization satisfies the current spec. -/

def HoleLeq (ev : Evidence) (Γ : Ctx) (h₁ h₂ : DesignHole) : Prop :=
  h₁.id = h₂.id ∧
  Refines h₁.spec h₂.spec ∧
  (∀ e, h₁.realization = some e → h₂.realization = some e) ∧
  (∀ e, h₂.realization = some e → Satisfies ev Γ e h₂.spec)

instance (ev : Evidence) [∀ e p, Decidable (ev e p)] (Γ : Ctx) (h₁ h₂ : DesignHole) :
    Decidable (HoleLeq ev Γ h₁ h₂) := by
  unfold HoleLeq
  have : Decidable (∀ e, h₁.realization = some e → h₂.realization = some e) := by
    cases h₁.realization with
    | none => exact isTrue fun _ h => nomatch h
    | some e =>
      if h : h₂.realization = some e then
        exact isTrue fun _ h' => Option.some.inj h' ▸ h
      else
        exact isFalse fun f => h (f e rfl)
  exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ WellFormedHole ev Γ h₂))

theorem HoleLeq.refl (ev : Evidence) (Γ : Ctx) {h : DesignHole}
    (wf : WellFormedHole ev Γ h) : HoleLeq ev Γ h h :=
  ⟨rfl, Refines.refl _, fun _ he => he, wf⟩

theorem HoleLeq.trans {ev : Evidence} {Γ : Ctx} {h₀ h₁ h₂ : DesignHole}
    (a : HoleLeq ev Γ h₀ h₁) (b : HoleLeq ev Γ h₁ h₂) : HoleLeq ev Γ h₀ h₂ :=
  ⟨a.1.trans b.1, a.2.1.trans b.2.1, fun e he => b.2.2.1 e (a.2.2.1 e he), b.2.2.2⟩

theorem HoleRefinesStar.toLeq {ev : Evidence} {Γ : Ctx} {h₁ h₂ : DesignHole}
    (wf : WellFormedHole ev Γ h₁) (h : HoleRefinesStar ev Γ h₁ h₂) : HoleLeq ev Γ h₁ h₂ :=
  ⟨h.id_eq, h.spec_refines, h.realization_mono, h.preserves_wellFormed wf⟩

theorem HoleLeq.toStar {ev : Evidence} {Γ : Ctx} {h₁ h₂ : DesignHole}
    (h : HoleLeq ev Γ h₁ h₂) : HoleRefinesStar ev Γ h₁ h₂ := by
  obtain ⟨hid, hspec, hmono, hwf⟩ := h
  obtain ⟨id₁, S₁, r₁⟩ := h₁
  obtain ⟨id₂, S₂, r₂⟩ := h₂
  simp only at hid hspec hmono hwf
  subst hid
  cases r₁ with
  | none =>
    cases r₂ with
    | none => exact .single (.refine hspec)
    | some e => exact .of_two (.refine hspec) (.realize (hwf e rfl))
  | some e =>
    have := hmono e rfl
    subst this
    exact .single (.strengthen hspec (hwf e rfl))

/-- The closure of the step relation is *exactly* the preorder `HoleLeq`
    (on well-formed starting holes). -/
theorem HoleRefinesStar_iff_HoleLeq {ev : Evidence} {Γ : Ctx} {h₁ h₂ : DesignHole}
    (wf : WellFormedHole ev Γ h₁) :
    HoleRefinesStar ev Γ h₁ h₂ ↔ HoleLeq ev Γ h₁ h₂ :=
  ⟨HoleRefinesStar.toLeq wf, HoleLeq.toStar⟩

end PersistentHole
