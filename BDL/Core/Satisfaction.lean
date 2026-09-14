import BDL.Core.Typing

/-!
# Satisfaction — evidence, realization satisfaction, and the hole lifecycle

Phase-0 content, ported to environment-dependent evidence.

## Why evidence now depends on the environment

In Phase 0, `Evidence : Expr → PropertyId → Prop`.  Once a realization may
refer to another hole, evidence for "`A` is monotone" may legitimately rest on
"`B` is committed to be monotone" — a fact about the *environment*, not about
`A`'s syntax.  So `Evidence : HoleEnv → Expr → PropertyId → Prop`.

This immediately raises the question the Phase-1 theorem must answer: does
refining `B` preserve evidence about `A`?  Not in general — see
`Experiments.nonmonotone_evidence_breaks_preservation`.  The invariant that
makes it hold is `Evidence.Monotone`: evidence must be stable under
environment refinement.  Positively-stated compositional evidence
(consulting only the *presence* of obligations and realizations) is monotone;
evidence that consults the *absence* of information is not.
-/

namespace BDL

abbrev Evidence := HoleEnv → Expr → PropertyId → Prop

/-- Evidence is stable under environment refinement. -/
def Evidence.Monotone (ev : Evidence) : Prop :=
  ∀ (Δ₁ Δ₂ : HoleEnv) (e : Expr) (p : PropertyId),
    EnvRefines Δ₁ Δ₂ → ev Δ₁ e p → ev Δ₂ e p

/-- Evidence that ignores the environment (the Phase-0 notion) is monotone. -/
theorem Evidence.Monotone.of_const (f : Expr → PropertyId → Prop) :
    Evidence.Monotone (fun _ e p => f e p) :=
  fun _ _ _ _ _ h => h

/-- `e` is a valid realization of `S` in environment `Δ` and context `Γ`. -/
def Satisfies (ev : Evidence) (Δ : HoleEnv) (Γ : Ctx) (e : Expr) (S : Spec) : Prop :=
  HasType Δ Γ e S.expectedType ∧ ∀ p ∈ S.obligations, ev Δ e p

instance (ev : Evidence) [∀ Δ e p, Decidable (ev Δ e p)] (Δ : HoleEnv) (Γ : Ctx) (e : Expr) (S : Spec) :
    Decidable (Satisfies ev Δ Γ e S) :=
  inferInstanceAs (Decidable (HasType Δ Γ e S.expectedType ∧ ∀ p ∈ S.obligations, ev Δ e p))

/-- **Theorem 5 (spec level).**  A realization of a refined spec realizes the
    original spec. -/
theorem Satisfies.of_refines {ev : Evidence} {Δ : HoleEnv} {Γ : Ctx} {e : Expr} {S₀ S₁ : Spec}
    (h : Refines S₀ S₁) (hs : Satisfies ev Δ Γ e S₁) : Satisfies ev Δ Γ e S₀ :=
  ⟨h.expectedType_eq ▸ hs.1, fun p hp => hs.2 p (h.obligations_subset hp)⟩

/-- Satisfaction survives environment refinement — given monotone evidence. -/
theorem Satisfies.of_envRefines {ev : Evidence} (mono : ev.Monotone)
    {Δ₁ Δ₂ : HoleEnv} (er : EnvRefines Δ₁ Δ₂) {Γ : Ctx} {e : Expr} {S : Spec}
    (hs : Satisfies ev Δ₁ Γ e S) : Satisfies ev Δ₂ Γ e S :=
  ⟨hs.1.of_envRefines er, fun p hp => mono _ _ _ _ er (hs.2 p hp)⟩

/-- **Completeness of `Refines`.**  With evidence abstract, the syntactic
    refinement relation is exactly the semantic one. -/
theorem Refines_iff_semantic (S₀ S₁ : Spec) :
    Refines S₀ S₁ ↔
      ∀ (ev : Evidence) (Δ : HoleEnv) (Γ : Ctx) (e : Expr),
        Satisfies ev Δ Γ e S₁ → Satisfies ev Δ Γ e S₀ := by
  constructor
  · intro h ev Δ Γ e hs
    exact hs.of_refines h
  · intro h
    constructor
    · have hs := h (fun _ _ _ => True) .empty [] S₁.expectedType.canon
        ⟨S₁.expectedType.canon_hasType _ [], fun _ _ => trivial⟩
      exact hs.1.unique (S₁.expectedType.canon_hasType _ [])
    · intro p hp
      have hs := h (fun _ _ q => q ∈ S₁.obligations) .empty [] S₁.expectedType.canon
        ⟨S₁.expectedType.canon_hasType _ [], fun _ hq => hq⟩
      exact hs.2 p hp

/-! ## Well-formed holes -/

/-- A realized hole's term satisfies its *current* spec; an unresolved hole is
    always well formed (every `Spec` is valid in this model). -/
def WellFormedHole (ev : Evidence) (Δ : HoleEnv) (Γ : Ctx) (h : DesignHole) : Prop :=
  ∀ e, h.realization = some e → Satisfies ev Δ Γ e h.spec

theorem WellFormedHole.unresolved (ev : Evidence) (Δ : HoleEnv) (Γ : Ctx) (id : HoleId) (S : Spec) :
    WellFormedHole ev Δ Γ (.unresolved id S) :=
  fun _ h => nomatch h

theorem WellFormedHole.realized {ev : Evidence} {Δ : HoleEnv} {Γ : Ctx} {id : HoleId} {S : Spec} {e : Expr}
    (hs : Satisfies ev Δ Γ e S) : WellFormedHole ev Δ Γ ⟨id, S, some e⟩ :=
  fun _ h => Option.some.inj h ▸ hs

theorem WellFormedHole.of_envRefines {ev : Evidence} (mono : ev.Monotone)
    {Δ₁ Δ₂ : HoleEnv} (er : EnvRefines Δ₁ Δ₂) {Γ : Ctx} {h : DesignHole}
    (wf : WellFormedHole ev Δ₁ Γ h) : WellFormedHole ev Δ₂ Γ h :=
  fun e he => (wf e he).of_envRefines mono er

instance (ev : Evidence) [∀ Δ e p, Decidable (ev Δ e p)] (Δ : HoleEnv) (Γ : Ctx) (h : DesignHole) :
    Decidable (WellFormedHole ev Δ Γ h) :=
  match hr : h.realization with
  | none => isTrue fun _ h' => by rw [hr] at h'; exact nomatch h'
  | some e =>
    if hs : Satisfies ev Δ Γ e h.spec then
      isTrue fun _ h' => by rw [hr] at h'; exact Option.some.inj h' ▸ hs
    else
      isFalse fun wf => hs (wf e hr)

/-! ## The lifecycle relation -/

/-- One lifecycle step of a hole, with side conditions checked in `Δ`.
    Identity preservation is definitional: each rule reuses `id`. -/
inductive HoleRefines (ev : Evidence) (Δ : HoleEnv) (Γ : Ctx) : DesignHole → DesignHole → Prop where
  | refine {id : HoleId} {S S' : Spec}
      (h : Refines S S') :
      HoleRefines ev Δ Γ ⟨id, S, none⟩ ⟨id, S', none⟩
  | realize {id : HoleId} {S : Spec} {e : Expr}
      (hs : Satisfies ev Δ Γ e S) :
      HoleRefines ev Δ Γ ⟨id, S, none⟩ ⟨id, S, some e⟩
  | strengthen {id : HoleId} {S S' : Spec} {e : Expr}
      (h : Refines S S') (hs : Satisfies ev Δ Γ e S') :
      HoleRefines ev Δ Γ ⟨id, S, some e⟩ ⟨id, S', some e⟩

section SingleStep
variable {ev : Evidence} {Δ : HoleEnv} {Γ : Ctx} {h₁ h₂ : DesignHole}

/-- **Theorem 1 — identity preservation.** -/
theorem HoleRefines.id_eq (h : HoleRefines ev Δ Γ h₁ h₂) : h₁.id = h₂.id := by
  cases h <;> rfl

theorem HoleRefines.spec_refines (h : HoleRefines ev Δ Γ h₁ h₂) : Refines h₁.spec h₂.spec := by
  cases h with
  | refine h => exact h
  | realize _ => exact Refines.refl _
  | strengthen h _ => exact h

/-- **Theorem 2 — type commitment preservation.** -/
theorem HoleRefines.expectedType_eq (h : HoleRefines ev Δ Γ h₁ h₂) :
    h₁.spec.expectedType = h₂.spec.expectedType :=
  h.spec_refines.expectedType_eq

/-- **Theorem 3 — obligation monotonicity.** -/
theorem HoleRefines.obligations_subset (h : HoleRefines ev Δ Γ h₁ h₂) :
    h₁.spec.obligations ⊆ h₂.spec.obligations :=
  h.spec_refines.obligations_subset

theorem HoleRefines.realization_mono (h : HoleRefines ev Δ Γ h₁ h₂) :
    ∀ e, h₁.realization = some e → h₂.realization = some e := by
  cases h with
  | refine _ => intro _ h; exact nomatch h
  | realize _ => intro _ h; exact nomatch h
  | strengthen _ _ => intro _ h; exact h

/-- A lifecycle step is a structural step. -/
theorem HoleRefines.toLeq (h : HoleRefines ev Δ Γ h₁ h₂) : HoleLeq h₁ h₂ :=
  ⟨h.id_eq, h.spec_refines, h.realization_mono⟩

/-- The target of a step is well formed, from the step's own side conditions. -/
theorem HoleRefines.wellFormed_target (h : HoleRefines ev Δ Γ h₁ h₂) : WellFormedHole ev Δ Γ h₂ := by
  cases h with
  | refine _ => exact WellFormedHole.unresolved ev Δ Γ _ _
  | realize hs => exact WellFormedHole.realized hs
  | strengthen _ hs => exact WellFormedHole.realized hs

/-- **Theorem 4 — well-formedness preservation.**  The hypothesis `wf` is
    unused: the target's well-formedness is `wellFormed_target`.  (Phase-0
    finding: the invariant lives in the definition, so this theorem has no
    independent content.) -/
theorem HoleRefines.preserves_wellFormed
    (_wf : WellFormedHole ev Δ Γ h₁) (h : HoleRefines ev Δ Γ h₁ h₂) :
    WellFormedHole ev Δ Γ h₂ :=
  h.wellFormed_target

/-- A step whose side conditions hold in `Δ₁` also holds in any refinement `Δ₂`. -/
theorem HoleRefines.of_envRefines (mono : ev.Monotone) {Δ₂ : HoleEnv} (er : EnvRefines Δ Δ₂)
    (h : HoleRefines ev Δ Γ h₁ h₂) : HoleRefines ev Δ₂ Γ h₁ h₂ := by
  cases h with
  | refine h => exact .refine h
  | realize hs => exact .realize (hs.of_envRefines mono er)
  | strengthen h hs => exact .strengthen h (hs.of_envRefines mono er)

end SingleStep

/-! ## Reflexive–transitive closure -/

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

theorem elim {S : α → α → Prop} (hrefl : ∀ a, S a a)
    (htrans : ∀ {a b c}, S a b → S b c → S a c) (hsub : ∀ {a b}, R a b → S a b)
    {a b : α} (h : Star R a b) : S a b := by
  induction h with
  | refl a => exact hrefl a
  | step hab _ ih => exact htrans (hsub hab) ih

end Star

theorem Refines.of_star {S₀ Sₙ : Spec} (h : Star Refines S₀ Sₙ) : Refines S₀ Sₙ :=
  h.elim Refines.refl Refines.trans id

/-- **Theorem 5 (n-step).** -/
theorem Satisfies.of_refines_star {ev : Evidence} {Δ : HoleEnv} {Γ : Ctx} {e : Expr} {S₀ Sₙ : Spec}
    (h : Star Refines S₀ Sₙ) (hs : Satisfies ev Δ Γ e Sₙ) : Satisfies ev Δ Γ e S₀ :=
  hs.of_refines (Refines.of_star h)

/-- **Theorem 6.**  Multi-step lifecycle (all side conditions checked in `Δ`). -/
abbrev HoleRefinesStar (ev : Evidence) (Δ : HoleEnv) (Γ : Ctx) : DesignHole → DesignHole → Prop :=
  Star (HoleRefines ev Δ Γ)

section MultiStep
variable {ev : Evidence} {Δ : HoleEnv} {Γ : Ctx} {h₀ h₁ h₂ : DesignHole}

theorem HoleRefinesStar.of_two (a : HoleRefines ev Δ Γ h₀ h₁) (b : HoleRefines ev Δ Γ h₁ h₂) :
    HoleRefinesStar ev Δ Γ h₀ h₂ :=
  .step a (.single b)

theorem HoleRefinesStar.toLeq (h : HoleRefinesStar ev Δ Γ h₀ h₂) : HoleLeq h₀ h₂ :=
  h.elim HoleLeq.refl HoleLeq.trans HoleRefines.toLeq

theorem HoleRefinesStar.id_eq (h : HoleRefinesStar ev Δ Γ h₀ h₂) : h₀.id = h₂.id := h.toLeq.id_eq
theorem HoleRefinesStar.spec_refines (h : HoleRefinesStar ev Δ Γ h₀ h₂) : Refines h₀.spec h₂.spec :=
  h.toLeq.spec_refines

theorem HoleRefinesStar.preserves_wellFormed
    (wf : WellFormedHole ev Δ Γ h₀) (h : HoleRefinesStar ev Δ Γ h₀ h₂) : WellFormedHole ev Δ Γ h₂ := by
  induction h with
  | refl _ => exact wf
  | step hab _ ih => exact ih (hab.preserves_wellFormed wf)

/-- **Theorem 5 (hole level).**  The eventual realization satisfies the spec
    the hole had at every earlier point in its life. -/
theorem HoleRefinesStar.final_realization_satisfies_all
    (wf : WellFormedHole ev Δ Γ h₀) (h : HoleRefinesStar ev Δ Γ h₀ h₂)
    {e : Expr} (he : h₂.realization = some e) : Satisfies ev Δ Γ e h₀.spec :=
  (h.preserves_wellFormed wf e he).of_refines h.spec_refines

/-- The lifecycle closure is exactly: structural order + well-formed target. -/
theorem HoleRefinesStar_iff (wf : WellFormedHole ev Δ Γ h₁) :
    HoleRefinesStar ev Δ Γ h₁ h₂ ↔ HoleLeq h₁ h₂ ∧ WellFormedHole ev Δ Γ h₂ := by
  constructor
  · intro h
    exact ⟨h.toLeq, h.preserves_wellFormed wf⟩
  · rintro ⟨⟨hid, hspec, hmono⟩, hwf⟩
    obtain ⟨id₁, S₁, r₁⟩ := h₁
    obtain ⟨id₂, S₂, r₂⟩ := h₂
    simp only at hid hspec hmono
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

end MultiStep

end BDL
