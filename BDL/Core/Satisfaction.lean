import BDL.Core.Typing

/-!
# Satisfaction — evidence, realization satisfaction, and the declaration lifecycle

Phase-0 content, ported to environment-dependent evidence.

## Why evidence now depends on the environment

In Phase 0, `Evidence : Expr → PropertyId → Prop`.  Once a realization may
refer to another declaration, evidence for "`A` is monotone" may legitimately
rest on "`B` is committed to be monotone" — a fact about the *environment*,
not about `A`'s syntax.  So `Evidence : DeclEnv → Expr → PropertyId → Prop`.

**Validation boundary.**  This is the layer that depends on commitments and
evidence; typing (`Typing.lean`) never does.

Does refining `B` preserve evidence about `A`?  Not in general — see
`Experiments.probe6_breaks`.  `Evidence.Monotone` is the **stability
condition** required of evidence that is intended to *survive* monotone
environment refinement; it is not a claim that all valid evidence is
monotone.  Positively-stated compositional evidence (consulting only the
*presence* of commitments and realizations) is monotone; evidence that
consults the *absence* of information is not.

Future distinction (documented, not implemented): the validation layer will
eventually separate
* *stable* (monotone) evidence, which survives refinement, from
* *environment-sensitive* evidence, which must be flagged for recheck when
  the environment changes — including after arbitrary edits (D-16), which
  are outside `EnvRefines` altogether.
-/

namespace BDL

abbrev Evidence := DeclEnv → Expr → PropertyId → Prop

/-- Stability under monotone environment refinement.  Required of evidence that
    is meant to survive refinement of the declarations it depends on. -/
def Evidence.Monotone (ev : Evidence) : Prop :=
  ∀ (Δ₁ Δ₂ : DeclEnv) (e : Expr) (p : PropertyId),
    EnvRefines Δ₁ Δ₂ → ev Δ₁ e p → ev Δ₂ e p

/-- Evidence that ignores the environment (the Phase-0 notion) is monotone. -/
theorem Evidence.Monotone.of_const (f : Expr → PropertyId → Prop) :
    Evidence.Monotone (fun _ e p => f e p) :=
  fun _ _ _ _ _ h => h

/-- `e` is a valid realization of `S` in environment `Δ` and context `Γ`. -/
def Satisfies (ev : Evidence) (Δ : DeclEnv) (Γ : Ctx) (e : Expr) (S : DeclInterface) : Prop :=
  HasType Δ Γ e S.expectedType ∧ ∀ p ∈ S.commitments, ev Δ e p

instance (ev : Evidence) [∀ Δ e p, Decidable (ev Δ e p)] (Δ : DeclEnv) (Γ : Ctx) (e : Expr) (S : DeclInterface) :
    Decidable (Satisfies ev Δ Γ e S) :=
  inferInstanceAs (Decidable (HasType Δ Γ e S.expectedType ∧ ∀ p ∈ S.commitments, ev Δ e p))

/-- **Theorem 5 (interface level).**  A realization of a refined interface
    realizes the original interface. -/
theorem Satisfies.of_refines {ev : Evidence} {Δ : DeclEnv} {Γ : Ctx} {e : Expr} {S₀ S₁ : DeclInterface}
    (h : InterfaceRefines S₀ S₁) (hs : Satisfies ev Δ Γ e S₁) : Satisfies ev Δ Γ e S₀ :=
  ⟨h.expectedType_eq ▸ hs.1, fun p hp => hs.2 p (h.commitments_subset hp)⟩

/-- Satisfaction survives environment refinement — given monotone evidence. -/
theorem Satisfies.of_envRefines {ev : Evidence} (mono : ev.Monotone)
    {Δ₁ Δ₂ : DeclEnv} (er : EnvRefines Δ₁ Δ₂) {Γ : Ctx} {e : Expr} {S : DeclInterface}
    (hs : Satisfies ev Δ₁ Γ e S) : Satisfies ev Δ₂ Γ e S :=
  ⟨hs.1.of_envRefines er, fun p hp => mono _ _ _ _ er (hs.2 p hp)⟩

/-- **Completeness of `InterfaceRefines`.**  With evidence abstract, the syntactic
    refinement relation is exactly the semantic one. -/
theorem InterfaceRefines_iff_semantic (S₀ S₁ : DeclInterface) :
    InterfaceRefines S₀ S₁ ↔
      ∀ (ev : Evidence) (Δ : DeclEnv) (Γ : Ctx) (e : Expr),
        Satisfies ev Δ Γ e S₁ → Satisfies ev Δ Γ e S₀ := by
  constructor
  · intro h ev Δ Γ e hs
    exact hs.of_refines h
  · intro h
    constructor
    · -- realize `S₁` by an unresolved declaration of its type, trivial evidence
      have hs := h (fun _ _ _ => True) (.single ⟨0⟩ S₁.expectedType) [] (.declRef ⟨0⟩)
        ⟨DeclEnv.single_hasType _ _ [], fun _ _ => trivial⟩
      exact hs.1.unique (DeclEnv.single_hasType _ _ [])
    · intro p hp
      have hs := h (fun _ _ q => q ∈ S₁.commitments) (.single ⟨0⟩ S₁.expectedType) [] (.declRef ⟨0⟩)
        ⟨DeclEnv.single_hasType _ _ [], fun _ hq => hq⟩
      exact hs.2 p hp

/-! ## Well-formed declarations -/

/-- A realized declaration's term satisfies its *current* interface; an
    unresolved declaration is always well formed (every `DeclInterface` is
    valid in this model). -/
def WellFormedDecl (ev : Evidence) (Δ : DeclEnv) (Γ : Ctx) (h : DesignDecl) : Prop :=
  ∀ e, h.realization = some e → Satisfies ev Δ Γ e h.interface

theorem WellFormedDecl.unresolved (ev : Evidence) (Δ : DeclEnv) (Γ : Ctx) (id : DeclId) (S : DeclInterface) :
    WellFormedDecl ev Δ Γ (.unresolved id S) :=
  fun _ h => nomatch h

theorem WellFormedDecl.realized {ev : Evidence} {Δ : DeclEnv} {Γ : Ctx} {id : DeclId} {S : DeclInterface} {e : Expr}
    (hs : Satisfies ev Δ Γ e S) : WellFormedDecl ev Δ Γ ⟨id, S, some e⟩ :=
  fun _ h => Option.some.inj h ▸ hs

theorem WellFormedDecl.of_envRefines {ev : Evidence} (mono : ev.Monotone)
    {Δ₁ Δ₂ : DeclEnv} (er : EnvRefines Δ₁ Δ₂) {Γ : Ctx} {h : DesignDecl}
    (wf : WellFormedDecl ev Δ₁ Γ h) : WellFormedDecl ev Δ₂ Γ h :=
  fun e he => (wf e he).of_envRefines mono er

instance (ev : Evidence) [∀ Δ e p, Decidable (ev Δ e p)] (Δ : DeclEnv) (Γ : Ctx) (h : DesignDecl) :
    Decidable (WellFormedDecl ev Δ Γ h) :=
  match hr : h.realization with
  | none => isTrue fun _ h' => by rw [hr] at h'; exact nomatch h'
  | some e =>
    if hs : Satisfies ev Δ Γ e h.interface then
      isTrue fun _ h' => by rw [hr] at h'; exact Option.some.inj h' ▸ hs
    else
      isFalse fun wf => hs (wf e hr)

/-! ## The lifecycle relation -/

/-- One monotone-refinement step of a declaration, with side conditions
    checked in `Δ`.  Identity preservation is definitional: each rule reuses
    `id`.  The three steps are: refine the interface of an unresolved
    declaration; realize it; strengthen the interface of a realized
    declaration *with re-verification*.  Nothing else is a refinement. -/
inductive DeclRefines (ev : Evidence) (Δ : DeclEnv) (Γ : Ctx) : DesignDecl → DesignDecl → Prop where
  | refine {id : DeclId} {S S' : DeclInterface}
      (h : InterfaceRefines S S') :
      DeclRefines ev Δ Γ ⟨id, S, none⟩ ⟨id, S', none⟩
  | realize {id : DeclId} {S : DeclInterface} {e : Expr}
      (hs : Satisfies ev Δ Γ e S) :
      DeclRefines ev Δ Γ ⟨id, S, none⟩ ⟨id, S, some e⟩
  | strengthen {id : DeclId} {S S' : DeclInterface} {e : Expr}
      (h : InterfaceRefines S S') (hs : Satisfies ev Δ Γ e S') :
      DeclRefines ev Δ Γ ⟨id, S, some e⟩ ⟨id, S', some e⟩

section SingleStep
variable {ev : Evidence} {Δ : DeclEnv} {Γ : Ctx} {h₁ h₂ : DesignDecl}

/-- **Theorem 1 — identity preservation.** -/
theorem DeclRefines.id_eq (h : DeclRefines ev Δ Γ h₁ h₂) : h₁.id = h₂.id := by
  cases h <;> rfl

theorem DeclRefines.interface_refines (h : DeclRefines ev Δ Γ h₁ h₂) : InterfaceRefines h₁.interface h₂.interface := by
  cases h with
  | refine h => exact h
  | realize _ => exact InterfaceRefines.refl _
  | strengthen h _ => exact h

/-- **Theorem 2 — type commitment preservation.** -/
theorem DeclRefines.expectedType_eq (h : DeclRefines ev Δ Γ h₁ h₂) :
    h₁.interface.expectedType = h₂.interface.expectedType :=
  h.interface_refines.expectedType_eq

/-- **Theorem 3 — commitment monotonicity.** -/
theorem DeclRefines.commitments_subset (h : DeclRefines ev Δ Γ h₁ h₂) :
    h₁.interface.commitments ⊆ h₂.interface.commitments :=
  h.interface_refines.commitments_subset

theorem DeclRefines.realization_mono (h : DeclRefines ev Δ Γ h₁ h₂) :
    ∀ e, h₁.realization = some e → h₂.realization = some e := by
  cases h with
  | refine _ => intro _ h; exact nomatch h
  | realize _ => intro _ h; exact nomatch h
  | strengthen _ _ => intro _ h; exact h

/-- A lifecycle step is a structural step. -/
theorem DeclRefines.toLeq (h : DeclRefines ev Δ Γ h₁ h₂) : DeclLeq h₁ h₂ :=
  ⟨h.id_eq, h.interface_refines, h.realization_mono⟩

/-- The target of a step is well formed, from the step's own side conditions. -/
theorem DeclRefines.wellFormed_target (h : DeclRefines ev Δ Γ h₁ h₂) : WellFormedDecl ev Δ Γ h₂ := by
  cases h with
  | refine _ => exact WellFormedDecl.unresolved ev Δ Γ _ _
  | realize hs => exact WellFormedDecl.realized hs
  | strengthen _ hs => exact WellFormedDecl.realized hs

/-- **Theorem 4 — well-formedness preservation.**  The hypothesis `wf` is
    unused: the target's well-formedness is `wellFormed_target`.  (Phase-0
    finding: the invariant lives in the definition, so this theorem has no
    independent content.) -/
theorem DeclRefines.preserves_wellFormed
    (_wf : WellFormedDecl ev Δ Γ h₁) (h : DeclRefines ev Δ Γ h₁ h₂) :
    WellFormedDecl ev Δ Γ h₂ :=
  h.wellFormed_target

/-- A step whose side conditions hold in `Δ₁` also holds in any refinement `Δ₂`. -/
theorem DeclRefines.of_envRefines (mono : ev.Monotone) {Δ₂ : DeclEnv} (er : EnvRefines Δ Δ₂)
    (h : DeclRefines ev Δ Γ h₁ h₂) : DeclRefines ev Δ₂ Γ h₁ h₂ := by
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

theorem InterfaceRefines.of_star {S₀ Sₙ : DeclInterface} (h : Star InterfaceRefines S₀ Sₙ) : InterfaceRefines S₀ Sₙ :=
  h.elim InterfaceRefines.refl InterfaceRefines.trans id

/-- **Theorem 5 (n-step).** -/
theorem Satisfies.of_refines_star {ev : Evidence} {Δ : DeclEnv} {Γ : Ctx} {e : Expr} {S₀ Sₙ : DeclInterface}
    (h : Star InterfaceRefines S₀ Sₙ) (hs : Satisfies ev Δ Γ e Sₙ) : Satisfies ev Δ Γ e S₀ :=
  hs.of_refines (InterfaceRefines.of_star h)

/-- **Theorem 6.**  Multi-step lifecycle (all side conditions checked in `Δ`). -/
abbrev DeclRefinesStar (ev : Evidence) (Δ : DeclEnv) (Γ : Ctx) : DesignDecl → DesignDecl → Prop :=
  Star (DeclRefines ev Δ Γ)

section MultiStep
variable {ev : Evidence} {Δ : DeclEnv} {Γ : Ctx} {h₀ h₁ h₂ : DesignDecl}

theorem DeclRefinesStar.of_two (a : DeclRefines ev Δ Γ h₀ h₁) (b : DeclRefines ev Δ Γ h₁ h₂) :
    DeclRefinesStar ev Δ Γ h₀ h₂ :=
  .step a (.single b)

theorem DeclRefinesStar.toLeq (h : DeclRefinesStar ev Δ Γ h₀ h₂) : DeclLeq h₀ h₂ :=
  h.elim DeclLeq.refl DeclLeq.trans DeclRefines.toLeq

theorem DeclRefinesStar.id_eq (h : DeclRefinesStar ev Δ Γ h₀ h₂) : h₀.id = h₂.id := h.toLeq.id_eq
theorem DeclRefinesStar.interface_refines (h : DeclRefinesStar ev Δ Γ h₀ h₂) : InterfaceRefines h₀.interface h₂.interface :=
  h.toLeq.interface_refines

theorem DeclRefinesStar.preserves_wellFormed
    (wf : WellFormedDecl ev Δ Γ h₀) (h : DeclRefinesStar ev Δ Γ h₀ h₂) : WellFormedDecl ev Δ Γ h₂ := by
  induction h with
  | refl _ => exact wf
  | step hab _ ih => exact ih (hab.preserves_wellFormed wf)

/-- **Theorem 5 (declaration level).**  The eventual realization satisfies
    the interface the declaration had at every earlier point in its life. -/
theorem DeclRefinesStar.final_realization_satisfies_all
    (wf : WellFormedDecl ev Δ Γ h₀) (h : DeclRefinesStar ev Δ Γ h₀ h₂)
    {e : Expr} (he : h₂.realization = some e) : Satisfies ev Δ Γ e h₀.interface :=
  (h.preserves_wellFormed wf e he).of_refines h.interface_refines

/-- The lifecycle closure is exactly: structural order + well-formed target. -/
theorem DeclRefinesStar_iff (wf : WellFormedDecl ev Δ Γ h₁) :
    DeclRefinesStar ev Δ Γ h₁ h₂ ↔ DeclLeq h₁ h₂ ∧ WellFormedDecl ev Δ Γ h₂ := by
  constructor
  · intro h
    exact ⟨h.toLeq, h.preserves_wellFormed wf⟩
  · rintro ⟨⟨dId, hspec, hmono⟩, hwf⟩
    obtain ⟨id₁, S₁, r₁⟩ := h₁
    obtain ⟨id₂, S₂, r₂⟩ := h₂
    simp only at dId hspec hmono
    subst dId
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
