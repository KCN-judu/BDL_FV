import BDL.Core.Decl

/-!
# Typing — the typing judgment against declaration and concept environments

`HasType Θ Δ G Γ e τ`, where

* `Δ : DeclEnv`    — consulted through `Δ.tyView` **only** (Phase-1 invariant);
* `Θ : ConceptEnv` — consulted through the representation binding
                      `Θ s = some R` **only** (Phase 3);
* `G : Grant`      — which semantic concepts this term may *construct*.

Rules that touch the environments:

    Δ.tyView d = some τ                          Θ s = some R   Θ Δ G Γ ⊢ e : sem s
    ───────────────────────────                  ──────────────────────────────────
    Θ Δ G Γ ⊢ declRef d : τ                      Θ Δ G Γ ⊢ rep e : R

    G s      Θ s = some R      Θ Δ G Γ ⊢ e : R
    ─────────────────────────────────────────
    Θ Δ G Γ ⊢ mk s e : sem s

**Typing boundary.**  Typing depends on the type view of declarations and
the representation view of concepts, and on nothing else — not on
realizations, commitments, evidence or validation state.  `tyView` itself is
unchanged from Phase 1; Phase 3 added a *second, concept-level* projection,
not a wider declaration-level one.

**Construction boundary.**  Client code (wiring, references) is typed under
`Grant.none`.  A declaration's realization is typed under
`Grant.of` its own signature (`Satisfaction.lean`), so a semantic value of
`s` is constructed only inside a declaration that announces `sem s` — the
signature is the authority for crossing semantic identities.
-/

namespace BDL

inductive HasType (Θ : ConceptEnv) (Δ : DeclEnv) (G : Grant) : Ctx → Expr → Ty → Prop where
  | var     {Γ i τ} : Γ[i]? = some τ → HasType Θ Δ G Γ (.var i) τ
  | boolLit {Γ b}   : HasType Θ Δ G Γ (.boolLit b) .bool
  | natLit  {Γ n}   : HasType Θ Δ G Γ (.natLit n) .nat
  | lam     {Γ dom body cod} :
      HasType Θ Δ G (dom :: Γ) body cod → HasType Θ Δ G Γ (.lam dom body) (.arr dom cod)
  | app     {Γ f a dom cod} :
      HasType Θ Δ G Γ f (.arr dom cod) → HasType Θ Δ G Γ a dom → HasType Θ Δ G Γ (.app f a) cod
  | declRef {Γ d τ} : Δ.tyView d = some τ → HasType Θ Δ G Γ (.declRef d) τ
  | rep     {Γ e s R} : Θ s = some R → HasType Θ Δ G Γ e (.sem s) → HasType Θ Δ G Γ (.rep e) R
  | mk      {Γ e s R} : G s → Θ s = some R → HasType Θ Δ G Γ e R → HasType Θ Δ G Γ (.mk s e) (.sem s)
  | prim    {Γ p} : HasType Θ Δ G Γ (.prim p) p.ty
  /-- Phase 4.  Only *data* may be delayed, and only outside binders
      (empty context): temporal state belongs to a declaration, not to a
      function.  A delay under a lambda would require closures to persist
      across ticks. -/
  | delay   {i e τ} : τ.Data → HasType Θ Δ G [] i τ → HasType Θ Δ G [] e τ →
      HasType Θ Δ G [] (.delay i e) τ
  /-- Phase 5.  Same shape as `delay`: transport preserves the type, hence
      semantic identity and dimension.  Which domain `e` lives in is not a
      typing matter (`Clock.lean`). -/
  | sync    {c i e τ} : τ.Data → HasType Θ Δ G [] i τ → HasType Θ Δ G [] e τ →
      HasType Θ Δ G [] (.sync c i e) τ

/-- Syntax-directed type inference. -/
def infer (Θ : ConceptEnv) (Δ : DeclEnv) (G : Grant) [DecidablePred G] : Ctx → Expr → Option Ty
  | Γ, .var i        => Γ[i]?
  | _, .boolLit _    => some .bool
  | _, .natLit _     => some .nat
  | Γ, .lam dom body => (infer Θ Δ G (dom :: Γ) body).map (.arr dom)
  | Γ, .app f a      =>
    match infer Θ Δ G Γ f, infer Θ Δ G Γ a with
    | some (.arr dom cod), some dom' => if dom = dom' then some cod else none
    | _, _ => none
  | _, .declRef d    => Δ.tyView d
  | Γ, .rep e        =>
    match infer Θ Δ G Γ e with
    | some (.sem s) => Θ s
    | _ => none
  | Γ, .mk s e       =>
    if G s then
      match Θ s, infer Θ Δ G Γ e with
      | some R, some R' => if R = R' then some (.sem s) else none
      | _, _ => none
    else none
  | _, .prim p       => some p.ty
  | Γ, .delay i e    =>
    if Γ = [] then
      match infer Θ Δ G [] i, infer Θ Δ G [] e with
      | some τ, some τ' => if τ = τ' ∧ τ.Data then some τ else none
      | _, _ => none
    else none
  | Γ, .sync _ i e   =>
    if Γ = [] then
      match infer Θ Δ G [] i, infer Θ Δ G [] e with
      | some τ, some τ' => if τ = τ' ∧ τ.Data then some τ else none
      | _, _ => none
    else none

section Inference
variable {Θ : ConceptEnv} {Δ : DeclEnv} {G : Grant} [DecidablePred G]

theorem infer_sound :
    ∀ {Γ : Ctx} {e : Expr} {τ : Ty}, infer Θ Δ G Γ e = some τ → HasType Θ Δ G Γ e τ
  | _, .var _, _, h => .var h
  | _, .boolLit _, _, h => by cases h; exact .boolLit
  | _, .natLit _, _, h => by cases h; exact .natLit
  | _, .declRef _, _, h => .declRef h
  | _, .prim _, _, h => by cases h; exact .prim
  | Γ, .lam dom body, τ, h => by
    cases hb : infer Θ Δ G (dom :: Γ) body with
    | none => simp [infer, hb] at h
    | some cod =>
      simp [infer, hb] at h
      subst h
      exact .lam (infer_sound hb)
  | Γ, .app f a, τ, h => by
    cases hf : infer Θ Δ G Γ f with
    | none => simp [infer, hf] at h
    | some τf =>
      cases ha : infer Θ Δ G Γ a with
      | none => cases τf <;> simp [infer, hf, ha] at h
      | some τa =>
        cases τf with
        | bool => simp [infer, hf, ha] at h
        | nat => simp [infer, hf, ha] at h
        | sem _ => simp [infer, hf, ha] at h
        | q _ => simp [infer, hf, ha] at h
        | opt _ => simp [infer, hf, ha] at h
        | list _ => simp [infer, hf, ha] at h
        | arr dom cod =>
          simp [infer, hf, ha] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .app (infer_sound hf) (infer_sound ha)
  | Γ, .rep e, τ, h => by
    cases he : infer Θ Δ G Γ e with
    | none => simp [infer, he] at h
    | some τe =>
      cases τe with
      | sem s => simp [infer, he] at h; exact .rep h (infer_sound he)
      | bool => simp [infer, he] at h
      | nat => simp [infer, he] at h
      | q _ => simp [infer, he] at h
      | opt _ => simp [infer, he] at h
      | list _ => simp [infer, he] at h
      | arr _ _ => simp [infer, he] at h
  | Γ, .delay i e, τ, h => by
    by_cases hΓ : Γ = []
    · subst hΓ
      cases hi : infer Θ Δ G [] i with
      | none => simp [infer, hi] at h
      | some τi =>
        cases he : infer Θ Δ G [] e with
        | none => simp [infer, hi, he] at h
        | some τe =>
          simp [infer, hi, he] at h
          obtain ⟨⟨rfl, hd⟩, rfl⟩ := h
          exact .delay hd (infer_sound hi) (infer_sound he)
    · simp [infer, hΓ] at h
  | Γ, .sync c i e, τ, h => by
    by_cases hΓ : Γ = []
    · subst hΓ
      cases hi : infer Θ Δ G [] i with
      | none => simp [infer, hi] at h
      | some τi =>
        cases he : infer Θ Δ G [] e with
        | none => simp [infer, hi, he] at h
        | some τe =>
          simp [infer, hi, he] at h
          obtain ⟨⟨rfl, hd⟩, rfl⟩ := h
          exact .sync hd (infer_sound hi) (infer_sound he)
    · simp [infer, hΓ] at h
  | Γ, .mk s e, τ, h => by
    by_cases hg : G s
    · cases hΘ : Θ s with
      | none => simp [infer, hg, hΘ] at h
      | some R =>
        cases he : infer Θ Δ G Γ e with
        | none => simp [infer, hg, hΘ, he] at h
        | some R' =>
          simp [infer, hg, hΘ, he] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .mk hg hΘ (infer_sound he)
    · simp [infer, hg] at h

theorem infer_complete {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : HasType Θ Δ G Γ e τ) : infer Θ Δ G Γ e = some τ := by
  induction h with
  | var h => exact h
  | boolLit => rfl
  | natLit => rfl
  | lam _ ih => simp [infer, ih]
  | app _ _ ihf iha => simp [infer, ihf, iha]
  | declRef h => exact h
  | rep hΘ _ ih => simp [infer, ih, hΘ]
  | mk hg hΘ _ ih => simp [infer, hg, hΘ, ih]
  | prim => rfl
  | delay hd _ _ ihi ihe => simp [infer, ihi, ihe, hd]
  | sync hd _ _ ihi ihe => simp [infer, ihi, ihe, hd]

theorem HasType.unique {Γ : Ctx} {e : Expr} {τ₁ τ₂ : Ty}
    (h₁ : HasType Θ Δ G Γ e τ₁) (h₂ : HasType Θ Δ G Γ e τ₂) : τ₁ = τ₂ :=
  Option.some.inj ((infer_complete h₁).symm.trans (infer_complete h₂))

instance (Γ : Ctx) (e : Expr) (τ : Ty) : Decidable (HasType Θ Δ G Γ e τ) :=
  decidable_of_iff (infer Θ Δ G Γ e = some τ) ⟨infer_sound, infer_complete⟩

end Inference

/-! ## Structural facts -/

section Structural
variable {Θ : ConceptEnv} {Δ : DeclEnv} {G : Grant}

/-- Weakening by extending the context at the tail (no index shifting
    needed) — for the **delay-free** fragment.  A `delay` is typed only in the
    empty context, so a stateful term cannot be moved under binders; this is
    the domain of validity of the Phase-1 inlining results. -/
theorem HasType.weaken_append {Γ : Ctx} {e : Expr} {τ : Ty} (hd : e.DelayFree)
    (h : HasType Θ Δ G Γ e τ) (Γ' : Ctx) : HasType Θ Δ G (Γ ++ Γ') e τ := by
  induction h with
  | var h =>
    apply HasType.var
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp h
    rw [List.getElem?_append_left hlt]
    exact h
  | boolLit => exact .boolLit
  | natLit => exact .natLit
  | lam _ ih => exact .lam (ih hd)
  | app _ _ ihf iha => exact .app (ihf hd.1) (iha hd.2)
  | declRef h => exact .declRef h
  | rep hΘ _ ih => exact .rep hΘ (ih hd)
  | mk hg hΘ _ ih => exact .mk hg hΘ (ih hd)
  | prim => exact .prim
  | delay _ _ _ _ _ => exact hd.elim
  | sync _ _ _ _ _ => exact hd.elim

/-- A delay-free term well typed at top level is well typed in every context. -/
theorem HasType.of_closed {e : Expr} {τ : Ty} (hd : e.DelayFree)
    (h : HasType Θ Δ G [] e τ) (Γ : Ctx) : HasType Θ Δ G Γ e τ :=
  h.weaken_append hd Γ

/-- Every type is inhabited in some environment — by an *unresolved
    declaration* of that type.  Signature-first typing never needs closed
    inhabitants; it needs declarations. -/
def DeclEnv.single (d : DeclId) (τ : Ty) : DeclEnv :=
  fun id => if id = d then some ⟨d, ⟨τ, []⟩, none⟩ else none

theorem DeclEnv.single_hasType (d : DeclId) (τ : Ty) (Γ : Ctx) :
    HasType Θ (DeclEnv.single d τ) G Γ (.declRef d) τ :=
  .declRef (by simp [DeclEnv.tyView, DeclEnv.single])

/-! ## Monotonicity in each environment -/

/-- **Factoring lemma (declarations).**  Typing depends on `Δ` only through
    `tyView`. -/
theorem HasType.mono_env {Δ₁ Δ₂ : DeclEnv}
    (hv : ∀ d τ, Δ₁.tyView d = some τ → Δ₂.tyView d = some τ)
    {Γ : Ctx} {e : Expr} {τ : Ty} (h : HasType Θ Δ₁ G Γ e τ) : HasType Θ Δ₂ G Γ e τ := by
  induction h with
  | var h => exact .var h
  | boolLit => exact .boolLit
  | natLit => exact .natLit
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha
  | declRef h => exact .declRef (hv _ _ h)
  | rep hΘ _ ih => exact .rep hΘ ih
  | mk hg hΘ _ ih => exact .mk hg hΘ ih
  | prim => exact .prim
  | delay hd _ _ ihi ihe => exact .delay hd ihi ihe
  | sync hd _ _ ihi ihe => exact .sync hd ihi ihe

theorem HasType.of_envRefines {Δ₁ Δ₂ : DeclEnv} (er : EnvRefines Δ₁ Δ₂)
    {Γ : Ctx} {e : Expr} {τ : Ty} (h : HasType Θ Δ₁ G Γ e τ) : HasType Θ Δ₂ G Γ e τ :=
  h.mono_env fun _ _ ht => er.tyView ht

/-- **Factoring lemma (concepts).**  Binding more representations never
    breaks a derivation: the concept environment is write-once. -/
theorem HasType.mono_concept {Θ₁ Θ₂ : ConceptEnv} (hc : ConceptRefines Θ₁ Θ₂)
    {Γ : Ctx} {e : Expr} {τ : Ty} (h : HasType Θ₁ Δ G Γ e τ) : HasType Θ₂ Δ G Γ e τ := by
  induction h with
  | var h => exact .var h
  | boolLit => exact .boolLit
  | natLit => exact .natLit
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha
  | declRef h => exact .declRef h
  | rep hΘ _ ih => exact .rep (hc _ _ hΘ) ih
  | mk hg hΘ _ ih => exact .mk hg (hc _ _ hΘ) ih
  | prim => exact .prim
  | delay hd _ _ ihi ihe => exact .delay hd ihi ihe
  | sync hd _ _ ihi ihe => exact .sync hd ihi ihe

/-- Granting more construction rights never breaks a derivation. -/
theorem HasType.mono_grant {G₁ G₂ : Grant} (hg : ∀ s, G₁ s → G₂ s)
    {Γ : Ctx} {e : Expr} {τ : Ty} (h : HasType Θ Δ G₁ Γ e τ) : HasType Θ Δ G₂ Γ e τ := by
  induction h with
  | var h => exact .var h
  | boolLit => exact .boolLit
  | natLit => exact .natLit
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha
  | declRef h => exact .declRef h
  | rep hΘ _ ih => exact .rep hΘ ih
  | mk hg' hΘ _ ih => exact .mk (hg _ hg') hΘ ih
  | prim => exact .prim
  | delay hd _ _ ihi ihe => exact .delay hd ihi ihe
  | sync hd _ _ ihi ihe => exact .sync hd ihi ihe

theorem HasType.to_all {Γ : Ctx} {e : Expr} {τ : Ty} (h : HasType Θ Δ G Γ e τ) :
    HasType Θ Δ Grant.all Γ e τ :=
  h.mono_grant fun _ _ => trivial

/-- Does `mk s` occur in the term? -/
def Expr.constructs (s : SemanticId) : Expr → Prop
  | .lam _ b => b.constructs s
  | .app f a => f.constructs s ∨ a.constructs s
  | .rep e => e.constructs s
  | .mk s' e => s' = s ∨ e.constructs s
  | .delay i e => i.constructs s ∨ e.constructs s
  | .sync _ i e => i.constructs s ∨ e.constructs s
  | _ => False

/-- **Construction requires a grant** (syntactic form of the isolation
    invariant): a well-typed term constructs `s` only if `G s`.  Under
    `Grant.of τ` this says a value of `sem s` is built only inside a
    realization whose signature announces `sem s`. -/
theorem HasType.constructs_granted {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : HasType Θ Δ G Γ e τ) : ∀ s, e.constructs s → G s := by
  induction h with
  | var _ | boolLit | natLit | declRef _ | prim => intro s hs; exact hs.elim
  | lam _ ih => exact ih
  | app _ _ ihf iha => intro s hs; exact hs.elim (ihf s) (iha s)
  | rep _ _ ih => exact ih
  | mk hg _ _ ih =>
    intro s hs
    rcases hs with rfl | hs
    · exact hg
    · exact ih s hs
  | delay _ _ _ ihi ihe => intro s hs; exact hs.elim (ihi s) (ihe s)
  | sync _ _ _ ihi ihe => intro s hs; exact hs.elim (ihi s) (ihe s)

/-- Every declaration a well-typed term refers to exists in the environment. -/
theorem HasType.refs_declared {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : HasType Θ Δ G Γ e τ) : ∀ x ∈ e.refs, ∃ τ', Δ.tyView x = some τ' := by
  induction h with
  | var _ | boolLit | natLit | prim => intro x hx; simp [Expr.refs] at hx
  | lam _ ih => exact ih
  | app _ _ ihf iha =>
    intro x hx
    simp only [Expr.refs, List.mem_append] at hx
    exact hx.elim (ihf x) (iha x)
  | declRef h =>
    intro x hx
    simp [Expr.refs] at hx
    subst hx
    exact ⟨_, h⟩
  | rep _ _ ih => exact ih
  | mk _ _ _ ih => exact ih
  | delay _ _ _ ihi ihe =>
    intro x hx
    simp only [Expr.refs, List.mem_append] at hx
    exact hx.elim (ihi x) (ihe x)
  | sync _ _ _ ihi ihe =>
    intro x hx
    simp only [Expr.refs, List.mem_append] at hx
    exact hx.elim (ihi x) (ihe x)

/-- A reference-free term's typing is independent of the declaration environment. -/
theorem HasType.refFree_env_irrelevant {Δ₁ Δ₂ : DeclEnv} {Γ : Ctx} {e : Expr} {τ : Ty}
    (hf : e.RefFree) (h : HasType Θ Δ₁ G Γ e τ) : HasType Θ Δ₂ G Γ e τ := by
  induction h with
  | var h => exact .var h
  | boolLit => exact .boolLit
  | natLit => exact .natLit
  | lam _ ih => exact .lam (ih hf)
  | app _ _ ihf iha => exact .app (ihf hf.app_left) (iha hf.app_right)
  | declRef _ => simp [Expr.RefFree, Expr.refs] at hf
  | rep hΘ _ ih => exact .rep hΘ (ih hf)
  | mk hg hΘ _ ih => exact .mk hg hΘ (ih hf)
  | prim => exact .prim
  | delay hd _ _ ihi ihe =>
    exact .delay hd (ihi (List.append_eq_nil_iff.mp hf).1) (ihe (List.append_eq_nil_iff.mp hf).2)
  | sync hd _ _ ihi ihe =>
    exact .sync hd (ihi (List.append_eq_nil_iff.mp hf).1) (ihe (List.append_eq_nil_iff.mp hf).2)

end Structural

end BDL
