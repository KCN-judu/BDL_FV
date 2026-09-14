import BDL.Core.Decl

/-!
# Typing — the typing judgment against a declaration environment

`HasType Δ Γ e τ`.  The only rule that consults `Δ` is `declRef`, and it
consults `Δ.tyView` only:

    Δ.tyView d = some τ
    ─────────────────────────
    HasType Δ Γ (declRef d) τ

**Typing boundary (Phase-1 invariant).**  Typing depends on the type view of
the interface and nothing else: not on realizations, not on commitments,
not on evidence or validation state.  Validation (`Satisfaction.lean`) is
what depends on commitments and evidence.  Consequently typing is invariant
under any change to the environment that preserves the type view
(`HasType.mono_env`), in particular under environment refinement
(`HasType.of_envRefines`).  This is the "signature-first" principle as a
lemma: clients depend on interfaces, not on bodies.
-/

namespace BDL

inductive HasType (Δ : DeclEnv) : Ctx → Expr → Ty → Prop where
  | var     {Γ i τ} : Γ[i]? = some τ → HasType Δ Γ (.var i) τ
  | boolLit {Γ b}   : HasType Δ Γ (.boolLit b) .bool
  | natLit  {Γ n}   : HasType Δ Γ (.natLit n) .nat
  | lam     {Γ dom body cod} :
      HasType Δ (dom :: Γ) body cod → HasType Δ Γ (.lam dom body) (.arr dom cod)
  | app     {Γ f a dom cod} :
      HasType Δ Γ f (.arr dom cod) → HasType Δ Γ a dom → HasType Δ Γ (.app f a) cod
  | declRef {Γ h τ} : Δ.tyView h = some τ → HasType Δ Γ (.declRef h) τ

/-- Syntax-directed type inference. -/
def infer (Δ : DeclEnv) : Ctx → Expr → Option Ty
  | Γ, .var i        => Γ[i]?
  | _, .boolLit _    => some .bool
  | _, .natLit _     => some .nat
  | Γ, .lam dom body => (infer Δ (dom :: Γ) body).map (.arr dom)
  | Γ, .app f a      =>
    match infer Δ Γ f, infer Δ Γ a with
    | some (.arr dom cod), some dom' => if dom = dom' then some cod else none
    | _, _ => none
  | _, .declRef h    => Δ.tyView h

theorem infer_sound {Δ : DeclEnv} :
    ∀ {Γ : Ctx} {e : Expr} {τ : Ty}, infer Δ Γ e = some τ → HasType Δ Γ e τ
  | _, .var _, _, h => .var h
  | _, .boolLit _, _, h => by cases h; exact .boolLit
  | _, .natLit _, _, h => by cases h; exact .natLit
  | _, .declRef _, _, h => .declRef h
  | Γ, .lam dom body, τ, h => by
    cases hb : infer Δ (dom :: Γ) body with
    | none => simp [infer, hb] at h
    | some cod =>
      simp [infer, hb] at h
      subst h
      exact .lam (infer_sound hb)
  | Γ, .app f a, τ, h => by
    cases hf : infer Δ Γ f with
    | none => simp [infer, hf] at h
    | some τf =>
      cases ha : infer Δ Γ a with
      | none => cases τf <;> simp [infer, hf, ha] at h
      | some τa =>
        cases τf with
        | bool => simp [infer, hf, ha] at h
        | nat => simp [infer, hf, ha] at h
        | sem _ => simp [infer, hf, ha] at h
        | arr dom cod =>
          simp [infer, hf, ha] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .app (infer_sound hf) (infer_sound ha)

theorem infer_complete {Δ : DeclEnv} {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : HasType Δ Γ e τ) : infer Δ Γ e = some τ := by
  induction h with
  | var h => exact h
  | boolLit => rfl
  | natLit => rfl
  | lam _ ih => simp [infer, ih]
  | app _ _ ihf iha => simp [infer, ihf, iha]
  | declRef h => exact h

theorem HasType.unique {Δ : DeclEnv} {Γ : Ctx} {e : Expr} {τ₁ τ₂ : Ty}
    (h₁ : HasType Δ Γ e τ₁) (h₂ : HasType Δ Γ e τ₂) : τ₁ = τ₂ :=
  Option.some.inj ((infer_complete h₁).symm.trans (infer_complete h₂))

instance (Δ : DeclEnv) (Γ : Ctx) (e : Expr) (τ : Ty) : Decidable (HasType Δ Γ e τ) :=
  decidable_of_iff (infer Δ Γ e = some τ) ⟨infer_sound, infer_complete⟩

/-! ## Structural facts -/

/-- Weakening by extending the context at the tail (no index shifting needed). -/
theorem HasType.weaken_append {Δ : DeclEnv} {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : HasType Δ Γ e τ) (Γ' : Ctx) : HasType Δ (Γ ++ Γ') e τ := by
  induction h with
  | var h =>
    apply HasType.var
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp h
    rw [List.getElem?_append_left hlt]
    exact h
  | boolLit => exact .boolLit
  | natLit => exact .natLit
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha
  | declRef h => exact .declRef h

/-- A term well typed at top level is well typed in every context. -/
theorem HasType.of_closed {Δ : DeclEnv} {e : Expr} {τ : Ty}
    (h : HasType Δ [] e τ) (Γ : Ctx) : HasType Δ Γ e τ :=
  h.weaken_append Γ

/-- Every type is inhabited in some environment — by an *unresolved
    declaration* of that type.  (Phase 2 replaced the Phase-0 canonical
    closed inhabitant: opaque semantic types have none.  Signature-first
    typing never needs closed inhabitants; it needs declarations.) -/
def DeclEnv.single (d : DeclId) (τ : Ty) : DeclEnv :=
  fun id => if id = d then some ⟨d, ⟨τ, []⟩, none⟩ else none

theorem DeclEnv.single_hasType (d : DeclId) (τ : Ty) (Γ : Ctx) :
    HasType (DeclEnv.single d τ) Γ (.declRef d) τ :=
  .declRef (by simp [DeclEnv.tyView, DeclEnv.single])

/-! ## Typing depends on the environment only through its type view -/

/-- **Factoring lemma.**  If `Δ₂` declares everything `Δ₁` declares, at the
    same expected type, then every `Δ₁`-typing is a `Δ₂`-typing.  No
    condition on commitments, realizations, or well-formedness. -/
theorem HasType.mono_env {Δ₁ Δ₂ : DeclEnv}
    (hv : ∀ h τ, Δ₁.tyView h = some τ → Δ₂.tyView h = some τ)
    {Γ : Ctx} {e : Expr} {τ : Ty} (h : HasType Δ₁ Γ e τ) : HasType Δ₂ Γ e τ := by
  induction h with
  | var h => exact .var h
  | boolLit => exact .boolLit
  | natLit => exact .natLit
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha
  | declRef h => exact .declRef (hv _ _ h)

theorem HasType.of_envRefines {Δ₁ Δ₂ : DeclEnv} (er : EnvRefines Δ₁ Δ₂)
    {Γ : Ctx} {e : Expr} {τ : Ty} (h : HasType Δ₁ Γ e τ) : HasType Δ₂ Γ e τ :=
  h.mono_env fun _ _ ht => er.tyView ht

/-- Every declaration a well-typed term refers to exists in the environment. -/
theorem HasType.refs_declared {Δ : DeclEnv} {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : HasType Δ Γ e τ) : ∀ x ∈ e.refs, ∃ τ', Δ.tyView x = some τ' := by
  induction h with
  | var _ | boolLit | natLit => intro x hx; simp [Expr.refs] at hx
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

/-- A reference-free term's typing is independent of the environment. -/
theorem HasType.refFree_env_irrelevant {Δ₁ Δ₂ : DeclEnv} {Γ : Ctx} {e : Expr} {τ : Ty}
    (hf : e.RefFree) (h : HasType Δ₁ Γ e τ) : HasType Δ₂ Γ e τ := by
  induction h with
  | var h => exact .var h
  | boolLit => exact .boolLit
  | natLit => exact .natLit
  | lam _ ih => exact .lam (ih hf)
  | app _ _ ihf iha => exact .app (ihf hf.app_left) (iha hf.app_right)
  | declRef _ => simp [Expr.RefFree, Expr.refs] at hf

end BDL
