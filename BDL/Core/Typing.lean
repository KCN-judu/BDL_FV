import BDL.Core.Hole

/-!
# Typing — the typing judgment against a hole environment

`HasType Δ Γ e τ`.  The only rule that consults `Δ` is `holeRef`, and it
consults `Δ.tyView` only.  Consequently typing is invariant under any change
to the environment that preserves the type view (`HasType.mono_env`), and in
particular under environment refinement (`HasType.of_envRefines`).  This is
the "signature-first" principle as a lemma: clients depend on signatures, not
on definitions.
-/

namespace BDL

inductive HasType (Δ : HoleEnv) : Ctx → Expr → Ty → Prop where
  | var     {Γ i τ} : Γ[i]? = some τ → HasType Δ Γ (.var i) τ
  | boolLit {Γ b}   : HasType Δ Γ (.boolLit b) .bool
  | natLit  {Γ n}   : HasType Δ Γ (.natLit n) .nat
  | lam     {Γ dom body cod} :
      HasType Δ (dom :: Γ) body cod → HasType Δ Γ (.lam dom body) (.arr dom cod)
  | app     {Γ f a dom cod} :
      HasType Δ Γ f (.arr dom cod) → HasType Δ Γ a dom → HasType Δ Γ (.app f a) cod
  | holeRef {Γ h τ} : Δ.tyView h = some τ → HasType Δ Γ (.holeRef h) τ

/-- Syntax-directed type inference. -/
def infer (Δ : HoleEnv) : Ctx → Expr → Option Ty
  | Γ, .var i        => Γ[i]?
  | _, .boolLit _    => some .bool
  | _, .natLit _     => some .nat
  | Γ, .lam dom body => (infer Δ (dom :: Γ) body).map (.arr dom)
  | Γ, .app f a      =>
    match infer Δ Γ f, infer Δ Γ a with
    | some (.arr dom cod), some dom' => if dom = dom' then some cod else none
    | _, _ => none
  | _, .holeRef h    => Δ.tyView h

theorem infer_sound {Δ : HoleEnv} :
    ∀ {Γ : Ctx} {e : Expr} {τ : Ty}, infer Δ Γ e = some τ → HasType Δ Γ e τ
  | _, .var _, _, h => .var h
  | _, .boolLit _, _, h => by cases h; exact .boolLit
  | _, .natLit _, _, h => by cases h; exact .natLit
  | _, .holeRef _, _, h => .holeRef h
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
        | arr dom cod =>
          simp [infer, hf, ha] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .app (infer_sound hf) (infer_sound ha)

theorem infer_complete {Δ : HoleEnv} {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : HasType Δ Γ e τ) : infer Δ Γ e = some τ := by
  induction h with
  | var h => exact h
  | boolLit => rfl
  | natLit => rfl
  | lam _ ih => simp [infer, ih]
  | app _ _ ihf iha => simp [infer, ihf, iha]
  | holeRef h => exact h

theorem HasType.unique {Δ : HoleEnv} {Γ : Ctx} {e : Expr} {τ₁ τ₂ : Ty}
    (h₁ : HasType Δ Γ e τ₁) (h₂ : HasType Δ Γ e τ₂) : τ₁ = τ₂ :=
  Option.some.inj ((infer_complete h₁).symm.trans (infer_complete h₂))

instance (Δ : HoleEnv) (Γ : Ctx) (e : Expr) (τ : Ty) : Decidable (HasType Δ Γ e τ) :=
  decidable_of_iff (infer Δ Γ e = some τ) ⟨infer_sound, infer_complete⟩

/-! ## Structural facts -/

/-- Weakening by extending the context at the tail (no index shifting needed). -/
theorem HasType.weaken_append {Δ : HoleEnv} {Γ : Ctx} {e : Expr} {τ : Ty}
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
  | holeRef h => exact .holeRef h

/-- A term well typed at top level is well typed in every context. -/
theorem HasType.of_closed {Δ : HoleEnv} {e : Expr} {τ : Ty}
    (h : HasType Δ [] e τ) (Γ : Ctx) : HasType Δ Γ e τ :=
  h.weaken_append Γ

/-- Every type is inhabited by a hole-free, variable-free term. -/
def Ty.canon : Ty → Expr
  | .bool => .boolLit true
  | .nat => .natLit 0
  | .arr a b => .lam a b.canon

theorem Ty.canon_hasType (Δ : HoleEnv) : ∀ (τ : Ty) (Γ : Ctx), HasType Δ Γ τ.canon τ
  | .bool, _ => .boolLit
  | .nat, _ => .natLit
  | .arr a b, Γ => .lam (b.canon_hasType Δ (a :: Γ))

/-! ## Typing depends on the environment only through its type view -/

/-- **Factoring lemma.**  If `Δ₂` declares every hole `Δ₁` declares, at the
    same expected type, then every `Δ₁`-typing is a `Δ₂`-typing.  No
    condition on obligations, realizations, or well-formedness. -/
theorem HasType.mono_env {Δ₁ Δ₂ : HoleEnv}
    (hv : ∀ h τ, Δ₁.tyView h = some τ → Δ₂.tyView h = some τ)
    {Γ : Ctx} {e : Expr} {τ : Ty} (h : HasType Δ₁ Γ e τ) : HasType Δ₂ Γ e τ := by
  induction h with
  | var h => exact .var h
  | boolLit => exact .boolLit
  | natLit => exact .natLit
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha
  | holeRef h => exact .holeRef (hv _ _ h)

theorem HasType.of_envRefines {Δ₁ Δ₂ : HoleEnv} (er : EnvRefines Δ₁ Δ₂)
    {Γ : Ctx} {e : Expr} {τ : Ty} (h : HasType Δ₁ Γ e τ) : HasType Δ₂ Γ e τ :=
  h.mono_env fun _ _ ht => er.tyView ht

/-- Every hole a well-typed term refers to is declared. -/
theorem HasType.refs_declared {Δ : HoleEnv} {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : HasType Δ Γ e τ) : ∀ x ∈ e.refs, ∃ τ', Δ.tyView x = some τ' := by
  induction h with
  | var _ | boolLit | natLit => intro x hx; simp [Expr.refs] at hx
  | lam _ ih => exact ih
  | app _ _ ihf iha =>
    intro x hx
    simp only [Expr.refs, List.mem_append] at hx
    exact hx.elim (ihf x) (iha x)
  | holeRef h =>
    intro x hx
    simp [Expr.refs] at hx
    subst hx
    exact ⟨_, h⟩

/-- A hole-free term's typing is independent of the environment. -/
theorem HasType.holeFree_env_irrelevant {Δ₁ Δ₂ : HoleEnv} {Γ : Ctx} {e : Expr} {τ : Ty}
    (hf : e.HoleFree) (h : HasType Δ₁ Γ e τ) : HasType Δ₂ Γ e τ := by
  induction h with
  | var h => exact .var h
  | boolLit => exact .boolLit
  | natLit => exact .natLit
  | lam _ ih => exact .lam (ih hf)
  | app _ _ ihf iha => exact .app (ihf hf.app_left) (iha hf.app_right)
  | holeRef _ => simp [Expr.HoleFree, Expr.refs] at hf

end BDL
