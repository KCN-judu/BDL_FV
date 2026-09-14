/-!
# Syntax — a tiny simply typed object language

Just enough STLC to give holes an `expectedType` and realizations a
typing judgment.  Variables are de Bruijn indices; binders are annotated
(Church style) so that typing is syntax-directed and decidable.

Nothing here is specific to design holes.
-/

namespace PersistentHole

inductive Ty where
  | bool
  | nat
  | arr (dom cod : Ty)
  deriving DecidableEq, Repr

inductive Expr where
  | var (i : Nat)                 -- de Bruijn index
  | boolLit (b : Bool)
  | natLit (n : Nat)
  | lam (dom : Ty) (body : Expr)  -- binder annotated with its domain
  | app (f a : Expr)
  deriving DecidableEq, Repr

/-- Typing context: the type of de Bruijn index `i` is `Γ[i]?`. -/
abbrev Ctx := List Ty

inductive HasType : Ctx → Expr → Ty → Prop where
  | var     {Γ i τ} : Γ[i]? = some τ → HasType Γ (.var i) τ
  | boolLit {Γ b}   : HasType Γ (.boolLit b) .bool
  | natLit  {Γ n}   : HasType Γ (.natLit n) .nat
  | lam     {Γ dom body cod} :
      HasType (dom :: Γ) body cod → HasType Γ (.lam dom body) (.arr dom cod)
  | app     {Γ f a dom cod} :
      HasType Γ f (.arr dom cod) → HasType Γ a dom → HasType Γ (.app f a) cod

/-- Syntax-directed type inference. -/
def infer : Ctx → Expr → Option Ty
  | Γ, .var i        => Γ[i]?
  | _, .boolLit _    => some .bool
  | _, .natLit _     => some .nat
  | Γ, .lam dom body => (infer (dom :: Γ) body).map (.arr dom)
  | Γ, .app f a      =>
    match infer Γ f, infer Γ a with
    | some (.arr dom cod), some dom' => if dom = dom' then some cod else none
    | _, _ => none

theorem infer_sound :
    ∀ {Γ : Ctx} {e : Expr} {τ : Ty}, infer Γ e = some τ → HasType Γ e τ
  | _, .var _, _, h => .var h
  | _, .boolLit _, _, h => by cases h; exact .boolLit
  | _, .natLit _, _, h => by cases h; exact .natLit
  | Γ, .lam dom body, τ, h => by
    cases hb : infer (dom :: Γ) body with
    | none => simp [infer, hb] at h
    | some cod =>
      simp [infer, hb] at h
      subst h
      exact .lam (infer_sound hb)
  | Γ, .app f a, τ, h => by
    cases hf : infer Γ f with
    | none => simp [infer, hf] at h
    | some τf =>
      cases ha : infer Γ a with
      | none => cases τf <;> simp [infer, hf, ha] at h
      | some τa =>
        cases τf with
        | bool => simp [infer, hf, ha] at h
        | nat => simp [infer, hf, ha] at h
        | arr dom cod =>
          simp [infer, hf, ha] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .app (infer_sound hf) (infer_sound ha)

theorem infer_complete {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : HasType Γ e τ) : infer Γ e = some τ := by
  induction h with
  | var h => exact h
  | boolLit => rfl
  | natLit => rfl
  | lam _ ih => simp [infer, ih]
  | app _ _ ihf iha => simp [infer, ihf, iha]

/-- Types are unique; used to show that changing a hole's `expectedType`
    invalidates any realization typed against the old one. -/
theorem HasType.unique {Γ : Ctx} {e : Expr} {τ₁ τ₂ : Ty}
    (h₁ : HasType Γ e τ₁) (h₂ : HasType Γ e τ₂) : τ₁ = τ₂ :=
  Option.some.inj ((infer_complete h₁).symm.trans (infer_complete h₂))

instance (Γ : Ctx) (e : Expr) (τ : Ty) : Decidable (HasType Γ e τ) :=
  decidable_of_iff (infer Γ e = some τ) ⟨infer_sound, infer_complete⟩

/-- Every type is inhabited by a closed term that uses no variables, and hence
    is well typed in *every* context.  (Avoids needing a weakening lemma.) -/
def Ty.canon : Ty → Expr
  | .bool => .boolLit true
  | .nat => .natLit 0
  | .arr a b => .lam a b.canon

theorem Ty.canon_hasType : ∀ (τ : Ty) (Γ : Ctx), HasType Γ τ.canon τ
  | .bool, _ => .boolLit
  | .nat, _ => .natLit
  | .arr a b, Γ => .lam (b.canon_hasType (a :: Γ))

end PersistentHole
