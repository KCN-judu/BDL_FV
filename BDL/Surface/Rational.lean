/-!
# Rational — an exact scalar field, choice-free (Phase 10b)

Lean core's `Rat` proves its algebra with `Classical.choice`; this
development has kept that axiom out.  The affine unit theory needs an
exact field with negatives and fractions, so here is a small one: pairs
`num/den` with `den > 0`, quotiented by cross-multiplication.  Every
identity is an integer identity, proved by rewriting with the ring laws
of `Int` (no `ring`, no Mathlib), and concrete equalities are decided.
-/

namespace BDL.Rational

/-- A fraction with positive denominator. -/
structure PreQ where
  num : Int
  den : Int
  den_pos : 0 < den

namespace PreQ

def Eqv (a b : PreQ) : Prop := a.num * b.den = b.num * a.den

theorem Eqv.refl (a : PreQ) : Eqv a a := rfl
theorem Eqv.symm {a b : PreQ} (h : Eqv a b) : Eqv b a := Eq.symm h
theorem Eqv.trans {a b c : PreQ} (h₁ : Eqv a b) (h₂ : Eqv b c) : Eqv a c := by
  unfold Eqv at *
  have hb : b.den ≠ 0 := Int.ne_of_gt b.den_pos
  apply Int.eq_of_mul_eq_mul_right hb
  calc a.num * c.den * b.den = (a.num * b.den) * c.den := by
        rw [Int.mul_assoc, Int.mul_comm c.den, ← Int.mul_assoc]
    _ = (b.num * a.den) * c.den := by rw [h₁]
    _ = (b.num * c.den) * a.den := by
        rw [Int.mul_assoc, Int.mul_comm a.den, ← Int.mul_assoc]
    _ = (c.num * b.den) * a.den := by rw [h₂]
    _ = c.num * a.den * b.den := by
        rw [Int.mul_assoc, Int.mul_comm b.den, ← Int.mul_assoc]

instance : Decidable (Eqv a b) := inferInstanceAs (Decidable (_ = _))

def ofInt (n : Int) : PreQ := ⟨n, 1, Int.one_pos⟩
def add (a b : PreQ) : PreQ := ⟨a.num * b.den + b.num * a.den, a.den * b.den, Int.mul_pos a.den_pos b.den_pos⟩
def mul (a b : PreQ) : PreQ := ⟨a.num * b.num, a.den * b.den, Int.mul_pos a.den_pos b.den_pos⟩
def neg (a : PreQ) : PreQ := ⟨-a.num, a.den, a.den_pos⟩
/-- Inverse; `0⁻¹ = 0`. -/
def inv (a : PreQ) : PreQ :=
  if h : 0 < a.num then ⟨a.den, a.num, h⟩
  else if h' : a.num < 0 then ⟨-a.den, -a.num, Int.neg_pos_of_neg h'⟩
  else ⟨0, 1, Int.one_pos⟩

/-! ### The ring identities, in `Int` -/

theorem add_respects {a a' b b' : PreQ} (ha : Eqv a a') (hb : Eqv b b') : Eqv (add a b) (add a' b') := by
  unfold Eqv at *
  simp only [add]
  -- (a d + c b)(b' d') = (a' d' + c' b')(b d)   with a b' = a' b, c d' = c' d
  have e1 : a.num * b.den * (a'.den * b'.den) = (a.num * a'.den) * (b.den * b'.den) := by
    simp only [Int.mul_comm, Int.mul_left_comm]
  have e2 : b.num * a.den * (a'.den * b'.den) = (b.num * b'.den) * (a.den * a'.den) := by
    simp only [Int.mul_comm, Int.mul_left_comm]
  have e3 : a'.num * b'.den * (a.den * b.den) = (a'.num * a.den) * (b.den * b'.den) := by
    simp only [Int.mul_comm, Int.mul_left_comm]
  have e4 : b'.num * a'.den * (a.den * b.den) = (b'.num * b.den) * (a.den * a'.den) := by
    simp only [Int.mul_comm, Int.mul_left_comm]
  rw [Int.add_mul, Int.add_mul, e1, e2, e3, e4, ha, hb]

theorem mul_respects {a a' b b' : PreQ} (ha : Eqv a a') (hb : Eqv b b') : Eqv (mul a b) (mul a' b') := by
  unfold Eqv at *
  simp only [mul]
  calc a.num * b.num * (a'.den * b'.den) = (a.num * a'.den) * (b.num * b'.den) := by
        simp only [Int.mul_comm, Int.mul_left_comm]
    _ = (a'.num * a.den) * (b'.num * b.den) := by rw [ha, hb]
    _ = a'.num * b'.num * (a.den * b.den) := by
        simp only [Int.mul_comm, Int.mul_left_comm]

theorem neg_respects {a a' : PreQ} (ha : Eqv a a') : Eqv (neg a) (neg a') := by
  unfold Eqv at *
  simp only [neg, Int.neg_mul, ha]

theorem inv_respects {a a' : PreQ} (ha : Eqv a a') : Eqv (inv a) (inv a') := by
  unfold Eqv at *
  have hd := a.den_pos
  have hd' := a'.den_pos
  unfold inv
  -- the sign of the numerator is an invariant of the class
  have hsign : (0 < a.num ↔ 0 < a'.num) ∧ (a.num < 0 ↔ a'.num < 0) := by
    constructor
    · constructor
      · intro h
        have : 0 < a'.num * a.den := ha ▸ Int.mul_pos h hd'
        exact Int.pos_of_mul_pos_left this hd
      · intro h
        have : 0 < a.num * a'.den := ha.symm ▸ Int.mul_pos h hd
        exact Int.pos_of_mul_pos_left this hd'
    · constructor
      · intro h
        have : a'.num * a.den < 0 := ha ▸ Int.mul_neg_of_neg_of_pos h hd'
        exact Int.neg_of_mul_neg_left this hd
      · intro h
        have : a.num * a'.den < 0 := ha.symm ▸ Int.mul_neg_of_neg_of_pos h hd
        exact Int.neg_of_mul_neg_left this hd'
  by_cases h1 : 0 < a.num
  · have h1' : 0 < a'.num := hsign.1.mp h1
    simp only [h1, h1', ↓reduceDIte]
    calc a.den * a'.num = a'.num * a.den := Int.mul_comm _ _
      _ = a.num * a'.den := ha.symm
      _ = a'.den * a.num := Int.mul_comm _ _
  · have h1' : ¬ 0 < a'.num := fun h => h1 (hsign.1.mpr h)
    by_cases h2 : a.num < 0
    · have h2' : a'.num < 0 := hsign.2.mp h2
      simp only [h1, h1', h2, h2', ↓reduceDIte]
      calc -a.den * -a'.num = a'.num * a.den := by rw [Int.neg_mul_neg, Int.mul_comm]
        _ = a.num * a'.den := ha.symm
        _ = -a'.den * -a.num := by rw [Int.neg_mul_neg, Int.mul_comm]
    · have h2' : ¬ a'.num < 0 := fun h => h2 (hsign.2.mpr h)
      simp [h1, h1', h2, h2']

end PreQ

instance PreQ.setoid : Setoid PreQ := ⟨PreQ.Eqv, ⟨PreQ.Eqv.refl, PreQ.Eqv.symm, PreQ.Eqv.trans⟩⟩

/-- The exact rationals. -/
def Q := Quotient PreQ.setoid

namespace Q

def mk (a : PreQ) : Q := Quotient.mk _ a
def ofInt (n : Int) : Q := mk (PreQ.ofInt n)
/-- `n / d` for a positive denominator. -/
def frac (n : Int) (d : Int) (h : 0 < d) : Q := mk ⟨n, d, h⟩

def add : Q → Q → Q :=
  Quotient.lift (fun a => Quotient.lift (fun b => mk (PreQ.add a b))
      (fun _ _ hb => Quotient.sound (PreQ.add_respects (PreQ.Eqv.refl a) hb)))
    (fun _ _ ha => funext (Quotient.ind fun b => Quotient.sound (PreQ.add_respects ha (PreQ.Eqv.refl b))))
def mul : Q → Q → Q :=
  Quotient.lift (fun a => Quotient.lift (fun b => mk (PreQ.mul a b))
      (fun _ _ hb => Quotient.sound (PreQ.mul_respects (PreQ.Eqv.refl a) hb)))
    (fun _ _ ha => funext (Quotient.ind fun b => Quotient.sound (PreQ.mul_respects ha (PreQ.Eqv.refl b))))
def neg : Q → Q := Quotient.lift (fun a => mk (PreQ.neg a)) (fun _ _ h => Quotient.sound (PreQ.neg_respects h))
def inv : Q → Q := Quotient.lift (fun a => mk (PreQ.inv a)) (fun _ _ h => Quotient.sound (PreQ.inv_respects h))
def zero : Q := ofInt 0
def one : Q := ofInt 1
def sub (a b : Q) : Q := add a (neg b)
def div (a b : Q) : Q := mul a (inv b)

theorem mk_eq {a b : PreQ} (h : PreQ.Eqv a b) : mk a = mk b := Quotient.sound h
theorem eqv_of_mk_eq {a b : PreQ} (h : mk a = mk b) : PreQ.Eqv a b := Quotient.exact h

@[simp] theorem add_mk (a b : PreQ) : add (mk a) (mk b) = mk (PreQ.add a b) := rfl
@[simp] theorem mul_mk (a b : PreQ) : mul (mk a) (mk b) = mk (PreQ.mul a b) := rfl
@[simp] theorem neg_mk (a : PreQ) : neg (mk a) = mk (PreQ.neg a) := rfl
@[simp] theorem inv_mk (a : PreQ) : inv (mk a) = mk (PreQ.inv a) := rfl
theorem zero_def : zero = mk (PreQ.ofInt 0) := rfl
theorem one_def : one = mk (PreQ.ofInt 1) := rfl

/-- Equality of concrete rationals is the cross-multiplication identity —
    decidable by computation, which is how the examples are checked. -/
theorem mk_eq_of_decide {a b : PreQ} (h : decide (a.num * b.den = b.num * a.den) = true) : mk a = mk b :=
  Quotient.sound (show PreQ.Eqv a b from of_decide_eq_true h)

theorem ind {P : Q → Prop} (h : ∀ a : PreQ, P (mk a)) : ∀ q, P q := Quotient.ind h

/-! ### Field laws, by `Quot.ind` and integer identities -/

theorem add_comm (a b : Q) : add a b = add b a := by
  induction a using ind; induction b using ind
  simp only [add_mk]; apply mk_eq; unfold PreQ.Eqv PreQ.add
  simp only [Int.add_comm, Int.mul_comm]

theorem add_assoc (a b c : Q) : add (add a b) c = add a (add b c) := by
  induction a using ind; induction b using ind; induction c using ind
  simp only [add_mk]; apply mk_eq; unfold PreQ.Eqv PreQ.add
  simp only [Int.mul_add, Int.mul_comm, Int.mul_left_comm, Int.add_assoc, Int.add_comm]

theorem zero_add (a : Q) : add zero a = a := by
  induction a using ind
  simp only [zero_def, add_mk]; apply mk_eq; unfold PreQ.Eqv PreQ.add PreQ.ofInt
  simp

theorem add_neg (a : Q) : add a (neg a) = zero := by
  induction a using ind
  simp only [zero_def, add_mk, neg_mk]; apply mk_eq; unfold PreQ.Eqv PreQ.add PreQ.neg PreQ.ofInt
  simp [Int.neg_mul]
  exact Int.add_right_neg _

theorem mul_comm (a b : Q) : mul a b = mul b a := by
  induction a using ind; induction b using ind
  simp only [mul_mk]; apply mk_eq; unfold PreQ.Eqv PreQ.mul
  simp only [Int.mul_comm]

theorem mul_assoc (a b c : Q) : mul (mul a b) c = mul a (mul b c) := by
  induction a using ind; induction b using ind; induction c using ind
  simp only [mul_mk]; apply mk_eq; unfold PreQ.Eqv PreQ.mul
  simp only [Int.mul_assoc]

theorem one_mul (a : Q) : mul one a = a := by
  induction a using ind
  simp only [one_def, mul_mk]; apply mk_eq; unfold PreQ.Eqv PreQ.mul PreQ.ofInt
  simp

theorem mul_add (a b c : Q) : mul a (add b c) = add (mul a b) (mul a c) := by
  induction a using ind; induction b using ind; induction c using ind
  simp only [add_mk, mul_mk]; apply mk_eq; unfold PreQ.Eqv PreQ.add PreQ.mul
  simp only [Int.mul_add, Int.mul_comm, Int.mul_left_comm, Int.add_comm]

theorem mk_eq_zero_iff (a : PreQ) : mk a = zero ↔ a.num = 0 := by
  constructor
  · intro h
    have := eqv_of_mk_eq h
    unfold PreQ.Eqv PreQ.ofInt at this
    simpa using this
  · intro h; apply mk_eq; unfold PreQ.Eqv PreQ.ofInt; simp [h]

theorem mul_inv_cancel (a : Q) (h : a ≠ zero) : mul a (inv a) = one := by
  induction a using ind
  rename_i a
  have hn : a.num ≠ 0 := fun h0 => h ((mk_eq_zero_iff a).mpr h0)
  simp only [inv_mk, mul_mk, one_def]
  apply mk_eq
  unfold PreQ.Eqv PreQ.mul PreQ.inv PreQ.ofInt
  by_cases h1 : 0 < a.num
  · simp only [h1, ↓reduceDIte]
    simp [Int.mul_comm]
  · have h2 : a.num < 0 := by omega
    simp only [h1, h2, ↓reduceDIte]
    simp [Int.mul_neg, Int.mul_comm]

theorem zero_ne_one : zero ≠ one := by
  intro h
  have := eqv_of_mk_eq h
  unfold PreQ.Eqv PreQ.ofInt at this
  simp at this

/-- Decidable equality on `Q`: cross-multiplication. -/
instance : DecidableEq Q := fun a b =>
  Quotient.recOnSubsingleton₂ a b fun x y =>
    if h : PreQ.Eqv x y then isTrue (Quotient.sound h)
    else isFalse fun e => h (Quotient.exact e)

end Q
end BDL.Rational
