import BDL.Surface.Composer

/-!
# Affine — where the linear unit model stops (Phase 10, §25–29)

Temperature scales are affine: `canonical = scale × x + offset`.  This
module shows, executably:

* the linear model cannot represent °C or °F (`celsius_not_linear`);
* an affine *literal* and an affine *coordinate* elaborate exactly and
  round-trip, with no kernel change — the offset is a subtraction of a
  constant in the kernel's own arithmetic (`affine_roundtrip`,
  `affLitE_typed`, `affInUnitE_typed`);
* what an affine unit breaks is not conversion but **arithmetic on
  absolute values**: `20 °C − 10 °C` is a difference of `10 K`
  (`delta_is_linear`), while `10 °C + 10 °C`, well typed at `q Temp`, is
  `303.15 °C`, not `20 °C` (`sum_of_points_is_not_a_point`).  The kernel's
  `q Temp` cannot tell an absolute temperature from a difference;
* the missing information is a *sort* — point or difference — on top of
  the dimension (`AffSort`), and the Formula Composer cannot choose
  between `K`, `°C` and `°F` for a delta slot from the dimension alone
  (`delta_candidates_need_sort`).

Verdict: affine **conversion** is safe surface elaboration now; affine
**arithmetic safety** needs the point/difference sort and is deferred.
The canonical basis is `K/180`, so that °C and °F have integer scales
and offsets: `1 K = 180`, `1 °F = 100`, `0 °C = 49167`, `0 °F = 45967`.
-/

namespace BDL.Affine
open BDL BDL.Reactive BDL.Stdlib BDL.Units BDL.Composer

/-- An affine unit: `canonical = x × scale + offset` in the `K/180` basis. -/
structure AffineUnit where
  id : Nat
  dim : Dim
  scale : Nat
  offset : Nat
  deriving DecidableEq, Repr

def kelvin : AffineUnit := ⟨40, Dim.Temp, 180, 0⟩
/-- `0 °C = 273.15 K = 49167 (K/180)` -/
def celsius : AffineUnit := ⟨41, Dim.Temp, 180, 49167⟩
/-- `1 °F = 5/9 K = 100 (K/180)`; `0 °F = 459.67/1.8 K = 45967 (K/180)` -/
def fahrenheit : AffineUnit := ⟨42, Dim.Temp, 100, 45967⟩
def reg : List AffineUnit := [kelvin, celsius, fahrenheit]

def toCanon (u : AffineUnit) (x : Nat) : Nat := x * u.scale + u.offset
def fromCanon (u : AffineUnit) (c : Nat) : Nat := (c - u.offset) / u.scale

/-- **K — the counterexample to scale-only units**: `0 °C` is `273.15 K`,
    which no scale factor produces from `0`; and the same for °F. -/
theorem celsius_not_linear : (¬ ∃ s : Nat, ∀ x, toCanon celsius x = x * s) ∧ (¬ ∃ s : Nat, ∀ x, toCanon fahrenheit x = x * s) := by
  constructor <;> (rintro ⟨s, h⟩; have := h 0; simp [toCanon, celsius, fahrenheit] at this)

/-- The scales agree where they should: `0 °C = 32 °F`, `100 °C = 212 °F = 373.15 K`. -/
theorem scales_agree :
    toCanon celsius 0 = toCanon fahrenheit 32 ∧ toCanon celsius 100 = toCanon fahrenheit 212 ∧
    toCanon celsius 100 = 67167 ∧ fromCanon kelvin (toCanon celsius 0) = 273 := by decide

/-- **Affine round trip** (exact in `Nat`, scale positive). -/
theorem affine_roundtrip (u : AffineUnit) (hs : 0 < u.scale) (x : Nat) : fromCanon u (toCanon u x) = x := by
  simp [fromCanon, toCanon, Nat.add_sub_cancel, Nat.mul_div_cancel _ hs]

/-- Affine conversion between scales is derived exactly as in the linear
    case: through the canonical magnitude. -/
def convert (u v : AffineUnit) (x : Nat) : Nat := fromCanon v (toCanon u x)
theorem convert_examples : convert celsius fahrenheit 100 = 212 ∧ convert fahrenheit celsius 212 = 100 ∧
    convert celsius kelvin 0 = 273 := by decide

/-! ## Elaboration without a kernel change -/

/-- An affine literal `n u`: the canonical magnitude, as a literal. -/
def affLitE (n : Nat) (u : AffineUnit) : Expr := .prim (.lit u.dim (toCanon u n))
/-- An affine coordinate: `(q − offset) / scale`, kernel subtraction and division. -/
def affInUnitE (u : AffineUnit) (q : Expr) : Expr :=
  app2 (.prim (.div u.dim u.dim)) (app2 (.prim (.sub u.dim)) q (.prim (.lit u.dim u.offset))) (.prim (.lit u.dim u.scale))

section Typing
variable {Θ : ConceptEnv} {Δ : DeclEnv} {G : Grant} {Γ : Ctx}
theorem affLitE_typed (n : Nat) (u : AffineUnit) : HasType Θ Δ G Γ (affLitE n u) (.q u.dim) := .prim
theorem affInUnitE_typed (u : AffineUnit) {q : Expr} (hq : HasType Θ Δ G Γ q (.q u.dim)) :
    HasType Θ Δ G Γ (affInUnitE u q) (.q Dim.zero) := by
  have h : HasType Θ Δ G Γ (affInUnitE u q) (.q (u.dim.sub u.dim)) := .app (.app .prim (.app (.app .prim hq) .prim)) .prim
  rwa [Dim.sub_self] at h
end Typing

section Eval
variable {Δ : DeclEnv} {I : Input} {t : Nat} {ρ : List Value}
theorem ev_affInUnitE (u : AffineUnit) {q : Expr} {m : Nat} (hq : Ev Δ I t ρ q (.nat m)) :
    Ev Δ I t ρ (affInUnitE u q) (.nat (fromCanon u m)) := by
  have h1 := Ev.appPrim (Ev.appPrim (Ev.prim (p := .sub u.dim)) hq) (Ev.lit u.dim u.offset)
  have h2 := Ev.appPrim (Ev.appPrim (Ev.prim (p := .div u.dim u.dim))
    (by simpa [app2, applyPrim, Prim.arity, Prim.compute] using h1)) (Ev.lit u.dim u.scale)
  simpa [affInUnitE, app2, applyPrim, Prim.arity, Prim.compute, fromCanon] using h2

/-- The affine literal read back in its unit is the coordinate written. -/
theorem affine_roundtrip_ev (u : AffineUnit) (hs : 0 < u.scale) (n : Nat) :
    Ev Δ I t ρ (affInUnitE u (affLitE n u)) (.nat n) := by
  have := ev_affInUnitE (Δ := Δ) (I := I) (t := t) (ρ := ρ) u (q := affLitE n u) (m := toCanon u n) (Ev.lit _ _)
  rwa [affine_roundtrip u hs] at this
end Eval

/-! ## L — absolute temperatures and differences -/

/-- A difference of two absolute temperatures is a *linear* quantity: the
    offsets cancel, `20 °C − 10 °C = 10 K`. -/
theorem delta_is_linear (a b : Nat) (h : b ≤ a) :
    toCanon celsius a - toCanon celsius b = (a - b) * 180 ∧ toCanon celsius 20 - toCanon celsius 10 = toCanon kelvin 10 := by
  refine ⟨?_, by decide⟩
  simp only [toCanon, celsius]
  omega

/-- **The sum of two absolute temperatures is not an absolute temperature
    the designer means**: `10 °C + 10 °C`, computed on canonical
    magnitudes, reads back as `293 °C`, not `20 °C` — yet it is well typed
    at `q Temp`.  The kernel's dimension cannot express the point/difference
    distinction. -/
theorem sum_of_points_is_not_a_point :
    fromCanon celsius (toCanon celsius 10 + toCanon celsius 10) = 293 ∧
    fromCanon celsius (toCanon celsius 10 + toCanon celsius 10) ≠ 20 := by decide

theorem sum_well_typed {Θ : ConceptEnv} {Δ : DeclEnv} {G : Grant} :
    HasType Θ Δ G [] (app2 (.prim (.add Dim.Temp)) (affLitE 10 celsius) (affLitE 10 celsius)) (.q Dim.Temp) :=
  .app (.app .prim .prim) .prim

/-- The sort an affine dimension needs beside `Dim`: a point on the scale,
    or a difference. -/
inductive AffSort where
  | point
  | delta
  deriving DecidableEq, Repr

/-- The arithmetic of an affine space: points and differences. -/
def affAdd : AffSort → AffSort → Option AffSort
  | .point, .delta => some .point
  | .delta, .point => some .point
  | .delta, .delta => some .delta
  | .point, .point => none
def affSub : AffSort → AffSort → Option AffSort
  | .point, .point => some .delta
  | .point, .delta => some .point
  | .delta, .delta => some .delta
  | .delta, .point => none

/-- With the sort, the meaningless sum is rejected and the meaningful
    difference accepted — a surface check the kernel does not perform. -/
theorem sort_decides : affAdd .point .point = none ∧ affSub .point .point = some .delta ∧
    affAdd .point .delta = some .point := by decide

/-- **Formula Composer and affine units**: from the dimension alone a
    `Temperature` slot and a `TemperatureDelta` slot get the same
    candidates (`K`, `°C`, `°F`); the sort is the extra information the
    editor needs to offer only difference units for a delta. -/
def affUnitsFor (d : Dim) : List AffineUnit := reg.filter (·.dim = d)
theorem delta_candidates_need_sort :
    affUnitsFor Dim.Temp = [kelvin, celsius, fahrenheit] ∧
    (affUnitsFor Dim.Temp).filter (·.offset = 0) = [kelvin] := by decide

end BDL.Affine
