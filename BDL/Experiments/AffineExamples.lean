import BDL.Surface.Charts
import BDL.Surface.Affine

/-!
# Phase 10b — affine charts, executed exactly

The chart theory (`Charts.lean`) instantiated at the exact rationals `Q`:
Celsius/Fahrenheit/Kelvin, a sensor calibration and an encoder offset.
Every number is exact (no `Nat` saturation, no floating point); each
example is a `Q` equality decided by cross-multiplication.
-/

namespace BDL.Experiments.Affine
open BDL.Rational BDL.Charts

abbrev F := ratField
def q (n : Int) : Q := Q.ofInt n
def r (n d : Int) (h : 0 < d := by decide) : Q := Q.frac n d h

/-! ## Temperature charts, kelvin canonical -/

/-- Kelvin: the canonical chart. -/
def kelvin : Chart Q := ⟨q 1, q 0⟩
/-- Celsius: `K = °C + 273.15`. -/
def celsius : Chart Q := ⟨q 1, r 27315 100⟩
/-- Fahrenheit: `K = 5/9 · °F + 45967/180` (`0 °F = 255.372… K`). -/
def fahrenheit : Chart Q := ⟨r 5 9, r 45967 180⟩

theorem charts_valid : kelvin.Valid F ∧ celsius.Valid F ∧ fahrenheit.Valid F := by
  refine ⟨?_, ?_, ?_⟩ <;> (intro h; have := Q.eqv_of_mk_eq h; simp [PreQ.Eqv, PreQ.ofInt] at this)

/-- **`C(Celsius, Fahrenheit)(x) = 9/5·x + 32`**, exactly and for every `x`. -/
theorem CtoF_closed (x : Q) : convert F celsius fahrenheit x = (AffMap.mk (r 9 5) (q 32)).apply F x := by
  rw [convert_is_affine]
  have h1 : (convertMap F celsius fahrenheit).a = r 9 5 := Q.mk_eq_of_decide (by decide)
  have h2 : (convertMap F celsius fahrenheit).b = q 32 := Q.mk_eq_of_decide (by decide)
  show (AffMap.mk (convertMap F celsius fahrenheit).a (convertMap F celsius fahrenheit).b).apply F x = _
  rw [h1, h2]

/-- **`C(Fahrenheit, Celsius)(x) = 5/9·(x − 32)`**, as `5/9·x + (−160/9)`. -/
theorem FtoC_closed (x : Q) : convert F fahrenheit celsius x = (AffMap.mk (r 5 9) (r (-160) 9)).apply F x := by
  rw [convert_is_affine]
  have h1 : (convertMap F fahrenheit celsius).a = r 5 9 := Q.mk_eq_of_decide (by decide)
  have h2 : (convertMap F fahrenheit celsius).b = r (-160) 9 := Q.mk_eq_of_decide (by decide)
  show (AffMap.mk (convertMap F fahrenheit celsius).a (convertMap F fahrenheit celsius).b).apply F x = _
  rw [h1, h2]

/-- **A, B, C**: `0 °C = 32 °F`, `100 °C = 212 °F`, `−40 °C = −40 °F`. -/
theorem exA : convert F celsius fahrenheit (q 0) = q 32 := Q.mk_eq_of_decide (by decide)
theorem exB : convert F celsius fahrenheit (q 100) = q 212 := Q.mk_eq_of_decide (by decide)
theorem exC : convert F celsius fahrenheit (q (-40)) = q (-40) := Q.mk_eq_of_decide (by decide)

/-- **D**: `°C → °F → °C` round trip (an instance of `convert_inverse`, and executed). -/
theorem exD : convert F fahrenheit celsius (convert F celsius fahrenheit (q 37)) = q 37 :=
  (convert_inverse F celsius fahrenheit charts_valid.2.1 charts_valid.2.2 (q 37)).1
theorem exD' : convert F fahrenheit celsius (q 212) = q 100 := Q.mk_eq_of_decide (by decide)

/-- **E**: `°C → K → °F` equals `°C → °F` (an instance of `convert_compose`, and executed). -/
theorem exE : convert F kelvin fahrenheit (convert F celsius kelvin (q 25)) = convert F celsius fahrenheit (q 25) :=
  convert_compose F celsius kelvin fahrenheit charts_valid.1 (q 25)
theorem exE' : convert F kelvin fahrenheit (convert F celsius kelvin (q 25)) = q 77 := Q.mk_eq_of_decide (by decide)

/-- **F**: a `10 °C` difference is an `18 °F` difference — the linear part is `9/5`. -/
theorem exF : F.sub (convert F celsius fahrenheit (q 30)) (convert F celsius fahrenheit (q 20)) = q 18 :=
  Q.mk_eq_of_decide (by decide)
theorem linear_part_CtoF : linearPart F celsius fahrenheit = r 9 5 := Q.mk_eq_of_decide (by decide)
theorem delta_law (x δ : Q) :
    F.sub (convert F celsius fahrenheit (F.add x δ)) (convert F celsius fahrenheit x) = F.mul (r 9 5) δ := by
  rw [difference_converts_linearly, linear_part_CtoF]
theorem delta_law_FtoC (x δ : Q) :
    F.sub (convert F fahrenheit celsius (F.add x δ)) (convert F fahrenheit celsius x) = F.mul (r 5 9) δ := by
  rw [difference_converts_linearly]
  have : linearPart F fahrenheit celsius = r 5 9 := Q.mk_eq_of_decide (by decide)
  rw [this]

/-- **G**: the same difference from another base point: `−5 °C → 5 °C` is also `18 °F`. -/
theorem exG : F.sub (convert F celsius fahrenheit (q 5)) (convert F celsius fahrenheit (q (-5))) = q 18 :=
  Q.mk_eq_of_decide (by decide)

/-- **Counterexample**: `C(°C,°F)` is not additive — `f(0+0) = 32`, `f(0)+f(0) = 64`. -/
theorem CtoF_not_additive :
    convert F celsius fahrenheit (F.add (q 0) (q 0)) ≠ F.add (convert F celsius fahrenheit (q 0)) (convert F celsius fahrenheit (q 0)) := by
  intro h
  rw [exA] at h
  have h0 : F.add (q 0) (q 0) = q 0 := Q.mk_eq_of_decide (by decide)
  rw [h0, exA] at h
  have := Q.eqv_of_mk_eq h
  simp [PreQ.Eqv, PreQ.ofInt, PreQ.add] at this

theorem CtoF_not_additive_general : ¬ ∀ x y, (convertMap F celsius fahrenheit).apply F (F.add x y)
    = F.add ((convertMap F celsius fahrenheit).apply F x) ((convertMap F celsius fahrenheit).apply F y) :=
  not_additive_of_offset F _ (by
    intro h
    have h2 : (convertMap F celsius fahrenheit).b = q 32 := Q.mk_eq_of_decide (by decide)
    rw [h2] at h
    have := Q.eqv_of_mk_eq h
    simp [PreQ.Eqv, PreQ.ofInt] at this)

/-! ## H — sensor calibration: `physical = a · raw + b` -/

/-- A 10-bit ADC over 5 V: `volts = 5/1023 · raw`. -/
def adcRaw : Chart Q := ⟨r 5 1023, q 0⟩
/-- Millivolts: `volts = mV / 1000`. -/
def millivolt : Chart Q := ⟨r 1 1000, q 0⟩
/-- A calibrated sensor reading in engineering units: `volts = reading/50 − 1/2`
    (a sensor whose 0 is at 0.5 V, 20 mV per unit). -/
def calibrated : Chart Q := ⟨r 1 50, r (-1) 2⟩

theorem adc_valid : adcRaw.Valid F ∧ millivolt.Valid F ∧ calibrated.Valid F := by
  refine ⟨?_, ?_, ?_⟩ <;> (intro h; have := Q.eqv_of_mk_eq h; simp [PreQ.Eqv, PreQ.ofInt] at this)

/-- Full scale is 5000 mV; raw `1023 → 5 V → 225 calibrated units`. -/
theorem exH : convert F adcRaw millivolt (q 1023) = q 5000 ∧
    convert F adcRaw calibrated (q 1023) = q 275 ∧
    -- composition through millivolts is the direct conversion
    convert F millivolt calibrated (convert F adcRaw millivolt (q 1023)) = convert F adcRaw calibrated (q 1023) ∧
    -- inverse: back to raw
    convert F calibrated adcRaw (convert F adcRaw calibrated (q 1023)) = q 1023 ∧
    -- a difference of 1023 counts is 5000 mV whatever the base point
    F.sub (convert F adcRaw millivolt (q 2046)) (convert F adcRaw millivolt (q 1023)) = q 5000 := by
  refine ⟨Q.mk_eq_of_decide (by decide), Q.mk_eq_of_decide (by decide),
    convert_compose F adcRaw millivolt calibrated adc_valid.2.1 _,
    (convert_inverse F adcRaw calibrated adc_valid.1 adc_valid.2.2 _).1, Q.mk_eq_of_decide (by decide)⟩

/-! ## I — encoder zero offset: `angle = k · count + home` -/

/-- Degrees, canonical. -/
def deg : Chart Q := ⟨q 1, q 0⟩
/-- A 4096-count encoder homed at 30°: `angle = 45/512 · count + 30`. -/
def encoder : Chart Q := ⟨r 45 512, q 30⟩

theorem exI : convert F encoder deg (q 0) = q 30 ∧ convert F encoder deg (q 4096) = q 390 ∧
    convert F deg encoder (q 30) = q 0 ∧ convert F deg encoder (q 120) = q 1024 ∧
    -- a difference of 1024 counts is 90°, from any home offset
    F.sub (convert F encoder deg (q 2048)) (convert F encoder deg (q 1024)) = q 90 ∧
    linearPart F encoder deg = r 45 512 := by
  refine ⟨Q.mk_eq_of_decide (by decide), Q.mk_eq_of_decide (by decide), Q.mk_eq_of_decide (by decide),
    Q.mk_eq_of_decide (by decide), Q.mk_eq_of_decide (by decide), Q.mk_eq_of_decide (by decide)⟩

/-! ## J — display-unit switch preserves the quantity; coordinate edit changes it -/

/-- `0 °C`, displayed in °F, reconstructs to the same kelvin quantity. -/
theorem exJ : reconstruct F fahrenheit (convert F celsius fahrenheit (coord F celsius (r 27315 100))) = r 27315 100 :=
  display_switch_preserves_quantity F celsius fahrenheit charts_valid.2.1 charts_valid.2.2 _
theorem exJ' : convert F celsius fahrenheit (coord F celsius (r 27315 100)) = q 32 := Q.mk_eq_of_decide (by decide)

/-- Editing `20 °C` to `21 °C` changes the quantity; switching `20 °C` to `68 °F` does not. -/
theorem edit_vs_switch :
    reconstruct F celsius (q 20) ≠ reconstruct F celsius (q 21) ∧
    reconstruct F fahrenheit (q 68) = reconstruct F celsius (q 20) := by
  refine ⟨coordinate_edit_changes_quantity F celsius charts_valid.2.1 ?_, Q.mk_eq_of_decide (by decide)⟩
  intro h
  have := Q.eqv_of_mk_eq h
  simp [PreQ.Eqv, PreQ.ofInt] at this

/-! ## The coordinate carries no chart -/

/-- The scalar `32` is a Fahrenheit coordinate of `0 °C` and a Celsius
    coordinate of `32 °C`: the number alone determines nothing; the chart
    given to `reconstruct` does. -/
theorem coordinate_needs_chart :
    reconstruct F fahrenheit (q 32) = reconstruct F celsius (q 0) ∧
    reconstruct F celsius (q 32) ≠ reconstruct F celsius (q 0) := by
  refine ⟨Q.mk_eq_of_decide (by decide), coordinate_edit_changes_quantity F celsius charts_valid.2.1 ?_⟩
  intro h
  have := Q.eqv_of_mk_eq h
  simp [PreQ.Eqv, PreQ.ofInt] at this

end BDL.Experiments.Affine
