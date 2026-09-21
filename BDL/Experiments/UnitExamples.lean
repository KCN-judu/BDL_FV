import BDL.Surface.Affine
import BDL.Surface.Generic

/-!
# Phase 10 — unit coordinates and formula assembly: cases A–L, executed

Kernel-executable cases run through `evalF` over the `Nat` registry
(`Units.Reg`, canonical `0.1 mm`, `ms`, arc-second, `K/180`); the
radian case runs in the exact symbolic model (`Units.Sym`, π symbolic).
Nominal cases use `Tilt`, `MotorAngle` (both angles) and `Brightness`,
`Opacity` (both dimensionless).
-/

namespace BDL.Experiments.Units
open BDL BDL.Reactive BDL.Stdlib BDL.Units BDL.Composer BDL.Affine

def Tilt : ConceptId := ⟨60⟩
def MotorAngle : ConceptId := ⟨61⟩
def Brightness : ConceptId := ⟨62⟩
def Opacity : ConceptId := ⟨63⟩
def Θ : ConceptEnv := fun s =>
  if s = Tilt ∨ s = MotorAngle then some (.q Dim.Angle)
  else if s = Brightness ∨ s = Opacity then some (.q Dim.zero) else none

def tilt : DeclId := ⟨0⟩
def motor : DeclId := ⟨1⟩
def time : DeclId := ⟨2⟩
def bright : DeclId := ⟨3⟩
def normTilt : DeclId := ⟨4⟩   -- F: inUnit(tilt, deg) / 90
def normTilt' : DeclId := ⟨5⟩  -- F': tilt / 90 deg
def speed : DeclId := ⟨6⟩      -- E: 10 km / 5 min
def lens : DeclId := ⟨7⟩       -- list of lengths in mixed units
def pairD : DeclId := ⟨8⟩      -- (90 deg, 1 s)

def Δ : DeclEnv := .ofList [
  ⟨tilt, ⟨.sem Tilt, []⟩, none⟩,
  ⟨motor, ⟨.sem MotorAngle, []⟩, none⟩,
  ⟨time, ⟨.q Dim.Time, []⟩, none⟩,
  ⟨bright, ⟨.sem Brightness, []⟩, none⟩,
  ⟨normTilt, ⟨.q Dim.zero, []⟩, some (app2 (.prim (.div Dim.zero Dim.zero)) (inUnitE Reg.deg (.rep (.declRef tilt))) (.prim (.lit Dim.zero 90)))⟩,
  ⟨normTilt', ⟨.q Dim.zero, []⟩, some (app2 (.prim (.div Dim.Angle Dim.Angle)) (.rep (.declRef tilt)) (litE 90 Reg.deg))⟩,
  ⟨speed, ⟨.q (Dim.Length.sub Dim.Time), []⟩, some (app2 (.prim (.div Dim.Length Dim.Time)) (litE 10 Reg.km) (litE 5 Reg.min))⟩,
  ⟨lens, ⟨.list (.q Dim.Length), []⟩, some (listLit (.q Dim.Length) [litE 10 Reg.cm, litE 1 Reg.m])⟩,
  ⟨pairD, ⟨.prod (.q Dim.Angle) (.q Dim.Time), []⟩, some (pairE (.q Dim.Angle) (.q Dim.Time) (litE 90 Reg.deg) (litE 1 Reg.s))⟩]

def trivEv : Evidence := fun _ _ _ => True
instance : ∀ Δ e p, Decidable (trivEv Δ e p) := fun _ _ _ => inferInstanceAs (Decidable True)

theorem units_well_typed : GlobalWF trivEv Θ Δ := GlobalWF.ofList (by decide)

/-- Inputs: tilt 45°, motor 30°, time 2 s. -/
def I : Input := fun d _ =>
  if d = tilt then .sem Tilt (.nat (45 * 3600))
  else if d = motor then .sem MotorAngle (.nat (30 * 3600))
  else if d = time then .nat 2000 else .nat 0

def run (e : Expr) : Option Value := evalF Δ I 64 0 [] e
def runIs (e : Expr) (v : Value) : Bool := match run e with | some w => Value.beq w v | none => false

/-- **A — `1 m == 100 cm`**: same canonical magnitude, same type, and the
    kernel equality says so. -/
theorem exA : runIs (litE 1 Reg.m) (.nat 10000) ∧ runIs (litE 100 Reg.cm) (.nat 10000) ∧
    runIs (eqE (.q Dim.Length) trivial (litE 1 Reg.m) (litE 100 Reg.cm)) (.bool true) ∧
    infer Θ Δ Grant.none [] (litE 1 Reg.m) = infer Θ Δ Grant.none [] (litE 100 Reg.cm) := by decide

/-- **B — `25.4 mm == 1 inch`** (`254 × 0.1 mm`). -/
theorem exB : runIs (eqE (.q Dim.Length) trivial (litE 254 Reg.mm) (litE 10 Reg.inch)) (.bool true) ∧
    runIs (eqE (.q Dim.Length) trivial (litE 25 Reg.mm) (litE 1 Reg.inch)) (.bool false) ∧
    -- 25.4 mm is not a whole number of mm; the exact statement is at 0.1 mm resolution:
    litE 1 Reg.inch = .prim (.lit Dim.Length 254) ∧ Reg.mm.scale * 254 = Reg.inch.scale * 10 := by decide

/-- **C — 90° expressed in degrees is 90**; and the coordinate of the
    `Tilt` input (45°) in degrees is 45 — through `rep`. -/
theorem exC : runIs (inUnitE Reg.deg (litE 90 Reg.deg)) (.nat 90) ∧
    runIs (inUnitE Reg.deg (.rep (.declRef tilt))) (.nat 45) := by decide

/-- **D — the same angle in radians**, exactly: `90 deg = π/2 rad` in the
    symbolic model (`Sym`), where π is a generator.  The `Nat` kernel has no
    radian unit: `π/2` is not an integer in any degree-compatible basis. -/
theorem exD :
    inUnit symScalars (withUnit symScalars (Sym.ofExp 1 2 1) SymReg.deg) SymReg.rad = some ⟨-1, 0, 0, 0, 1⟩ ∧
    convert symScalars (Sym.ofExp 1 2 1) SymReg.deg SymReg.rad = some (Sym.div Sym.pi Sym.two) ∧
    -- and back: π/2 rad in degrees is 90 = 2·3²·5
    convert symScalars (Sym.div Sym.pi Sym.two) SymReg.rad SymReg.deg = some (Sym.ofExp 1 2 1) ∧
    ¬ ∃ u ∈ Reg.all, u.dim = Dim.Angle ∧ u.id = 10 := by decide

/-- **E — speed from mixed source units**: `10 km / 5 min` is `33.3 m/s`:
    `333` in the kernel's canonical `0.1 mm/ms` (floor); exactly `100/3` in `Sym`. -/
theorem exE : runIs (.declRef speed) (.nat 333) ∧
    infer Θ Δ Grant.none [] (.declRef speed) = some (.q ⟨1, -1, 0, 0, 0⟩) ∧
    (convert symScalars (Sym.ofExp 1 0 1) SymReg.km SymReg.m).map (fun l => Sym.div l (Sym.mul (Sym.ofExp 0 0 1) SymReg.min.scale))
      = some (Sym.ofExp 2 (-1) 2) := by decide

/-- **F — normalized tilt** `inUnit(tilt, deg) / 90` and `tilt / (90 deg)`
    are both dimensionless and evaluate equal (in `Nat`, `a / (s·90) =
    (a / s) / 90`); at 45° both give 0 (integer), the exact value being
    `1/2`. -/
theorem exF : infer Θ Δ Grant.none [] (.declRef normTilt) = some (.q Dim.zero) ∧
    infer Θ Δ Grant.none [] (.declRef normTilt') = some (.q Dim.zero) ∧
    runIs (.declRef normTilt) (.nat 0) ∧ runIs (.declRef normTilt') (.nat 0) := by decide

/-- The two normalizations agree for every tilt: `Nat.div_div_eq_div_mul`. -/
theorem normalizations_agree (a : Nat) : a / (Reg.deg.scale * 90) = a / Reg.deg.scale / 90 := by
  rw [Nat.div_div_eq_div_mul]

/-- **G — Composer**: `? / (1 s)` expected `Speed` ⇒ `? : Length`. -/
def Speed : Dim := Dim.Length.sub Dim.Time
theorem exG : solve (.div (.hole 0) (.known Dim.Time)) Speed = some [(0, Dim.Length)] ∧
    (candidates Reg.all (.div (.hole 0) (.known Dim.Time)) Speed 0).map (·.id) = [1, 2, 3, 4, 5] := by decide

/-- **H — Torque**: `Force × ?` expected `Torque` ⇒ `? : Length`. -/
def Force : Dim := ⟨1, -2, 0, 1, 0⟩
def Torque : Dim := ⟨2, -2, 0, 1, 0⟩
theorem exH : solve (.mul (.known Force) (.hole 0)) Torque = some [(0, Dim.Length)] ∧
    -- a two-hole product is reported unsolved, not guessed
    solve (.mul (.hole 0) (.hole 1)) Torque = none ∧
    -- an inconsistent known part is rejected
    solve (.add (.known Force) (.hole 0)) Torque = none := by decide

/-- **I — invalid: a time expressed in millimetres** is rejected by typing
    (`inUnitE_safe`): the unit's dimension must be the quantity's. -/
theorem exI : infer Θ Δ Grant.none [] (inUnitE Reg.mm (.declRef time)) = none ∧
    infer Θ Δ Grant.none [] (inUnitE Reg.s (.declRef time)) = some (.q Dim.zero) ∧
    infer Θ Δ Grant.none [] (withUnitE Reg.mm (.prim (.lit Dim.zero 10))) = some (.q Dim.Length) := by decide

/-- **J — a preferred-unit change leaves the core unchanged** (by
    construction, `presentation_irrelevant_*`) and changes the display: the
    tilt reads 45 in degrees and 162000 in arc-seconds. -/
def Pdeg : Presentation := ⟨fun _ => some Reg.deg⟩
def Parcsec : Presentation := ⟨fun _ => some ⟨13, Dim.Angle, 1⟩⟩
theorem exJ : display Pdeg Tilt (I tilt 0) = some 45 ∧ display Parcsec Tilt (I tilt 0) = some 162000 ∧
    (∀ e τ, HasType Θ (Presented.mk ⟨Δ, Θ, fun _ => none, fun _ => none, fun _ => none⟩ Pdeg).design.Δ Grant.none [] e τ ↔
      HasType Θ (Presented.mk ⟨Δ, Θ, fun _ => none, fun _ => none, fun _ => none⟩ Parcsec).design.Δ Grant.none [] e τ) := by
  refine ⟨by decide, by decide, fun _ _ => Iff.rfl⟩

/-- **K — °C is not a scale** (`celsius_not_linear`), executed: `0 °C` is
    `273 K`, `100 °C = 212 °F`. -/
theorem exK : toCanon celsius 0 ≠ 0 ∧ fromCanon kelvin (toCanon celsius 0) = 273 ∧ convert celsius fahrenheit 100 = 212 := by
  decide

/-- **L — absolute vs difference**: `20 °C − 10 °C = 10 K`; `10 °C + 10 °C`
    is well typed and reads `293 °C`. -/
theorem exL : toCanon celsius 20 - toCanon celsius 10 = toCanon kelvin 10 ∧
    fromCanon celsius (toCanon celsius 10 + toCanon celsius 10) = 293 ∧
    (affAdd .point .point = none) := by decide

/-! ## Nominal cases (§37): unit compatibility is not identity -/

/-- `Tilt` and `MotorAngle` can both be read in degrees, and stay distinct:
    the coordinate is a scalar, rebuilding a concept needs `mk` under its
    own grant, and no unit operation constructs anything. -/
theorem nominal_distinct :
    infer Θ Δ Grant.none [] (inUnitE Reg.deg (.rep (.declRef tilt))) = some (.q Dim.zero) ∧
    infer Θ Δ Grant.none [] (inUnitE Reg.deg (.rep (.declRef motor))) = some (.q Dim.zero) ∧
    -- a Tilt is not a MotorAngle, before or after a unit round trip
    infer Θ Δ Grant.none [] (.declRef tilt) ≠ infer Θ Δ Grant.none [] (.declRef motor) ∧
    infer Θ Δ Grant.none [] (withUnitE Reg.deg (inUnitE Reg.deg (.rep (.declRef tilt)))) = some (.q Dim.Angle) ∧
    -- without the grant, wrapping the coordinate as a MotorAngle is rejected
    infer Θ Δ Grant.none [] (.mk MotorAngle (withUnitE Reg.deg (inUnitE Reg.deg (.rep (.declRef tilt))))) = none ∧
    -- `inUnit` on a concept without `rep` is rejected: the discipline is not bypassed
    infer Θ Δ Grant.none [] (inUnitE Reg.deg (.declRef tilt)) = none := by decide

/-- Brightness and Opacity: both dimensionless, both displayable as
    percentages, still distinct. -/
def percent : NUnit := ⟨50, Dim.zero, 1⟩
theorem brightness_opacity_distinct :
    infer Θ Δ Grant.none [] (inUnitE percent (.rep (.declRef bright))) = some (.q Dim.zero) ∧
    infer Θ Δ Grant.none [] (.mk Opacity (withUnitE percent (inUnitE percent (.rep (.declRef bright))))) = none := by decide

/-! ## Generics (§38), ordering (§39), lists and products (§40) -/

/-- `min(10 cm, 1 m)` instantiates at the closed `q Length` after
    elaboration and picks `10 cm`; `clamp(angle, 0 deg, 90 deg)` at `q Angle`. -/
theorem generics_after_units :
    runIs (app2 (minF (.q Dim.Length)) (litE 10 Reg.cm) (litE 1 Reg.m)) (.nat 1000) ∧
    runIs (app3 (clampF (.q Dim.Angle)) (.rep (.declRef tilt)) (litE 0 Reg.deg) (litE 90 Reg.deg)) (.nat (45 * 3600)) ∧
    runIs (app3 (clampF (.q Dim.Angle)) (litE 120 Reg.deg) (litE 0 Reg.deg) (litE 90 Reg.deg)) (.nat (90 * 3600)) ∧
    -- mixed dimensions do not instantiate
    infer Θ Δ Grant.none [] (app2 (minF (.q Dim.Length)) (litE 10 Reg.cm) (litE 1 Reg.s)) = none := by decide

/-- Ordering of an ordered concept ignores presentation: the comparison is
    on canonical magnitudes, whatever the display unit. -/
theorem ordering_unit_independent :
    runIs (ltAt (Ordered.sem Tilt Dim.Angle) (.declRef tilt) (.declRef motor)) (.bool false) ∧
    display Pdeg Tilt (I tilt 0) = some 45 ∧ display Pdeg MotorAngle (I motor 0) = some 30 := by decide

/-- Lists and products of quantities keep their core types; units are gone. -/
theorem lists_products_core_types :
    infer Θ Δ Grant.none [] (.declRef lens) = some (.list (.q Dim.Length)) ∧
    infer Θ Δ Grant.none [] (.declRef pairD) = some (.prod (.q Dim.Angle) (.q Dim.Time)) ∧
    runIs (.declRef lens) (.list [.nat 1000, .nat 10000]) ∧
    runIs (.declRef pairD) (.pair (.nat 324000) (.nat 1000)) := by decide

/-! ## Composer explanation (§42): `Speed = [Length] / [Time]` -/

theorem speed_slot :
    (slot Reg.all (.div (.hole 0) (.known Dim.Time)) Speed 0).map (fun s => (s.expected, s.units.map (·.id)))
      = some (Dim.Length, [1, 2, 3, 4, 5]) ∧
    (slot Reg.all (.div (.known Dim.Length) (.hole 1)) Speed 1).map (fun s => (s.expected, s.units.map (·.id)))
      = some (Dim.Time, [20, 21, 22]) := by decide

end BDL.Experiments.Units
