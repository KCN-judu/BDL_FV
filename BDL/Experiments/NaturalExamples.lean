import BDL.Surface.Natural
import BDL.Surface.Units

/-!
# Phase 11 — natural binder and range syntax, executed

Each natural form is desugared (`Natural.desugar`), compared with the
hand-written Phase-9 term, type-checked by `infer`, and run by `evalF`.
Nominal cases use `Tilt` and `MotorAngle` (both angles, both ordered) and
`Mode` (unordered).
-/

namespace BDL.Experiments.Natural
open BDL BDL.Reactive BDL.Stdlib BDL.Natural BDL.Units

def Tilt : ConceptId := ⟨70⟩
def MotorAngle : ConceptId := ⟨71⟩
def Mode : ConceptId := ⟨72⟩
def Θ : ConceptEnv := fun s =>
  if s = Tilt ∨ s = MotorAngle then some (.q Dim.Angle) else if s = Mode then some (.q Dim.zero) else none
def O : Poly.OrdDecl := fun s => s = Tilt ∨ s = MotorAngle
def Q0 : Ty := .q Dim.zero
def lit (n : Nat) : Expr := .prim (.lit Dim.zero n)

def xs : DeclId := ⟨0⟩       -- list Q0
def ys : DeclId := ⟨1⟩       -- list Q0
def rows : DeclId := ⟨2⟩     -- list (list Q0)
def tilts : DeclId := ⟨3⟩    -- list (sem Tilt)
def loT : DeclId := ⟨4⟩      -- sem Tilt bound
def hiT : DeclId := ⟨5⟩
def angle : DeclId := ⟨6⟩    -- q Angle
def mode1 : DeclId := ⟨7⟩    -- sem Mode
def opt1 : DeclId := ⟨8⟩     -- opt Q0
def readings : DeclId := ⟨9⟩ -- list (q Angle)

def Δ : DeclEnv := .ofList [
  ⟨xs, ⟨.list Q0, []⟩, none⟩, ⟨ys, ⟨.list Q0, []⟩, none⟩, ⟨rows, ⟨.list (.list Q0), []⟩, none⟩,
  ⟨tilts, ⟨.list (.sem Tilt), []⟩, none⟩, ⟨loT, ⟨.sem Tilt, []⟩, none⟩, ⟨hiT, ⟨.sem Tilt, []⟩, none⟩,
  ⟨angle, ⟨.q Dim.Angle, []⟩, none⟩, ⟨mode1, ⟨.sem Mode, []⟩, none⟩, ⟨opt1, ⟨.opt Q0, []⟩, none⟩,
  ⟨readings, ⟨.list (.q Dim.Angle), []⟩, none⟩]

def mkI (xv yv : List Nat) (rv : List (List Nat)) (ang : Nat) (o : Option Nat) : Input := fun d _ =>
  if d = xs then .list (xv.map .nat) else if d = ys then .list (yv.map .nat)
  else if d = rows then .list (rv.map fun r => .list (r.map .nat))
  else if d = tilts then .list [.sem Tilt (.nat 10), .sem Tilt (.nat 20)]
  else if d = loT then .sem Tilt (.nat 5) else if d = hiT then .sem Tilt (.nat 30)
  else if d = angle then .nat ang
  else if d = mode1 then .sem Mode (.nat 1)
  else if d = opt1 then (match o with | some n => .some (.nat n) | none => .none)
  else if d = readings then .list [.nat (10 * 3600), .nat (40 * 3600)]
  else .nat 0

def I₁ : Input := mkI [1, 2, 3] [10] [[1, 0], [2, 3]] (30 * 3600) (some 7)
def I₂ : Input := mkI [0, 1] [10] [[0, 0], [1]] (60 * 3600) none

def runIs (I : Input) (e : Expr) (v : Value) : Bool :=
  match evalF Δ I 64 0 [] e with | some w => Value.beq w v | none => false
def ty (e : Expr) : Option Ty := infer Θ Δ Grant.none [] e

/-- Surface helpers: `x > 0` and `x > y` for locals. -/
def gt0 (x : Name) : NatExpr := .app (.app (.core (.prim (.lt Dim.zero))) (.core (lit 0))) (.local x)
def gtN (x : Name) (n : Nat) : NatExpr := .app (.app (.core (.prim (.lt Dim.zero))) (.core (lit n))) (.local x)
def ref (d : DeclId) : NatExpr := .core (.declRef d)

/-! ## A — `all x in xs: x > 0` is the library call, and means `∀` -/

def allNat : NatExpr := .binder .all Q0 "x" (ref xs) (gt0 "x")
def allCore : Expr := app2 (allF Q0) (.lam Q0 (ltE Dim.zero (lit 0) (.var 0))) (.declRef xs)

theorem exA : desugar [] allNat = some allCore ∧ ty allCore = some .bool ∧
    runIs I₁ allCore (.bool true) ∧ runIs I₂ allCore (.bool false) := by decide

/-- `any x in xs: x > 2`. -/
def anyNat : NatExpr := .binder .any Q0 "x" (ref xs) (gtN "x" 2)
theorem exA' : (desugar [] anyNat).map (runIs I₁ · (.bool true)) = some true ∧
    (desugar [] anyNat).map (runIs I₂ · (.bool false)) = some true := by decide

/-! ## B — `map x in xs: x + 5` -/

def mapNat : NatExpr := .binder (.map Q0) Q0 "x" (ref xs)
  (.app (.app (.core (.prim (.add Dim.zero))) (.local "x")) (.core (lit 5)))
def mapCore : Expr := app2 (mapF Q0 Q0) (.lam Q0 (app2 (.prim (.add Dim.zero)) (.var 0) (lit 5))) (.declRef xs)

theorem exB : desugar [] mapNat = some mapCore ∧ ty mapCore = some (.list Q0) ∧
    runIs I₁ mapCore (.list [.nat 6, .nat 7, .nat 8]) := by decide

/-- `filter x in xs: x > 1`. -/
def filterNat : NatExpr := .binder .filter Q0 "x" (ref xs) (gtN "x" 1)
theorem exB' : (desugar [] filterNat).map (ty ·) = some (some (.list Q0)) ∧
    (desugar [] filterNat).map (runIs I₁ · (.list [.nat 2, .nat 3])) = some true := by decide

/-! ## C — `angle in 10 deg .. 45 deg`, units first -/

def rangeNat : NatExpr := .range (.q Dim.Angle) (ref angle) (.core (litE 10 Reg.deg)) (.core (litE 45 Reg.deg))
def rangeCore : Expr := app3 (inRangeF (.q Dim.Angle)) (.declRef angle) (litE 10 Reg.deg) (litE 45 Reg.deg)

theorem exC : desugar [] rangeNat = some rangeCore ∧ ty rangeCore = some .bool ∧
    runIs I₁ rangeCore (.bool true) ∧ runIs I₂ rangeCore (.bool false) := by decide

/-- The range is `lo ≤ x ∧ x ≤ hi`, at the bounds too. -/
theorem exC' : ∀ n ∈ [9, 10, 11, 44, 45, 46],
    runIs (mkI [] [] [] (n * 3600) none) rangeCore (.bool (decide (10 ≤ n ∧ n ≤ 45))) := by decide

/-- The principle: `all reading in readings: reading in 10 deg .. 45 deg`. -/
def allReadings : NatExpr := .binder .all (.q Dim.Angle) "reading" (ref readings)
  (.range (.q Dim.Angle) (.local "reading") (.core (litE 10 Reg.deg)) (.core (litE 45 Reg.deg)))
theorem exC'' : (desugar [] allReadings).map (ty ·) = some (some .bool) ∧
    (desugar [] allReadings).map (runIs I₁ · (.bool true)) = some true := by decide

/-! ## D — nested binders: `all row in rows: any v in row: v > 0` -/

def nested : NatExpr := .binder .all (.list Q0) "row" (ref rows) (.binder .any Q0 "v" (.local "row") (gt0 "v"))
theorem exD : (desugar [] nested).map (ty ·) = some (some .bool) ∧
    (desugar [] nested).map (runIs I₁ · (.bool true)) = some true ∧
    (desugar [] nested).map (runIs I₂ · (.bool false)) = some true := by decide

/-! ## E — shadowing: the nearest binder wins -/

/-- `all x in xs: any x in ys: x > 5` — the inner `x` ranges over `ys`
    (`[10]`), so this is true although every element of `xs` is `≤ 5`. -/
def shadow : NatExpr := .binder .all Q0 "x" (ref xs) (.binder .any Q0 "x" (ref ys) (gtN "x" 5))
def shadowCore : Expr :=
  app2 (allF Q0) (.lam Q0 (app2 (anyF Q0) (.lam Q0 (ltE Dim.zero (lit 5) (.var 0))) (.declRef ys))) (.declRef xs)
theorem exE : desugar [] shadow = some shadowCore ∧ runIs I₂ shadowCore (.bool true) := by decide

/-- `all x in xs: any y in ys: x > y` refers to both: false (no x in `[0,1]` exceeds 10). -/
def twoBinders : NatExpr := .binder .all Q0 "x" (ref xs) (.binder .any Q0 "y" (ref ys)
  (.app (.app (.core (.prim (.lt Dim.zero))) (.local "y")) (.local "x")))
theorem exE' : desugar [] twoBinders = some (app2 (allF Q0) (.lam Q0 (app2 (anyF Q0)
    (.lam Q0 (ltE Dim.zero (.var 0) (.var 1))) (.declRef ys))) (.declRef xs)) ∧
    (desugar [] twoBinders).map (runIs I₂ · (.bool false)) = some true := by decide

/-! ## F — alpha-equivalence -/

theorem exF : desugar [] (.binder .all Q0 "y" (ref xs) (gt0 "y")) = desugar [] allNat ∧
    desugar [] (allNat.rename "x" "reading") = desugar [] allNat ∧
    desugar [] (shadow.rename "x" "z") = desugar [] shadow := by
  refine ⟨rfl, alpha "x" "reading" allNat (by decide), alpha "x" "z" shadow (by decide)⟩

/-! ## G — nominal element types -/

/-- `all t in tilts: t in loT .. hiT` — the local is a `Tilt`, the bounds
    are `Tilt`s: accepted; with `q Angle` bounds: rejected; through `rep`
    against `q Angle` bounds: accepted. -/
def oT : Ordered (.sem Tilt) := .sem Tilt Dim.Angle
def tiltRange : NatExpr := .binder .all (.sem Tilt) "t" (ref tilts) (.range oT (.local "t") (ref loT) (ref hiT))
def tiltRangeBad : NatExpr := .binder .all (.sem Tilt) "t" (ref tilts)
  (.range oT (.local "t") (.core (litE 10 Reg.deg)) (.core (litE 45 Reg.deg)))
def tiltRangeRep : NatExpr := .binder .all (.sem Tilt) "t" (ref tilts)
  (.range (.q Dim.Angle) (.app (.core (.lam (.sem Tilt) (.rep (.var 0)))) (.local "t"))
    (.core (litE 0 Reg.deg)) (.core (litE 45 Reg.deg)))

theorem exG : (desugar [] tiltRange).map (ty ·) = some (some .bool) ∧
    (desugar [] tiltRange).map (runIs I₁ · (.bool true)) = some true ∧
    (desugar [] tiltRangeBad).map (ty ·) = some none ∧
    (desugar [] tiltRangeRep).map (ty ·) = some (some .bool) := by decide

/-- A predicate on `MotorAngle` cannot take the `Tilt` local, though both are angles. -/
def motorPred : Expr := .lam (.sem MotorAngle) (.boolLit true)
def tiltPred : Expr := .lam (.sem Tilt) (.boolLit true)
theorem nominal_slot :
    (desugar [] (.binder .all (.sem Tilt) "t" (ref tilts) (.app (.core motorPred) (.local "t")))).map (ty ·) = some none ∧
    (desugar [] (.binder .all (.sem Tilt) "t" (ref tilts) (.app (.core tiltPred) (.local "t")))).map (ty ·)
      = some (some .bool) := by decide

/-- The binder local's type is forced by the collection (`binder_local_type`),
    executed: the same body under a `q Angle` binder over `tilts` is rejected. -/
theorem local_type_forced :
    (desugar [] (.binder .all (.q Dim.Angle) "t" (ref tilts) (.core (.boolLit true)))).map (ty ·) = some none := by
  decide

/-! ## H — negative examples -/

theorem negatives :
    -- `all x in 5: true`: the collection is not a list
    (desugar [] (.binder .all Q0 "x" (.core (lit 5)) (.core (.boolLit true)))).map (ty ·) = some none ∧
    -- `filter x in xs: 5`: the body is not a bool
    (desugar [] (.binder .filter Q0 "x" (ref xs) (.core (lit 5)))).map (ty ·) = some none ∧
    -- `angle in 2 s .. 3 s`: bounds of another dimension
    (desugar [] (.range (.q Dim.Angle) (ref angle) (.core (litE 2 Reg.s)) (.core (litE 3 Reg.s)))).map (ty ·) = some none ∧
    -- an unordered concept has no order: the surface policy rejects the range
    Poly.Ty.ordB O Θ (.sem Mode) = false ∧
    -- a binder variable outside its body is not a surface variable at all
    desugar [] (.local "x") = none ∧
    desugar [] (.binder .all Q0 "x" (ref xs) (gt0 "y")) = none := by decide

/-! ## I — coalesce `x ?? 0` -/

theorem exI : desugar [] (.coalesce Q0 (ref opt1) (.core (lit 0))) = some (app2 (getOrElseF Q0) (.declRef opt1) (lit 0)) ∧
    runIs I₁ (app2 (getOrElseF Q0) (.declRef opt1) (lit 0)) (.nat 7) ∧
    runIs I₂ (app2 (getOrElseF Q0) (.declRef opt1) (lit 0)) (.nat 0) := by decide

/-! ## J — no construction -/

theorem no_construction (s : ConceptId) : ∀ e', desugar [] allReadings = some e' → ¬ e'.constructs s :=
  fun _ h => desugar_constructs s allReadings [] h ⟨id, ⟨trivial, id, id⟩⟩

end BDL.Experiments.Natural
