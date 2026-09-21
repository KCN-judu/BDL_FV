import BDL.Surface.Generic

/-!
# Phase 9b — the expressiveness cases A–L, executed

Each case is a small design written with the definitional library
(`Stdlib.lean`) over the kernel, type-checked by `infer` and run by the
proved-sound interpreter `evalF`; results are checked with `decide`
through the structural equality `Value.beq` (`Value.eq_of_beq` makes a
`true` answer real equality).  Rejections (I, J) are `infer = none`.
-/

namespace BDL.Experiments.Equations
open BDL BDL.Reactive BDL.Stdlib BDL.Generic

def Brightness : ConceptId := ⟨50⟩
def Opacity : ConceptId := ⟨51⟩
def Mode : ConceptId := ⟨52⟩
def Q0 : Ty := .q Dim.zero
def B : Ty := .sem Brightness
/-- Brightness is an ordered concept (Phase 9c evidence); Mode is not. -/
def oB : Ordered B := .sem Brightness Dim.zero
def O : Poly.OrdDecl := fun s => s = Brightness ∨ s = Opacity
def lit (n : Nat) : Expr := litE Dim.zero n
def trivEv : Evidence := fun _ _ _ => True
instance : ∀ Δ e p, Decidable (trivEv Δ e p) := fun _ _ _ => inferInstanceAs (Decidable True)

/-- All three concepts are represented by `q 0`: same representation, distinct identity. -/
def Θ : ConceptEnv := fun s => if s = Brightness ∨ s = Opacity ∨ s = Mode then some Q0 else none

/-! ## Declarations -/

def bIn : DeclId := ⟨0⟩       -- Brightness input
def bMin : DeclId := ⟨1⟩      -- Brightness 10 (constructed under its own grant)
def bMax : DeclId := ⟨2⟩      -- Brightness 90
def bOut : DeclId := ⟨3⟩      -- A: clamp
def mode : DeclId := ⟨4⟩      -- q 0 input
def isAuto : DeclId := ⟨5⟩    -- B: mode ∈ {1, 2}
def temps : DeclId := ⟨6⟩     -- list (q 0) input
def allBelow : DeclId := ⟨7⟩  -- C: every temperature below 30
def faults : DeclId := ⟨8⟩    -- list (q 0) input (severities)
def anyHigh : DeclId := ⟨9⟩   -- D: any severity above 2
def hum : DeclId := ⟨10⟩      -- q 0 input
def th : DeclId := ⟨11⟩       -- E: (temperature, humidity)
def thT : DeclId := ⟨12⟩      -- E: fst
def calibrated : DeclId := ⟨13⟩ -- F: map (+ 5) temps
def ys : DeclId := ⟨14⟩       -- G: second sampled collection (input)
def zipped : DeclId := ⟨15⟩   -- G: zip temps ys
def firstOr : DeclId := ⟨16⟩  -- H: head temps or 0
def inRng : DeclId := ⟨17⟩    -- K: hum ∈ [30, 60]
def level : DeclId := ⟨18⟩    -- L: piecewise rule
def oIn : DeclId := ⟨19⟩      -- Opacity input (for J)
def lenIn : DeclId := ⟨20⟩    -- q Length input (for I)
def timeIn : DeclId := ⟨21⟩   -- q Time input (for I)
def temp : DeclId := ⟨22⟩     -- q 0 input
def mode1 : DeclId := ⟨23⟩    -- sem Mode input (for the capability audit)
def mode2 : DeclId := ⟨24⟩

def thr : Expr := lit 30
def sev : Expr := lit 2

def decls : List DesignDecl := [
  ⟨bIn, ⟨B, []⟩, none⟩,
  ⟨bMin, ⟨B, []⟩, some (.mk Brightness (lit 10))⟩,
  ⟨bMax, ⟨B, []⟩, some (.mk Brightness (lit 90))⟩,
  ⟨bOut, ⟨B, []⟩, some (app3 (clampF oB) (.declRef bIn) (.declRef bMin) (.declRef bMax))⟩,
  ⟨mode, ⟨Q0, []⟩, none⟩,
  ⟨isAuto, ⟨.bool, []⟩, some (oneOfE Q0 trivial (.declRef mode) [lit 1, lit 2])⟩,
  ⟨temps, ⟨.list Q0, []⟩, none⟩,
  ⟨allBelow, ⟨.bool, []⟩, some (app2 (allF Q0) (.lam Q0 (ltE Dim.zero (.var 0) thr)) (.declRef temps))⟩,
  ⟨faults, ⟨.list Q0, []⟩, none⟩,
  ⟨anyHigh, ⟨.bool, []⟩, some (app2 (anyF Q0) (.lam Q0 (ltE Dim.zero sev (.var 0))) (.declRef faults))⟩,
  ⟨hum, ⟨Q0, []⟩, none⟩,
  ⟨temp, ⟨Q0, []⟩, none⟩,
  ⟨th, ⟨.prod Q0 Q0, []⟩, some (pairE Q0 Q0 (.declRef temp) (.declRef hum))⟩,
  ⟨thT, ⟨Q0, []⟩, some (fstE Q0 Q0 (.declRef th))⟩,
  ⟨calibrated, ⟨.list Q0, []⟩,
    some (app2 (mapF Q0 Q0) (.lam Q0 (app2 (.prim (.add Dim.zero)) (.var 0) (lit 5))) (.declRef temps))⟩,
  ⟨ys, ⟨.list Q0, []⟩, none⟩,
  ⟨zipped, ⟨.list (.prod Q0 Q0), []⟩, some (app2 (zipF Q0 Q0) (.declRef temps) (.declRef ys))⟩,
  ⟨firstOr, ⟨Q0, []⟩, some (app2 (getOrElseF Q0) (.app (.prim (.head Q0)) (.declRef temps)) (lit 0))⟩,
  ⟨inRng, ⟨.bool, []⟩, some (app3 (inRangeF (.q Dim.zero)) (.declRef hum) (lit 30) (lit 60))⟩,
  ⟨level, ⟨Q0, []⟩, some (iteE Q0 (andE (.declRef inRng) (.declRef allBelow)) (lit 1)
    (iteE Q0 (.declRef anyHigh) (lit 2) (lit 0)))⟩,
  ⟨oIn, ⟨.sem Opacity, []⟩, none⟩,
  ⟨lenIn, ⟨.q Dim.Length, []⟩, none⟩,
  ⟨timeIn, ⟨.q Dim.Time, []⟩, none⟩,
  ⟨mode1, ⟨.sem Mode, []⟩, none⟩,
  ⟨mode2, ⟨.sem Mode, []⟩, none⟩]

def Δ : DeclEnv := .ofList decls

/-- The design is globally well typed (every realization at its declared type). -/
theorem examples_well_typed : GlobalWF trivEv Θ Δ := GlobalWF.ofList (by decide)

def rank : DeclId → Nat := fun d =>
  if d = bOut then 1 else if d = isAuto ∨ d = allBelow ∨ d = anyHigh ∨ d = th ∨ d = calibrated ∨ d = zipped ∨ d = firstOr ∨ d = inRng then 1
  else if d = thT then 2 else if d = level then 2 else 0

theorem examples_causal : causalCheck decls rank = true := by decide

/-- Inputs: brightness `b`, mode `m`, temperatures, fault severities, humidity, ys. -/
def mkI (b m h tp : Nat) (ts fs yv : List Nat) : Input := fun d _ =>
  if d = bIn then .sem Brightness (.nat b)
  else if d = mode then .nat m
  else if d = hum then .nat h
  else if d = temp then .nat tp
  else if d = temps then .list (ts.map .nat)
  else if d = faults then .list (fs.map .nat)
  else if d = ys then .list (yv.map .nat)
  else if d = oIn then .sem Opacity (.nat 0)
  else .nat 0

/-- Run a declaration and compare structurally with an expected value. -/
def runIs (I : Input) (d : DeclId) (v : Value) : Bool :=
  match evalF Δ I 64 0 [] (.declRef d) with
  | some w => Value.beq w v
  | none => false

def I₁ : Input := mkI 5 2 45 25 [20, 25, 28] [1, 3] [7, 8]
def I₂ : Input := mkI 100 3 70 35 [20, 35] [1, 2] []

/-- **A — clamp brightness**: 5 ↦ 10 (the lower bound), 100 ↦ 90; the result
    is still a `Brightness` value. -/
theorem exA : runIs I₁ bOut (.sem Brightness (.nat 10)) ∧ runIs I₂ bOut (.sem Brightness (.nat 90)) := by decide

/-- **B — mode in a finite set**: 2 ∈ {1, 2}; 3 ∉ {1, 2}. -/
theorem exB : runIs I₁ isAuto (.bool true) ∧ runIs I₂ isAuto (.bool false) := by decide

/-- **C — every sensor below the threshold**. -/
theorem exC : runIs I₁ allBelow (.bool true) ∧ runIs I₂ allBelow (.bool false) := by decide

/-- **D — any fault above the severity threshold**. -/
theorem exD : runIs I₁ anyHigh (.bool true) ∧ runIs I₂ anyHigh (.bool false) := by decide

/-- **E — pair of temperature and humidity**, and its first projection. -/
theorem exE : runIs I₁ th (.pair (.nat 25) (.nat 45)) ∧ runIs I₁ thT (.nat 25) := by decide

/-- **F — map a calibration over sensor values**. -/
theorem exF : runIs I₁ calibrated (.list [.nat 25, .nat 30, .nat 33]) := by decide

/-- **G — zip two sampled collections** (truncates to the shorter). -/
theorem exG : runIs I₁ zipped (.list [.pair (.nat 20) (.nat 7), .pair (.nat 25) (.nat 8)]) ∧
    runIs I₂ zipped (.list []) := by decide

/-- **H — generic Option fallback**: `head temps` or `0`. -/
theorem exH : runIs I₁ firstOr (.nat 20) ∧ runIs (mkI 0 0 0 0 [] [] []) firstOr (.nat 0) := by decide

/-- **I — dimension-preserving min**: `min` at `q Length` types on two
    lengths and is rejected on a length and a time. -/
theorem exI :
    infer Θ Δ Grant.none [] (app2 (minF (.q Dim.Length)) (.declRef lenIn) (.declRef lenIn)) = some (.q Dim.Length) ∧
    infer Θ Δ Grant.none [] (app2 (minF (.q Dim.Length)) (.declRef lenIn) (.declRef timeIn)) = none := by decide

/-- **J — semantic-type-preserving generic**: `min` at `Brightness` returns
    `Brightness` and rejects an `Opacity` argument, although both are `q 0`
    underneath. -/
theorem exJ :
    infer Θ Δ Grant.none [] (app2 (minF oB) (.declRef bIn) (.declRef bMin)) = some B ∧
    infer Θ Δ Grant.none [] (app2 (minF oB) (.declRef bIn) (.declRef oIn)) = none ∧
    infer Θ Δ Grant.none [] (eqE B trivial (.declRef bIn) (.declRef oIn)) = none ∧
    infer Θ Δ Grant.none [] (app2 (containsF B trivial) (.declRef oIn) (listLit B [.declRef bIn])) = none := by decide

/-! ## Phase 9c — the capability boundary, on realistic types

`Mode` is a concept represented like `Brightness` (`q 0`) but *not*
declared ordered.  Equality is accepted on modes, pairs, lists and options;
ordering is rejected on all of them — at the surface (no `Ordered`
evidence: `Scheme.instantiate = none`) and in the kernel, where `lt`
exists only at quantities, so the terms cannot even be written. -/

/-- **Equality accepted** on modes, pairs of quantities, lists and options. -/
theorem eq_accepted :
    infer Θ Δ Grant.none [] (eqE (.sem Mode) trivial (.declRef mode1) (.declRef mode2)) = some .bool ∧
    infer Θ Δ Grant.none [] (eqE (.prod Q0 Q0) ⟨trivial, trivial⟩ (.declRef th) (.declRef th)) = some .bool ∧
    infer Θ Δ Grant.none [] (eqE (.list Q0) trivial (.declRef temps) (.declRef ys)) = some .bool ∧
    infer Θ Δ Grant.none [] (eqE (.opt Q0) trivial (.app (.prim (.head Q0)) (.declRef temps)) (noneE Q0)) = some .bool ∧
    runIs (mkI 0 0 0 0 [1, 2] [] [1, 2]) ⟨0⟩ (.sem Brightness (.nat 0)) = true := by decide

def ltScheme : Poly.Scheme := ⟨.arr (.tvar 0) (.arr (.tvar 0) .bool), [(0, .ord)]⟩
def eqScheme : Poly.Scheme := ⟨.arr (.tvar 0) (.arr (.tvar 0) .bool), [(0, .eq)]⟩

/-- **Ordering rejected** where it has no behaviour-design meaning:
    `mode1 < mode2`, `pair < pair`, `list < list`, `None < Some`, `bool < bool`
    — and accepted exactly on quantities and declared-ordered concepts. -/
theorem lt_rejected :
    ltScheme.instantiate O Θ (.arr (.sem Mode) (.arr (.sem Mode) .bool)) = none ∧
    ltScheme.instantiate O Θ (.arr (.prod Q0 Q0) (.arr (.prod Q0 Q0) .bool)) = none ∧
    ltScheme.instantiate O Θ (.arr (.list Q0) (.arr (.list Q0) .bool)) = none ∧
    ltScheme.instantiate O Θ (.arr (.opt Q0) (.arr (.opt Q0) .bool)) = none ∧
    ltScheme.instantiate O Θ (.arr .bool (.arr .bool .bool)) = none ∧
    (ltScheme.instantiate O Θ (.arr B (.arr B .bool))).isSome = true ∧
    (ltScheme.instantiate O Θ (.arr Q0 (.arr Q0 .bool))).isSome = true ∧
    -- the same types all admit equality
    (eqScheme.instantiate O Θ (.arr (.sem Mode) (.arr (.sem Mode) .bool))).isSome = true ∧
    (eqScheme.instantiate O Θ (.arr (.prod Q0 Q0) (.arr (.prod Q0 Q0) .bool))).isSome = true ∧
    (eqScheme.instantiate O Θ (.arr (.list Q0) (.arr (.list Q0) .bool))).isSome = true ∧
    (eqScheme.instantiate O Θ (.arr (.opt Q0) (.arr (.opt Q0) .bool))).isSome = true := by decide

/-- In the kernel no ordering exists on these types at all: the only
    comparison primitive is at quantities. -/
theorem lt_only_on_quantities (p : Prim) (τ : Ty) (h : p.ty = .arr τ (.arr τ .bool)) (hlt : ∃ d, p = .lt d) :
    ∃ d, τ = .q d := by
  obtain ⟨d, rfl⟩ := hlt
  simp only [Prim.ty, Ty.arr.injEq] at h
  exact ⟨d, h.1.symm⟩

/-- An ordered concept's evidence is well formed only if declared: with
    `O Mode = false` no admissible instance exists, whatever dimension is
    tried — this is the rejection of `min<Mode>`. -/
theorem min_mode_rejected : Poly.Ty.ordB O Θ (.sem Mode) = false ∧ ¬ (Poly.Cap.holds O Θ .ord (.sem Mode)) := by
  simp [Poly.Ty.ordB, Poly.Cap.holds, O, Mode, Brightness, Opacity]

/-- **K — range membership**: 45 ∈ [30, 60]; 70 ∉. -/
theorem exK : runIs I₁ inRng (.bool true) ∧ runIs I₂ inRng (.bool false) := by decide

/-- **L — piecewise rule** over a range, a collection predicate and a
    boolean: level 1 when humidity in range and all temperatures below the
    threshold; level 2 when some fault is severe; else 0. -/
theorem exL : runIs I₁ level (.nat 1) ∧ runIs I₂ level (.nat 0) ∧
    runIs (mkI 0 0 70 0 [] [5] []) level (.nat 2) := by decide

/-! ## M — an enumeration with a payload, as a tagged product

Production BDL's textual syntax declares `enum LampMode { Off, Automatic,
Manual(Brightness) }` and matches on it.  Without a kernel sum type the
value is a tag paired with the optional payload, and `match` elaborates to
a conditional on the tag with `getD` on the payload.  The encoding is
executable; whether a kernel `sum` is warranted is recorded as deferred. -/

def LampMode : Ty := .prod Q0 (.opt Q0)
def modeOff : Expr := pairE Q0 (.opt Q0) (lit 0) (noneE Q0)
def modeAuto : Expr := pairE Q0 (.opt Q0) (lit 1) (noneE Q0)
def modeManual (b : Expr) : Expr := pairE Q0 (.opt Q0) (lit 2) (someE Q0 b)
/-- `match mode { Off => 0, Automatic => tilt, Manual(v) => v }` -/
def resolveE (m tilt : Expr) : Expr :=
  iteE Q0 (eqE Q0 trivial (fstE Q0 (.opt Q0) m) (lit 0)) (lit 0)
    (iteE Q0 (eqE Q0 trivial (fstE Q0 (.opt Q0) m) (lit 1)) tilt
      (app2 (getOrElseF Q0) (sndE Q0 (.opt Q0) m) (lit 0)))

theorem exM :
    infer Θ Δ Grant.none [] modeOff = some LampMode ∧
    infer Θ Δ Grant.none [] (resolveE (modeManual (lit 7)) (lit 3)) = some Q0 ∧
    (evalF Δ I₁ 64 0 [] (resolveE modeOff (lit 3))).map (Value.beq · (.nat 0)) = some true ∧
    (evalF Δ I₁ 64 0 [] (resolveE modeAuto (lit 3))).map (Value.beq · (.nat 3)) = some true ∧
    (evalF Δ I₁ 64 0 [] (resolveE (modeManual (lit 7)) (lit 3))).map (Value.beq · (.nat 7)) = some true := by
  decide

/-! ## Records elaborate to nested pairs -/

def rec3 : Expr := recE [(Q0, lit 1), (Q0, lit 2), (.bool, .boolLit true)]

theorem records_are_pairs :
    infer Θ Δ Grant.none [] rec3 = some (.prod Q0 (.prod Q0 .bool)) ∧
    (evalF Δ I₁ 64 0 [] (projE [Q0, Q0, .bool] 1 rec3)).map (Value.beq · (.nat 2)) = some true ∧
    (evalF Δ I₁ 64 0 [] (projE [Q0, Q0, .bool] 2 rec3)).map (Value.beq · (.bool true)) = some true := by decide

/-! ## Options through `fold`: `mapOpt` and `optElim` -/

theorem options_by_fold :
    (evalF Δ I₁ 64 0 [] (app2 (mapOptF Q0 Q0) (.lam Q0 (app2 (.prim (.add Dim.zero)) (.var 0) (lit 1)))
      (someE Q0 (lit 4)))).map (Value.beq · (.some (.nat 5))) = some true ∧
    (evalF Δ I₁ 64 0 [] (app3 (optElimF Q0 .bool) (.boolLit false) (.lam Q0 (ltE Dim.zero (lit 3) (.var 0)))
      (noneE Q0))).map (Value.beq · (.bool false)) = some true := by decide

end BDL.Experiments.Equations
