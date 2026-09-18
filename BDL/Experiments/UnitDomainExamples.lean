import BDL.Surface.UnitDomain
import BDL.Surface.Stdlib

/-!
# Phase 12 — executed examples for the unit-domain normalization

The lamp again.  `TempSensor : () -> RoomTemp` is unresolved (a source);
`boost : () -> Q0` is resolved with memory (`delay 0 (boost + 1)`, a
counter); `dimByTilt : Tilt -> Q0` has one input.  Each example is a closed
`decide`: the signatures round-trip through the two encodings; `boost`,
`boost()` and `boost(())` evaluate to one value at each tick; the source is
read from the input; the literal alternative — a unit binder around memory —
is refused by `infer`.
-/

namespace BDL.Experiments.UnitDomainEx
open BDL BDL.Reactive BDL.Stdlib BDL.UnitDomain

def Tilt : SemanticId := ⟨80⟩
def RoomTemp : SemanticId := ⟨81⟩
def Θ : ConceptEnv := fun s =>
  if s = Tilt then some (.q Dim.Angle) else if s = RoomTemp then some (.q Dim.Temp) else none
def Q0 : Ty := .q Dim.zero
def QA : Ty := .q Dim.Angle
def lit (n : Nat) : Expr := .prim (.lit Dim.zero n)
def addE (a b : Expr) : Expr := app2 (.prim (.add Dim.zero)) a b

def tempSensor : DeclId := ⟨0⟩   -- () -> RoomTemp, unresolved: a source
def boost : DeclId := ⟨1⟩        -- () -> Q0, resolved with memory
def dimByTilt : DeclId := ⟨2⟩    -- Tilt -> q Angle

def Δ : DeclEnv := .ofList [
  ⟨tempSensor, ⟨.sem RoomTemp, []⟩, none⟩,
  ⟨boost, ⟨Q0, []⟩, some (.delay (lit 0) (addE (.declRef boost) (lit 1)))⟩,
  ⟨dimByTilt, ⟨.arr (.sem Tilt) QA, []⟩, some (.lam (.sem Tilt) (.rep (.var 0)))⟩]

def I : Input := fun d t => if d = tempSensor then .sem RoomTemp (.nat (20 + t)) else .nat 0

def runIs (I : Input) (t : Nat) (ρ : List Value) (e : Expr) (v : Value) : Bool :=
  match evalF Δ I 64 t ρ e with | some w => Value.beq w v | none => false
def ty (Γ : Ctx) (e : Expr) : Option Ty := infer Θ Δ Grant.none Γ e

/-! ## A — the signatures and their two encodings -/

def sigTemp : Sig := ⟨[], .sem RoomTemp⟩
def sigDim : Sig := ⟨[.sem Tilt], QA⟩
def sigTwo : Sig := ⟨[.sem Tilt, .sem RoomTemp], Q0⟩

/-- `() -> RoomTemp` is the canonical type; `RoomTemp` is the kernel one;
    each recovers the other; unit elimination computes the encoding. -/
theorem exA :
    canonical sigTemp = .arr .unit (.k (.sem RoomTemp)) ∧
    encode sigTemp = .sem RoomTemp ∧
    canonicalOfKernel (.sem RoomTemp) = canonical sigTemp ∧
    canonical sigTwo = .arr (.prod (.k (.sem Tilt)) (.k (.sem RoomTemp))) (.k Q0) ∧
    encode sigTwo = .arr (.sem Tilt) (.arr (.sem RoomTemp) Q0) ∧
    decode (encode sigTwo) = sigTwo ∧ decode (encode sigDim) = sigDim ∧
    elim (canonical sigTemp) = some (encode sigTemp) ∧
    elim (canonical sigTwo) = some (encode sigTwo) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> simp [canonical, sigTemp, sigTwo, domainOf, elim, encode, Q0]

/-! ## B — `boost`, `boost()`, `boost(())` are one term with one value -/

theorem exB :
    (RefForm.bare boost).desugar = (RefForm.call0 boost).desugar ∧
    (RefForm.call0 boost).desugar = (RefForm.callUnit boost).desugar ∧
    runIs I 0 [] (.declRef boost) (.nat 0) ∧
    runIs I 1 [] (.declRef boost) (.nat 1) ∧
    runIs I 3 [] (.declRef boost) (.nat 3) ∧
    -- two readings in one tick, in different local environments, agree
    runIs I 3 [.nat 99] (.declRef boost) (.nat 3) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## C — the source is read from the environment; the resolved one is not -/

theorem exC :
    runIs I 0 [] (.declRef tempSensor) (.sem RoomTemp (.nat 20)) ∧
    runIs I 5 [] (.declRef tempSensor) (.sem RoomTemp (.nat 25)) ∧
    -- `boost` ignores the input stream entirely: another `I` gives the same value
    runIs (fun _ _ => .nat 7) 3 [] (.declRef boost) (.nat 3) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## D — typing: the realization of `() -> Q0` is checked at `Q0`; a unit
binder around the memory would be refused -/

theorem exD :
    ty [] (.delay (lit 0) (addE (.declRef boost) (lit 1))) = some Q0 ∧
    -- the literal alternative: a binder (of any domain) around the delay
    ty [] (.lam Q0 (.delay (lit 0) (addE (.declRef boost) (lit 1)))) = none ∧
    -- the one-input mapping is one binder around a body checked under `[sem Tilt]`
    ty [.sem Tilt] (.rep (.var 0)) = some QA ∧
    ty [] (lams [.sem Tilt] (.rep (.var 0))) = some (encode sigDim) ∧
    lams [] (.declRef boost) = .declRef boost := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩ <;> decide

/-! ## E — transport and drive want a unit domain -/

theorem exE :
    ty [] (.sync ⟨1⟩ (lit 0) (.declRef boost)) = some Q0 ∧
    ty [] (.sync ⟨1⟩ (.declRef tempSensor) (.declRef tempSensor)) = some (.sem RoomTemp) ∧
    -- a relationship with inputs cannot be transported: `sync` needs data
    ty [] (.sync ⟨1⟩ (.declRef dimByTilt) (.declRef dimByTilt)) = none := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end BDL.Experiments.UnitDomainEx
