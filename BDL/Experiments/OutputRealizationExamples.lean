import BDL.Surface.OutputRealization
import BDL.Surface.Stdlib
import BDL.Experiments.HardwareAlternatives

/-!
# Phase 14 — executed examples for output realization

One abstract design with four logical outputs — a light (`Brightness`), a
relay (`SwitchState`), a servo (`ServoAngle`), a motor (`MotorSpeed`) — and
the device encoders deployment may choose for them:

* A — GPIO: `SwitchState -> bool` (the identity level).
* B — PWM: `Brightness -> duty` (`n·255/100`), and 4-bit PWM that
  quantizes (40 % and 41 % both to duty 6) — still a valid realization.
* C — a calibrated non-linear actuator: `ServoAngle -> pulse width`
  (`1000 + a·1000/180` µs).
* D — H-bridge: `MotorSpeed = (forward?, magnitude)` → `(duty, direction)`,
  a structured raw command from a pair, with no record type.
* E/F/G — rejected: an encoder at the wrong representation does not fit; a
  concept represented differently does not fit; an encoder that constructs
  a concept is untypable under `Grant.none`; an impure encoder is
  tick-dependent.
* H — **the platform-independence witness**: the same light realized by
  PWM and by an I²C register; the behaviour trace is identical, the raw
  command types and traces differ; both profiles are admissible on the
  Nano.
* I — Model A refuted executably: retargeting `oLight.accepts` to the duty
  type breaks the drive edge; an encoder in another clock breaks it too.
-/

namespace BDL.Experiments.OutputRealizationEx
open BDL BDL.Reactive BDL.Clock BDL.Output BDL.Stdlib BDL.Provision BDL.OutputRealization BDL.Hardware

/-! ## The abstract design -/

def Brightness : SemanticId := ⟨100⟩   -- percent, `q 0`
def SwitchState : SemanticId := ⟨101⟩  -- `bool`
def ServoAngle : SemanticId := ⟨102⟩   -- degrees, `q Angle`
def MotorSpeed : SemanticId := ⟨103⟩   -- `(forward?, magnitude)`, `bool × q 0`
def Other : SemanticId := ⟨104⟩        -- an unrelated concept, `q 0`

def Q0 : Ty := .q Dim.zero
def QA : Ty := .q Dim.Angle
def MS : Ty := .prod .bool Q0

def Θ : ConceptEnv := fun s =>
  if s = Brightness then some Q0 else if s = SwitchState then some .bool
  else if s = ServoAngle then some QA else if s = MotorSpeed then some MS
  else if s = Other then some Q0 else none

def lit (d : Dim) (n : Nat) : Expr := .prim (.lit d n)

-- declarations
def dial : DeclId := ⟨0⟩     -- () -> Brightness, a Source
def light : DeclId := ⟨1⟩    -- Brightness := dial (the driver of the light)
def sw : DeclId := ⟨2⟩       -- () -> SwitchState, a Source, drives the relay
def ang : DeclId := ⟨3⟩      -- () -> ServoAngle, drives the servo
def spd : DeclId := ⟨4⟩      -- () -> MotorSpeed, drives the motor
-- fresh encoder identities
def ePwm : DeclId := ⟨10⟩
def eI2c : DeclId := ⟨11⟩
def eGpio : DeclId := ⟨12⟩
def eServo : DeclId := ⟨13⟩
def eH : DeclId := ⟨14⟩
def ePwm4 : DeclId := ⟨15⟩

-- logical outputs and machine sinks
def oLight : OutputId := ⟨0⟩
def oRelay : OutputId := ⟨1⟩
def oServo : OutputId := ⟨2⟩
def oMotor : OutputId := ⟨3⟩
def pPwm : OutputId := ⟨10⟩
def pI2c : OutputId := ⟨11⟩
def pGpio : OutputId := ⟨12⟩
def pServo : OutputId := ⟨13⟩
def pH : OutputId := ⟨14⟩
def pPwm4 : OutputId := ⟨15⟩

def c0 : ClockId := ⟨0⟩

def decls : List DesignDecl := [
  ⟨dial, ⟨.sem Brightness, []⟩, none⟩,
  ⟨light, ⟨.sem Brightness, []⟩, some (.mk Brightness (.rep (.declRef dial)))⟩,
  ⟨sw, ⟨.sem SwitchState, []⟩, none⟩,
  ⟨ang, ⟨.sem ServoAngle, []⟩, none⟩,
  ⟨spd, ⟨.sem MotorSpeed, []⟩, none⟩]
def Δ : DeclEnv := .ofList decls
def Κ : ClockEnv := fun _ => some c0
def specLight : OutputSpec := ⟨.sem Brightness, c0⟩
def specRelay : OutputSpec := ⟨.sem SwitchState, c0⟩
def specServo : OutputSpec := ⟨.sem ServoAngle, c0⟩
def specMotor : OutputSpec := ⟨.sem MotorSpeed, c0⟩
def Ω : OutputEnv := .ofList [(oLight, specLight), (oRelay, specRelay), (oServo, specServo), (oMotor, specMotor)]
def edges : List (DeclId × OutputId) := [(light, oLight), (sw, oRelay), (ang, oServo), (spd, oMotor)]
def β : DriveEnv := .ofList edges

theorem Δ_typed : GlobalWF (fun _ _ _ => True) Θ Δ := GlobalWF.ofList (by decide)
theorem Δ_causal : Causal Δ :=
  Causal.ofList (fun d => if d = light then 1 else 0) 2 (by intro d; split <;> omega) (by decide)
theorem Δ_clocked : WellClocked Κ Δ := WellClocked.ofList (by decide)
theorem β_wf : DriveWF Ω Κ Δ β := DriveWF.ofList (by decide)
theorem β_single : SingleDriver β := SingleDriver.ofList (by decide)

/-! ## Encoders -/

/-- Identity level: `bool -> bool`. -/
def gpio : Encoder where
  rep := .bool
  raw := .bool
  encode := .lam .bool (.var 0)
  transfer := id
  rep_semFree := trivial
  rep_data := trivial
  raw_semFree := trivial
  raw_data := trivial
  encode_pure := trivial
  computes := by rintro v ⟨b, rfl⟩; exact .appClo .lam (.refInput rfl) (.var rfl)

/-- 8-bit PWM: `duty = n · 255 / 100`. -/
def pwm8Tr : Expr :=
  .lam Q0 (app2 (.prim (.div Dim.zero Dim.zero))
    (app2 (.prim (.mul Dim.zero Dim.zero)) (.var 0) (lit Dim.zero 255)) (lit Dim.zero 100))

def pwm8 : Encoder where
  rep := Q0
  raw := Q0
  encode := pwm8Tr
  transfer := fun v => match v with | .nat n => .nat (n * 255 / 100) | v => v
  rep_semFree := trivial
  rep_data := trivial
  raw_semFree := trivial
  raw_data := trivial
  encode_pure := by simp [pwm8Tr, app2, lit, Expr.Pure]
  computes := by
    rintro v ⟨n, rfl⟩
    have h := Ev.appClo (Δ := DeclEnv.empty) (I := fun _ _ => Value.nat n) (t := 0) (ρ := [])
      (f := pwm8Tr) (a := .declRef ⟨0⟩) (ρ' := []) (body := _) (va := .nat n) .lam (.refInput rfl)
      (Ev.prim2 rfl (Ev.prim2 rfl (.var rfl) (Ev.lit _ _)) (Ev.lit _ _))
    simpa [Transduces, Prim.compute] using h

/-- 4-bit PWM: `duty = n · 15 / 100` — a quantizing encoder. -/
def pwm4Tr : Expr :=
  .lam Q0 (app2 (.prim (.div Dim.zero Dim.zero))
    (app2 (.prim (.mul Dim.zero Dim.zero)) (.var 0) (lit Dim.zero 15)) (lit Dim.zero 100))

def pwm4 : Encoder where
  rep := Q0
  raw := Q0
  encode := pwm4Tr
  transfer := fun v => match v with | .nat n => .nat (n * 15 / 100) | v => v
  rep_semFree := trivial
  rep_data := trivial
  raw_semFree := trivial
  raw_data := trivial
  encode_pure := by simp [pwm4Tr, app2, lit, Expr.Pure]
  computes := by
    rintro v ⟨n, rfl⟩
    have h := Ev.appClo (Δ := DeclEnv.empty) (I := fun _ _ => Value.nat n) (t := 0) (ρ := [])
      (f := pwm4Tr) (a := .declRef ⟨0⟩) (ρ' := []) (body := _) (va := .nat n) .lam (.refInput rfl)
      (Ev.prim2 rfl (Ev.prim2 rfl (.var rfl) (Ev.lit _ _)) (Ev.lit _ _))
    simpa [Transduces, Prim.compute] using h

/-- An I²C brightness register: the command is `(register 42, value n)`. -/
def i2cTr : Expr := .lam Q0 (app2 (.prim (.pair Q0 Q0)) (lit Dim.zero 42) (.var 0))

def i2cReg : Encoder where
  rep := Q0
  raw := .prod Q0 Q0
  encode := i2cTr
  transfer := fun v => .pair (.nat 42) v
  rep_semFree := trivial
  rep_data := trivial
  raw_semFree := ⟨trivial, trivial⟩
  raw_data := ⟨trivial, trivial⟩
  encode_pure := by simp [i2cTr, app2, lit, Expr.Pure]
  computes := by
    rintro v ⟨n, rfl⟩
    have h := Ev.appClo (Δ := DeclEnv.empty) (I := fun _ _ => Value.nat n) (t := 0) (ρ := [])
      (f := i2cTr) (a := .declRef ⟨0⟩) (ρ' := []) (body := _) (va := .nat n) .lam (.refInput rfl)
      (Ev.prim2 rfl (Ev.lit _ _) (.var rfl))
    simpa [Transduces, Prim.compute] using h

/-- A servo pulse: `1000 + a · 1000 / 180` µs from degrees — calibrated,
    non-linear in the sense that the raw command is an affine function of
    the angle with integer division. -/
def servoTr : Expr :=
  .lam QA (app2 (.prim (.add Dim.zero)) (lit Dim.zero 1000)
    (app2 (.prim (.div (Dim.Angle.add Dim.zero) Dim.Angle))
      (app2 (.prim (.mul Dim.Angle Dim.zero)) (.var 0) (lit Dim.zero 1000)) (lit Dim.Angle 180)))

def servoPulse : Encoder where
  rep := QA
  raw := Q0
  encode := servoTr
  transfer := fun v => match v with | .nat a => .nat (1000 + a * 1000 / 180) | v => v
  rep_semFree := trivial
  rep_data := trivial
  raw_semFree := trivial
  raw_data := trivial
  encode_pure := by simp [servoTr, app2, lit, Expr.Pure]
  computes := by
    rintro v ⟨a, rfl⟩
    have h := Ev.appClo (Δ := DeclEnv.empty) (I := fun _ _ => Value.nat a) (t := 0) (ρ := [])
      (f := servoTr) (a := .declRef ⟨0⟩) (ρ' := []) (body := _) (va := .nat a) .lam (.refInput rfl)
      (Ev.prim2 rfl (Ev.lit _ _) (Ev.prim2 rfl (Ev.prim2 rfl (.var rfl) (Ev.lit _ _)) (Ev.lit _ _)))
    simpa [Transduces, Prim.compute] using h

/-- H-bridge: `(forward?, magnitude) ↦ (duty = magnitude · 2, direction = forward?)`. -/
def hbridgeTr : Expr :=
  .lam MS (app2 (.prim (.pair Q0 .bool))
    (app2 (.prim (.mul Dim.zero Dim.zero)) (.app (.prim (.snd .bool Q0)) (.var 0)) (lit Dim.zero 2))
    (.app (.prim (.fst .bool Q0)) (.var 0)))

def hbridge : Encoder where
  rep := MS
  raw := .prod Q0 .bool
  encode := hbridgeTr
  transfer := fun v => match v with | .pair f (.nat m) => .pair (.nat (m * 2)) f | v => v
  rep_semFree := ⟨trivial, trivial⟩
  rep_data := ⟨trivial, trivial⟩
  raw_semFree := ⟨trivial, trivial⟩
  raw_data := ⟨trivial, trivial⟩
  encode_pure := by simp [hbridgeTr, app2, lit, Expr.Pure]
  computes := by
    rintro v ⟨f, m, rfl, ⟨b, rfl⟩, ⟨n, rfl⟩⟩
    have h := Ev.appClo (Δ := DeclEnv.empty) (I := fun _ _ => Value.pair (.bool b) (.nat n)) (t := 0) (ρ := [])
      (f := hbridgeTr) (a := .declRef ⟨0⟩) (ρ' := []) (body := _) (va := .pair (.bool b) (.nat n)) .lam (.refInput rfl)
      (Ev.prim2 rfl (Ev.prim2 rfl (Ev.appPrim .prim (.var rfl)) (Ev.lit _ _)) (Ev.appPrim .prim (.var rfl)))
    simpa [Transduces, applyPrim, Prim.arity, Prim.compute] using h

/-! ## Realizations and their preconditions -/

def RPwm : Realization := ⟨oLight, light, pPwm, ePwm, pwm8⟩
def RPwm4 : Realization := ⟨oLight, light, pPwm4, ePwm4, pwm4⟩
def RI2c : Realization := ⟨oLight, light, pI2c, eI2c, i2cReg⟩
def RGpio : Realization := ⟨oRelay, sw, pGpio, eGpio, gpio⟩
def RServo : Realization := ⟨oServo, ang, pServo, eServo, servoPulse⟩
def RH : Realization := ⟨oMotor, spd, pH, eH, hbridge⟩

theorem wfPwm : WF Θ Δ Ω β Κ RPwm specLight :=
  WF.of_driveWF β_wf rfl rfl rfl rfl (by decide) (infer_sound (by decide))
theorem wfPwm4 : WF Θ Δ Ω β Κ RPwm4 specLight :=
  WF.of_driveWF β_wf rfl rfl rfl rfl (by decide) (infer_sound (by decide))
theorem wfI2c : WF Θ Δ Ω β Κ RI2c specLight :=
  WF.of_driveWF β_wf rfl rfl rfl rfl (by decide) (infer_sound (by decide))
theorem wfGpio : WF Θ Δ Ω β Κ RGpio specRelay :=
  WF.of_driveWF β_wf rfl rfl rfl rfl (by decide) (infer_sound (by decide))
theorem wfServo : WF Θ Δ Ω β Κ RServo specServo :=
  WF.of_driveWF β_wf rfl rfl rfl rfl (by decide) (infer_sound (by decide))
theorem wfH : WF Θ Δ Ω β Κ RH specMotor :=
  WF.of_driveWF β_wf rfl rfl rfl rfl (by decide) (infer_sound (by decide))

/-- The inputs: dial 40 % at tick 0, 41 % at tick 1; switch on; angle 90°;
    motor forward at 30. -/
def I : Input := fun d t =>
  if d = dial then .sem Brightness (.nat (40 + t))
  else if d = sw then .sem SwitchState (.bool true)
  else if d = ang then .sem ServoAngle (.nat 90)
  else if d = spd then .sem MotorSpeed (.pair (.bool true) (.nat 30))
  else .nat 0

def runIs (Δ : DeclEnv) (t : Nat) (e : Expr) (v : Value) : Bool :=
  match evalF Δ I 64 t [] e with | some w => Value.beq w v | none => false

def ΔPwm : DeclEnv := lowerΔ Δ RPwm specLight
def ΔPwm4 : DeclEnv := lowerΔ Δ RPwm4 specLight
def ΔI2c : DeclEnv := lowerΔ Δ RI2c specLight
def ΔGpio : DeclEnv := lowerΔ Δ RGpio specRelay
def ΔServo : DeclEnv := lowerΔ Δ RServo specServo
def ΔH : DeclEnv := lowerΔ Δ RH specMotor

/-! ## A–D — the encoders at work -/

theorem exA_gpio :
    ΔGpio.realizationOf eGpio = some (.app gpio.encode (.rep (.declRef sw))) ∧
    runIs ΔGpio 0 (.declRef eGpio) (.bool true) ∧
    runIs ΔGpio 0 (.declRef sw) (.sem SwitchState (.bool true)) := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

theorem exB_pwm :
    ΔPwm.realizationOf ePwm = some (.app pwm8Tr (.rep (.declRef light))) ∧
    runIs ΔPwm 0 (.declRef ePwm) (.nat 102) ∧
    runIs ΔPwm 1 (.declRef ePwm) (.nat 104) ∧
    -- the logical driver is untouched
    runIs ΔPwm 0 (.declRef light) (.sem Brightness (.nat 40)) ∧
    runIs Δ 0 (.declRef light) (.sem Brightness (.nat 40)) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Quantization: 40 % and 41 % both become duty 6, and the realization is
    as valid as the 8-bit one — no injectivity is required. -/
theorem exB_quantized :
    runIs ΔPwm4 0 (.declRef ePwm4) (.nat 6) ∧ runIs ΔPwm4 1 (.declRef ePwm4) (.nat 6) ∧
    runIs ΔPwm4 0 (.declRef light) (.sem Brightness (.nat 40)) ∧
    runIs ΔPwm4 1 (.declRef light) (.sem Brightness (.nat 41)) ∧
    driveWFCheck (lowerΩ Ω RPwm4 specLight) (lowerΚ Κ RPwm4 specLight) ΔPwm4 ((ePwm4, pPwm4) :: edges) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem exC_servo :
    runIs ΔServo 0 (.declRef eServo) (.nat 1500) ∧
    runIs ΔServo 0 (.declRef ang) (.sem ServoAngle (.nat 90)) := by
  refine ⟨?_, ?_⟩ <;> decide

theorem exD_hbridge :
    runIs ΔH 0 (.declRef eH) (.pair (.nat 60) (.bool true)) ∧
    ΔH.tyView eH = some (.prod Q0 .bool) := by
  refine ⟨?_, rfl⟩; decide

/-! ## E/F/G — rejected profiles and encoders -/

/-- A typed term with memory: `(λk. λn. k) (delay 0 1)`; typed at `q₀ -> q₀`,
    impure, and its "encoding" of 7 is 0 at tick 0 and 1 at tick 1. -/
def memEnc : Expr := .app (.lam Q0 (.lam Q0 (.var 1))) (.delay (lit Dim.zero 0) (lit Dim.zero 1))

theorem exEFG :
    -- E: the PWM encoder does not fit the relay (a `bool` output)
    ¬ EFits Θ (.sem SwitchState) pwm8 ∧
    -- F: the servo encoder consumes angles; it does not fit the light (a percentage)
    ¬ EFits Θ (.sem Brightness) servoPulse ∧
    -- the fits that hold
    EFits Θ (.sem Brightness) pwm8 ∧ EFits Θ (.sem Brightness) i2cReg ∧ EFits Θ (.sem MotorSpeed) hbridge ∧
    -- G: an encoder that constructs a concept is refused under `Grant.none`
    infer Θ DeclEnv.empty Grant.none [] (.lam Q0 (.mk Other (.var 0))) = none ∧
    -- and would be accepted only under that concept's grant, which no encoder has
    infer Θ DeclEnv.empty (Grant.of (.sem Other)) [] (.lam Q0 (.mk Other (.var 0))) = some (.arr Q0 (.sem Other)) ∧
    -- an impure encoder is typed yet tick-dependent
    infer Θ DeclEnv.empty Grant.none [] memEnc = some (.arr Q0 Q0) ∧ ¬ memEnc.Pure ∧
    (match evalF DeclEnv.empty (fun _ _ => .nat 7) 32 0 [] (.app memEnc (.declRef ⟨0⟩)) with
      | some (.nat n) => n | _ => 99) = 0 ∧
    (match evalF DeclEnv.empty (fun _ _ => .nat 7) 32 1 [] (.app memEnc (.declRef ⟨0⟩)) with
      | some (.nat n) => n | _ => 99) = 1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

/-! ## H — the platform-independence witness -/

/-- The same light, realized by PWM and by I²C: the logical output carries
    the same value in both lowered designs (and in the abstract one); the
    machine commands differ in type and value. -/
theorem exH :
    -- behaviour trace identical
    runIs ΔPwm 0 (.declRef light) (.sem Brightness (.nat 40)) ∧
    runIs ΔI2c 0 (.declRef light) (.sem Brightness (.nat 40)) ∧
    runIs Δ 0 (.declRef light) (.sem Brightness (.nat 40)) ∧
    -- the same logical output in both
    lowerΩ Ω RPwm specLight oLight = some specLight ∧ lowerΩ Ω RI2c specLight oLight = some specLight ∧
    lowerβ β RPwm light = some oLight ∧ lowerβ β RI2c light = some oLight ∧
    -- different machine sinks, types and commands
    lowerΩ Ω RPwm specLight pPwm = some ⟨Q0, c0⟩ ∧ lowerΩ Ω RI2c specLight pI2c = some ⟨.prod Q0 Q0, c0⟩ ∧
    runIs ΔPwm 0 (.declRef ePwm) (.nat 102) ∧
    runIs ΔI2c 0 (.declRef eI2c) (.pair (.nat 42) (.nat 40)) := by
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> decide

/-- The structural theorems, instantiated on the PWM realization. -/
theorem exH_structure :
    EnvRefines Δ ΔPwm ∧ GlobalWF (fun _ _ _ => True) Θ ΔPwm ∧ Causal ΔPwm ∧
    WellClocked (lowerΚ Κ RPwm specLight) ΔPwm ∧
    DriveWF (lowerΩ Ω RPwm specLight) (lowerΚ Κ RPwm specLight) ΔPwm (lowerβ β RPwm) ∧
    SingleDriver (lowerβ β RPwm) := by
  have nm : NoMention Δ ePwm := NoMention.of_globalWF Δ_typed rfl
  exact ⟨lower_envRefines wfPwm, lower_wf (Evidence.Monotone.of_const _) Δ_typed wfPwm,
    lower_causal wfPwm nm Δ_causal, lower_wellClocked wfPwm nm Δ_clocked,
    lower_driveWF wfPwm β_wf, (lower_singleDriver wfPwm β_wf β_single).2⟩

/-- Both profiles are admissible on the Nano: fit, and a solvable
    requirement list (one PWM line; SDA and SCL on one I²C unit). -/
def pwmProfile : DeviceOutputProfile := ⟨pwm8, [⟨⟨0⟩, .pwm, none, none⟩]⟩
def i2cProfile : DeviceOutputProfile :=
  ⟨i2cReg, [⟨⟨0⟩, .i2cSDA, none, some (0, .same)⟩, ⟨⟨1⟩, .i2cSCL, none, some (0, .same)⟩]⟩

theorem exH_admissible :
    Admissible Θ (.sem Brightness) HardwareCase.nano pwmProfile ∧
    Admissible Θ (.sem Brightness) HardwareCase.nano i2cProfile ∧
    -- the encoder alone says nothing about pins; the requirements alone say nothing about brightness
    ¬ Admissible Θ (.sem SwitchState) HardwareCase.nano pwmProfile := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## I — Model A and an implicit clock crossing, refuted executably -/

/-- Retargeting the light's accepted type to the duty type: the existing
    edge `light → oLight` is no longer well formed. -/
def ΩRetarget : OutputEnv := fun q => if q = oLight then some ⟨Q0, c0⟩ else Ω q

/-- An encoder read in another domain than its driver: the edge `e → p`
    fails `DriveWF` (the sink is in the output's clock), and the encoder
    body fails the domain judgment. -/
def ΚBad : ClockEnv := fun x => if x = ePwm then some ⟨1⟩ else Κ x

theorem exI :
    driveWFCheck ΩRetarget Κ Δ edges = false ∧
    driveWFCheck (lowerΩ Ω RPwm specLight) ΚBad ΔPwm ((ePwm, pPwm) :: edges) = false ∧
    wellClockedCheck ΚBad (decls ++ [⟨ePwm, ⟨Q0, []⟩, some (encoderBody (.sem Brightness) pwm8Tr light)⟩]) = false := by
  refine ⟨by decide, by decide, by decide⟩

theorem exI_theorem : ¬ DriveWF ΩRetarget Κ Δ β :=
  retarget_breaks_driveWF (Ω := Ω) (o := oLight) (d := light) (c := Brightness) (raw := Q0) (clock := c0) rfl rfl trivial

end BDL.Experiments.OutputRealizationEx
