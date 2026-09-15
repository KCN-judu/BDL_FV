import BDL.Validation.Hardware
import BDL.Experiments.OutputAlternatives

/-!
# Phase 7 — Arduino-Nano case study and counterexamples

The board is a finite declarative table (`nano`).  Requirements are derived
from Phase-6 output bindings through *device descriptions*
(`DeviceKind.requirements`), so the pipeline is

    OutputId → device kind → requirements → solve → assignment

and the BDL design (`Δ`, `Κ`, `Ω`, `β`) is never an argument of the solver.

Sections: §1 the Nano; §2 devices and the requirement pipeline; §3 the
motor-control example (SAT, with the produced mapping); §4 Counterexample A
(semantically valid, UNSAT) and B (same design SAT on a larger board);
§5 aliasing (C), exclusivity (D), bus sharing (E); §6 fixed pins (F),
resource removal (G), requirement strengthening (H); §7 timers — pin
capability alone is not enough; §8 explanation; §9 evidence sensitivity.
-/

namespace BDL.Experiments.HardwareCase
open BDL BDL.Reactive BDL.Clock BDL.Hardware BDL.Output BDL.Experiments.Output BDL.Experiments.Semantic BDL.Experiments.Clock BDL.Experiments.Reactive

/-! ## §1 The Arduino Nano (ATmega328P) as a table -/

def D (n : Nat) : ResourceId := ⟨n⟩
def A (n : Nat) : ResourceId := ⟨20 + n⟩

open Capability in
/-- Pin capabilities and the unit backing each: PWM timers 0/1/2, I2C unit 0,
    SPI unit 0, UART unit 0.  External interrupts INT0/INT1 on D2/D3 only. -/
def nanoResources : List Resource := [
  ⟨D 0,  [digitalIn, digitalOut, uartRX], [(uartRX, 0)]⟩,
  ⟨D 1,  [digitalIn, digitalOut, uartTX], [(uartTX, 0)]⟩,
  ⟨D 2,  [digitalIn, digitalOut, interrupt], []⟩,
  ⟨D 3,  [digitalIn, digitalOut, pwm, interrupt], [(pwm, 2)]⟩,
  ⟨D 4,  [digitalIn, digitalOut], []⟩,
  ⟨D 5,  [digitalIn, digitalOut, pwm], [(pwm, 0)]⟩,
  ⟨D 6,  [digitalIn, digitalOut, pwm], [(pwm, 0)]⟩,
  ⟨D 7,  [digitalIn, digitalOut], []⟩,
  ⟨D 8,  [digitalIn, digitalOut], []⟩,
  ⟨D 9,  [digitalIn, digitalOut, pwm], [(pwm, 1)]⟩,
  ⟨D 10, [digitalIn, digitalOut, pwm, spiSS], [(pwm, 1), (spiSS, 0)]⟩,
  ⟨D 11, [digitalIn, digitalOut, pwm, spiMOSI], [(pwm, 2), (spiMOSI, 0)]⟩,
  ⟨D 12, [digitalIn, digitalOut, spiMISO], [(spiMISO, 0)]⟩,
  ⟨D 13, [digitalIn, digitalOut, spiSCK], [(spiSCK, 0)]⟩,
  ⟨A 0,  [analogIn, digitalIn, digitalOut], []⟩,
  ⟨A 1,  [analogIn, digitalIn, digitalOut], []⟩,
  ⟨A 2,  [analogIn, digitalIn, digitalOut], []⟩,
  ⟨A 3,  [analogIn, digitalIn, digitalOut], []⟩,
  ⟨A 4,  [analogIn, digitalIn, digitalOut, i2cSDA], [(i2cSDA, 0)]⟩,
  ⟨A 5,  [analogIn, digitalIn, digitalOut, i2cSCL], [(i2cSCL, 0)]⟩,
  ⟨A 6,  [analogIn], []⟩,
  ⟨A 7,  [analogIn], []⟩]

/-- Buses are shared; everything else is exclusive. -/
def nano : Hardware := ⟨nanoResources, [.i2cSDA, .i2cSCL]⟩

/-- A larger mock board: the Nano plus six more PWM pins on three more timers. -/
def bigResources : List Resource := nanoResources ++ [
  ⟨D 40, [.digitalIn, .digitalOut, .pwm], [(.pwm, 3)]⟩, ⟨D 41, [.digitalIn, .digitalOut, .pwm], [(.pwm, 3)]⟩,
  ⟨D 42, [.digitalIn, .digitalOut, .pwm], [(.pwm, 4)]⟩, ⟨D 43, [.digitalIn, .digitalOut, .pwm], [(.pwm, 4)]⟩,
  ⟨D 44, [.digitalIn, .digitalOut, .pwm], [(.pwm, 5)]⟩, ⟨D 45, [.digitalIn, .digitalOut, .pwm], [(.pwm, 5)]⟩]
def big : Hardware := ⟨bigResources, [.i2cSDA, .i2cSCL]⟩

theorem nano_extends_big : nano.Extends big := by
  refine ⟨?_, by decide⟩
  -- the Nano prefix of `big` is found first
  have h : ∀ res ∈ nanoResources, big.find res.id = some res := by decide
  intro res hres
  exact ⟨res, List.mem_append_left _ hres, rfl, List.Subset.refl _, rfl, h res hres⟩

/-! ## §2 Devices: from a physical sink to requirements -/

/-- Declarative device interfaces.  A device *kind* says which capabilities
    a device of that kind needs; a binding of a sink to a kind generates
    requirements.  (Reusable components in the sense of §27; here a small
    closed vocabulary suffices.) -/
inductive DeviceKind where
  | pwmActuator          -- one PWM line
  | hBridgeChannel       -- PWM + direction
  | i2cSensor            -- bus membership: SDA + SCL, same unit
  | quadratureEncoder    -- two interrupt lines
  deriving DecidableEq, Repr

def rid (o : OutputId) (slot : Nat) : RequirementId := ⟨o.n * 10 + slot⟩

def DeviceKind.requirements (o : OutputId) : DeviceKind → Requirements
  | .pwmActuator => [⟨rid o 0, .pwm, none, none⟩]
  | .hBridgeChannel => [⟨rid o 0, .pwm, none, none⟩, ⟨rid o 1, .digitalOut, none, none⟩]
  | .i2cSensor => [⟨rid o 0, .i2cSDA, none, some (o.n, .same)⟩, ⟨rid o 1, .i2cSCL, none, some (o.n, .same)⟩]
  | .quadratureEncoder => [⟨rid o 0, .interrupt, none, none⟩, ⟨rid o 1, .interrupt, none, none⟩]

/-- The pipeline: bindings of sinks to device kinds ⇒ requirements. -/
def requirementsOf (bindings : List (OutputId × DeviceKind)) : Requirements :=
  bindings.flatMap fun p => p.2.requirements p.1

/-! ## §3 The motor-control example: four H-bridge channels and an I2C sensor -/

def m1 : OutputId := ⟨11⟩
def m2 : OutputId := ⟨12⟩
def m3 : OutputId := ⟨13⟩
def m4 : OutputId := ⟨14⟩
def imu : OutputId := ⟨15⟩

def motorBindings : List (OutputId × DeviceKind) :=
  [(m1, .hBridgeChannel), (m2, .hBridgeChannel), (m3, .hBridgeChannel), (m4, .hBridgeChannel), (imu, .i2cSensor)]
def motorReqs : Requirements := requirementsOf motorBindings

/-- **SAT on the Nano**, and the concrete mapping the solver produces — the
    IDE-shaped result.  (Requirements `110/111` are M1's PWM/DIR, etc.) -/
theorem motor_control_sat_on_nano : HardwareSatisfiable nano motorReqs := by decide

theorem motor_control_assignment :
    (solve nano motorReqs).map (List.map fun e => (e.1.id.n, e.2.n)) =
      some [(110, 3), (111, 0), (120, 5), (121, 1), (130, 6), (131, 2), (140, 9), (141, 4), (150, 24), (151, 25)] := by
  decide

/-! ## §4 Counterexample A — semantically valid, hardware-UNSAT; B — target-relative -/

/-- Seven independent PWM actuators: a design that passes every Phase 0–6
    check.  Seven sinks, seven drivers, seven inputs. -/
def sinks7 : List OutputId := [⟨21⟩, ⟨22⟩, ⟨23⟩, ⟨24⟩, ⟨25⟩, ⟨26⟩, ⟨27⟩]
def srcId (i : Nat) : DeclId := ⟨300 + i⟩
def drvId (i : Nat) : DeclId := ⟨310 + i⟩
def decls7 : List DesignDecl :=
  (List.range 7).flatMap fun i =>
    [⟨srcId i, ⟨MotorAngle, []⟩, none⟩, ⟨drvId i, ⟨MotorAngle, []⟩, some (.declRef (srcId i))⟩]
def Δ7 : DeclEnv := .ofList decls7
def Κ7 : ClockEnv := fun _ => Option.some actuatorClock
def Ω7 : OutputEnv := .ofList (sinks7.map fun o => (o, ⟨MotorAngle, actuatorClock⟩))
def β7 : DriveEnv := .ofList (((List.range 7).zip sinks7).map fun p => (drvId p.1, p.2))

theorem seven_pwm_design_semantically_valid :
    GlobalWF trivEv Dimension.Θdim Δ7 ∧ WellClocked Κ7 Δ7 ∧ Causal Δ7 ∧
    DriveWF Ω7 Κ7 Δ7 β7 ∧ SingleDriver β7 ∧ CompleteOutputs β7 sinks7 :=
  ⟨GlobalWF.ofList (by decide), WellClocked.ofList (by decide),
   Causal.ofList (fun d => if d.n ≥ 310 then 1 else 0) 2 (by intro d; show (if _ then 1 else 0) < 2; split <;> decide) (by decide),
   DriveWF.ofList (by decide), SingleDriver.ofList (by decide),
   fun o ho => by
     simp [sinks7] at ho
     rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
       | exact ⟨drvId 0, by decide⟩ | exact ⟨drvId 1, by decide⟩ | exact ⟨drvId 2, by decide⟩
       | exact ⟨drvId 3, by decide⟩ | exact ⟨drvId 4, by decide⟩ | exact ⟨drvId 5, by decide⟩
       | exact ⟨drvId 6, by decide⟩⟩

def reqs7 : Requirements := requirementsOf (sinks7.map fun o => (o, .pwmActuator))

/-- **`semantic_validity_does_not_imply_hardware_satisfiable`.**  Six PWM
    pins on the Nano; seven needed. -/
theorem seven_pwm_unsat_on_nano : ¬ HardwareSatisfiable nano reqs7 := by decide

/-- **`hardware_satisfiability_is_target_relative`** / **`board_swap_preserves_design_semantics`**:
    the *same* `reqs7` (hence the same design — the solver never sees `Δ`)
    is SAT on the larger board. -/
theorem seven_pwm_sat_on_big : HardwareSatisfiable big reqs7 := by decide

/-! ## §5 Aliasing (C), exclusivity (D), bus sharing (E) -/

def enc1 : OutputId := ⟨31⟩
def enc2 : OutputId := ⟨32⟩
def pwm6 : List OutputId := [⟨41⟩, ⟨42⟩, ⟨43⟩, ⟨44⟩, ⟨45⟩, ⟨46⟩]

/-- **Counterexample C — counts suffice, overlap kills.**  Two interrupt
    lines (the Nano has exactly two: D2, D3) and six PWM lines (exactly six:
    D3 … D11).  Every capability count is met; D3 is needed twice. -/
def aliasReqs : Requirements := requirementsOf ((enc1, .quadratureEncoder) :: pwm6.map fun o => (o, .pwmActuator))

theorem capability_counts_suffice :
    (nanoResources.filter fun r => .interrupt ∈ r.caps).length = 2 ∧
    (nanoResources.filter fun r => .pwm ∈ r.caps).length = 6 ∧
    (aliasReqs.filter fun q => q.cap = .interrupt).length = 2 ∧
    (aliasReqs.filter fun q => q.cap = .pwm).length = 6 := by decide

theorem multifunction_overlap_unsat : ¬ HardwareSatisfiable nano aliasReqs := by decide

/-- **Counterexample D — exclusive resources cannot be shared.**  Two PWM
    requirements pinned to D3. -/
def r1D3 : Requirement := ⟨⟨1⟩, .pwm, some (D 3), none⟩
def r2D3 : Requirement := ⟨⟨2⟩, .pwm, some (D 3), none⟩
def twoOnD3 : Requirements := [r1D3, r2D3]
theorem exclusive_cannot_share : ¬ HardwareSatisfiable nano twoOnD3 ∧ ¬ Compatible nano (r1D3, D 3) (r2D3, D 3) := by
  refine ⟨by decide, ?_⟩
  intro h
  have := (h.1 rfl).2
  simp [nano, r1D3] at this

/-- **Counterexample E / `shared_bus_allocation_accepted`**: two I2C sensors
    share A4/A5 — allocation is not `allDifferent`. -/
def imu2 : OutputId := ⟨16⟩
def twoSensors : Requirements := requirementsOf [(imu, .i2cSensor), (imu2, .i2cSensor)]
theorem shared_bus_allocation_accepted :
    HardwareSatisfiable nano twoSensors ∧
    (solve nano twoSensors).map (List.map fun e => (e.1.id.n, e.2.n)) = some [(150, 24), (151, 25), (160, 24), (161, 25)] := by
  exact ⟨by decide, by decide⟩

/-! ## §6 Fixed pins (F), resource removal (G), strengthening (H) -/

/-- **Counterexample F / `fixed_assignment_respected`**: an encoder needs
    D2 and D3; pinning a PWM line to D3 by hand makes the design UNSAT. -/
def encPlusPwm : Requirements := requirementsOf [(enc1, .quadratureEncoder), (m1, .pwmActuator)]
def encPlusPwmFixed : Requirements := requirementsOf [(enc1, .quadratureEncoder)] ++ [⟨rid m1 0, .pwm, some (D 3), none⟩]

theorem fixed_pin_turns_unsat : HardwareSatisfiable nano encPlusPwm ∧ ¬ HardwareSatisfiable nano encPlusPwmFixed := by
  exact ⟨by decide, by decide⟩

/-- A manual choice that *is* consistent is respected by the solver. -/
def m1OnD5 : Requirements := [⟨rid m1 0, .pwm, some (D 5), none⟩, ⟨rid m1 1, .digitalOut, none, none⟩]
theorem fixed_assignment_respected :
    (solve nano m1OnD5).map (List.map fun e => (e.1.id.n, e.2.n)) = some [(110, 5), (111, 0)] := by decide

/-- **Counterexample G — removing a resource invalidates an allocation.**
    Drop D3 from the board: the motor assignment (which used D3) is no longer
    valid, and the reduced board is UNSAT for the aliasing design's
    interrupt half. -/
def nanoNoD3 : Hardware := ⟨nanoResources.filter fun r => r.id ≠ D 3, [.i2cSDA, .i2cSCL]⟩

/-- The mapping the solver produced for the motor example, as an explicit assignment. -/
def motorAssign : Assignment :=
  [(⟨rid m1 0, .pwm, none, none⟩, D 3), (⟨rid m1 1, .digitalOut, none, none⟩, D 0),
   (⟨rid m2 0, .pwm, none, none⟩, D 5), (⟨rid m2 1, .digitalOut, none, none⟩, D 1),
   (⟨rid m3 0, .pwm, none, none⟩, D 6), (⟨rid m3 1, .digitalOut, none, none⟩, D 2),
   (⟨rid m4 0, .pwm, none, none⟩, D 9), (⟨rid m4 1, .digitalOut, none, none⟩, D 4),
   (⟨rid imu 0, .i2cSDA, none, some (imu.n, .same)⟩, A 4), (⟨rid imu 1, .i2cSCL, none, some (imu.n, .same)⟩, A 5)]

theorem motor_solve_eq : solve nano motorReqs = some motorAssign := by decide

theorem resource_removal_invalidates :
    PartialValid nano motorAssign ∧ ¬ PartialValid nanoNoD3 motorAssign ∧
    ¬ HardwareSatisfiable nanoNoD3 (requirementsOf [(enc1, .quadratureEncoder)]) := by
  exact ⟨(solve_sound motor_solve_eq).1, by decide, by decide⟩

/-- **Counterexample H — strengthening a requirement invalidates.**  A
    direction line on D4 is fine; asking D4 for PWM is not. -/
theorem requirement_strengthening_invalidates :
    ReqOK nano ⟨⟨7⟩, .digitalOut, none, none⟩ (D 4) ∧ ¬ ReqOK nano ⟨⟨7⟩, .pwm, none, none⟩ (D 4) := by
  refine ⟨by decide, ?_⟩
  intro h
  have := h.1
  simp [Supports, nano, Hardware.find, nanoResources, D] at this

/-! ## §7 Timers — pin capability alone is not sufficient -/

/-- Four PWM channels that must run on *independent timers* (pairwise
    distinct units).  Six PWM-capable pins, but only three timers. -/
def fourIndependentPwm : Requirements :=
  [⟨⟨1⟩, .pwm, none, some (7, .distinct)⟩, ⟨⟨2⟩, .pwm, none, some (7, .distinct)⟩,
   ⟨⟨3⟩, .pwm, none, some (7, .distinct)⟩, ⟨⟨4⟩, .pwm, none, some (7, .distinct)⟩]
def fourAnyPwm : Requirements :=
  [⟨⟨1⟩, .pwm, none, none⟩, ⟨⟨2⟩, .pwm, none, none⟩, ⟨⟨3⟩, .pwm, none, none⟩, ⟨⟨4⟩, .pwm, none, none⟩]

theorem timers_matter :
    HardwareSatisfiable nano fourAnyPwm ∧ ¬ HardwareSatisfiable nano fourIndependentPwm ∧
    HardwareSatisfiable big fourIndependentPwm := by
  exact ⟨by decide, by decide, by decide⟩

/-- Grouped peripheral: TX and RX of one UART must come from the same unit —
    on a two-UART mock board the solver keeps them together. -/
def twoUart : Hardware := ⟨[
  ⟨D 0, [.uartRX], [(.uartRX, 0)]⟩, ⟨D 1, [.uartTX], [(.uartTX, 0)]⟩,
  ⟨D 2, [.uartRX], [(.uartRX, 1)]⟩, ⟨D 3, [.uartTX], [(.uartTX, 1)]⟩], []⟩
def uartReq : Requirements := [⟨⟨1⟩, .uartTX, some (D 3), some (9, .same)⟩, ⟨⟨2⟩, .uartRX, none, some (9, .same)⟩]
theorem grouped_peripheral_same_unit :
    (solve twoUart uartReq).map (List.map fun e => (e.1.id.n, e.2.n)) = some [(1, 3), (2, 2)] := by decide

/-! ## §8 Explanation -/

/-- For the seven-PWM design the first dead end is the seventh actuator,
    blocked on every PWM pin by an earlier one. -/
theorem seven_pwm_explanation :
    (diagnose nano reqs7).map (fun ex => match ex with
      | .blocked req bl => (req.id.n, bl.map fun p => (p.1.n, p.2.n))
      | .noCapableResource req => (req.id.n, [])) =
    some (270, [(3, 210), (5, 220), (6, 230), (9, 240), (10, 250), (11, 260)]) := by
  decide

/-- A requirement nothing on the board supports is reported as such. -/
theorem no_capable_resource_explanation :
    (diagnose nano [⟨⟨1⟩, .pwm, some (D 4), none⟩]).map (fun ex => match ex with
      | .noCapableResource req => req.id.n | .blocked req _ => req.id.n + 1000) = some 1 := by
  decide

/-! ## §9 Feasibility is environment-sensitive evidence -/

/-- Six PWM actuators are SAT; adding one more (a *monotone* design
    extension — a new declaration, a new sink, a new requirement) makes the
    design UNSAT.  So "deployable on the Nano" is not evidence that survives
    design refinement: it is deployment-sensitive, not `Evidence.Monotone`. -/
def reqs6 : Requirements := requirementsOf ((sinks7.take 6).map fun o => (o, .pwmActuator))
theorem feasibility_not_monotone_under_extension :
    HardwareSatisfiable nano reqs6 ∧ reqs6 <+: reqs7 ∧ ¬ HardwareSatisfiable nano reqs7 :=
  ⟨by decide, by decide, seven_pwm_unsat_on_nano⟩

end BDL.Experiments.HardwareCase
