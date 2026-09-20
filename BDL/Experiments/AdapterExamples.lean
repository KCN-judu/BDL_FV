import BDL.Surface.DeviceClock
import BDL.Experiments.OutputRealizationExamples

/-!
# Phase 15 — executed examples for the adapter boundary and the device clock

Over the Phase-14 design (`OutputRealizationExamples`: the light at 40 % and
41 %, realized by 8-bit PWM):

* A — the `duty8` policy accepts the raw duty 102 and the adapter sets the
  line; the line then carries 102 (`line_last_accepted`).
* B — an out-of-range command (a dial at 120 % → duty 306) is refused under
  `duty8` and the line holds its previous value; under `clamp8` the same
  command sets 255.  Two policies, one command trace, two operation traces.
* C — a tick at which the output's clock is inactive leaves the line where
  it was (`held`).
* D — the device clock: the PWM sink moved to a slower device domain
  through the explicit `sync`; at the device's first activation the line
  carries the initial representation, afterwards the command specified at
  the last activation of the output's clock strictly before.
* E — a stateful adapter that is *not* one: slew-rate limiting as an
  ordinary upstream declaration with `delay`, realized by the same pure
  encoder — the raw trace ramps `0, 25, 51, 76, 102` toward 40 % while the
  design itself, not the realization, holds the state.
-/

namespace BDL.Experiments.AdapterEx
open BDL BDL.Reactive BDL.Clock BDL.Output BDL.Stdlib BDL.Provision BDL.OutputRealization BDL.Adapter BDL.DeviceClock
open BDL.Experiments.OutputRealizationEx

/-! ## A/B — policies over one command trace -/

/-- A dial at 120 %: brightness 120, encoded to duty 306, out of the 8-bit range. -/
def Iover : Input := fun d _ => if d = dial then .sem Brightness (.nat 120) else .nat 0

theorem exA_policies :
    duty8.accept (.nat 102) = some (.nat 102) ∧
    duty8.accept (.nat 306) = none ∧
    clamp8.accept (.nat 306) = some (.nat 255) ∧
    Policy.total.accept (.nat 306) = some (.nat 306) ∧
    level.accept (.bool true) = some (.bool true) ∧
    -- the raw command itself does not depend on the policy: the lowered sink carries 102 / 306
    (match evalF ΔPwm I 64 0 [] (.declRef ePwm) with | some (.nat n) => n | _ => 0) = 102 ∧
    (match evalF ΔPwm Iover 64 0 [] (.declRef ePwm) with | some (.nat n) => n | _ => 0) = 306 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> decide

/-- The always-active schedule: every tick is an activation of `c0`. -/
def S : Sched := Sched.always

/-- The raw command 102 is specified at tick 0 under `I`, and 306 under `Iover`. -/
theorem raw102 : RawCommand S Δ I Ω β RPwm 0 (.nat 102) := by
  refine ⟨specLight, .sem Brightness (.nat 40), rfl, ⟨light, specLight, rfl, rfl, ?_⟩, rfl⟩
  exact (single_domain_embedding _).mpr (Ev.of_evalF (Δ := Δ) (I := I) (fuel := 64) rfl)

theorem raw306 : RawCommand S Δ Iover Ω β RPwm 0 (.nat 306) := by
  refine ⟨specLight, .sem Brightness (.nat 120), rfl, ⟨light, specLight, rfl, rfl, ?_⟩, rfl⟩
  exact (single_domain_embedding _).mpr (Ev.of_evalF (Δ := Δ) (I := Iover) (fuel := 64) rfl)

/-- A: the adapter sets 102 and the line carries 102. -/
theorem exA_set :
    AdapterOp S Δ I Ω β RPwm specLight duty8 0 (.set (.nat 102)) ∧
    Line S Δ I Ω β RPwm specLight duty8 (.nat 0) 0 (.nat 102) :=
  have h : AdapterOp S Δ I Ω β RPwm specLight duty8 0 (.set (.nat 102)) := .set rfl rfl raw102 rfl
  ⟨h, line_last_accepted h⟩

/-- B: the over-range command is refused under `duty8` (the line holds its
    start value 0), set to 255 under `clamp8`, set to 306 under the total
    policy — one command, three operations. -/
theorem exB_refusal :
    AdapterOp S Δ Iover Ω β RPwm specLight duty8 0 .refused ∧
    Line S Δ Iover Ω β RPwm specLight duty8 (.nat 0) 0 (.nat 0) ∧
    AdapterOp S Δ Iover Ω β RPwm specLight clamp8 0 (.set (.nat 255)) ∧
    AdapterOp S Δ Iover Ω β RPwm specLight Policy.total 0 (.set (.nat 306)) :=
  have hr : AdapterOp S Δ Iover Ω β RPwm specLight duty8 0 .refused := .refused rfl rfl raw306 rfl
  ⟨hr, .hold0 hr (fun _ h => nomatch h), .set rfl rfl raw306 rfl, .set rfl rfl raw306 rfl⟩

/-! ## C — an inactive tick holds the line -/

/-- The output's clock activates on even ticks only. -/
def S2 : Sched := Sched.periodic (fun _ => 2)

theorem exC_held :
    S2 c0 1 = false ∧
    AdapterOp S2 Δ I Ω β RPwm specLight duty8 1 .held ∧
    ∀ m, Line S2 Δ I Ω β RPwm specLight duty8 (.nat 0) 0 m → Line S2 Δ I Ω β RPwm specLight duty8 (.nat 0) 1 m :=
  ⟨rfl, .held rfl rfl, fun _ hl => line_holds_when_inactive rfl rfl hl⟩

/-! ## D — the explicit device clock -/

def c1 : ClockId := ⟨1⟩
/-- The initial representation: 0 % — a pure closed literal. -/
def init0 : InitRep := ⟨lit Dim.zero 0, .nat 0, trivial, Ev.lit _ _⟩
def ΔSyncPwm : DeclEnv := lowerSyncΔ Δ RPwm specLight init0
/-- The device domain `c1` activates on odd ticks, the output's clock `c0` on
    even ticks. -/
def Sdev : Sched := fun c t => if c = c0 then t % 2 = 0 else t % 2 = 1

def runDev (t : Nat) (e : Expr) : Option Value := mevalF Sdev ΔSyncPwm I 64 c1 t [] e

theorem exD_device_clock :
    -- structure: the encoder in the device domain, the sink there too
    (lowerSyncΚ Κ RPwm c1) ePwm = some c1 ∧ lowerSyncΩ Ω RPwm c1 pPwm = some ⟨Q0, c1⟩ ∧
    ΔSyncPwm.realizationOf ePwm = some (.app pwm8Tr (.sync c0 (lit Dim.zero 0) (.rep (.declRef light)))) ∧
    -- at device tick 1 the output's clock activated at 0 (dial 40 → 102)
    (match runDev 1 (.declRef ePwm) with | some (.nat n) => n | _ => 999) = 102 ∧
    -- at device tick 3 the last activation of `c0` before 3 is tick 2 (dial 42 → 107)
    (match runDev 3 (.declRef ePwm) with | some (.nat n) => n | _ => 999) = 107 ∧
    -- the sampled command: what `prevAct` names
    prevAct Sdev c0 1 = some 0 ∧ prevAct Sdev c0 3 = some 2 ∧ prevAct Sdev c0 0 = none := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl⟩ <;> decide

/-- Before the output's clock ever activated (a device tick 0 under a
    schedule where `c0` first activates at tick 1), the sink carries the
    initial representation through the encoder: duty `0`. -/
def SdevLate : Sched := fun c t => if c = c0 then t % 2 = 1 else t % 2 = 0

theorem exD_initial :
    prevAct SdevLate c0 0 = none ∧
    (match mevalF SdevLate ΔSyncPwm I 64 c1 0 [] (.declRef ePwm) with | some (.nat n) => n | _ => 999) = 0 := by
  refine ⟨rfl, ?_⟩; decide

/-- The device-clocked lowering is well formed, causal (no new instantaneous
    edge), well clocked in the device domain and single-driver. -/
theorem exD_structure :
    EnvRefines Δ ΔSyncPwm ∧ GlobalWF (fun _ _ _ => True) Θ ΔSyncPwm ∧ Causal ΔSyncPwm ∧
    WellClocked (lowerSyncΚ Κ RPwm c1) ΔSyncPwm ∧
    DriveWF (lowerSyncΩ Ω RPwm c1) (lowerSyncΚ Κ RPwm c1) ΔSyncPwm (lowerβ β RPwm) ∧
    SingleDriver (lowerβ β RPwm) := by
  have nm : NoMention Δ ePwm := NoMention.of_globalWF Δ_typed rfl
  exact ⟨lowerSync_envRefines wfPwm, lowerSync_wf (Evidence.Monotone.of_const _) Δ_typed wfPwm (infer_sound (by decide)),
    lowerSync_causal Δ_causal, lowerSync_wellClocked wfPwm nm Δ_clocked,
    lowerSync_driveWF wfPwm β_wf, (lowerSync_singleDriver wfPwm β_wf β_single).2⟩

/-! ## E — slew-rate limiting is behaviour, not realization -/

/-- The slew-limited brightness: `limited := if delay 0 limited + 10 < dial
    then delay 0 limited + 10 else dial` — ordinary state upstream of the
    logical output, visible to the designer and the simulation. -/
def limited : DeclId := ⟨6⟩
def stepUp : Expr :=
  app2 (.prim (.add Dim.zero)) (.delay (lit Dim.zero 0) (.rep (.declRef limited))) (lit Dim.zero 10)
def slewBody : Expr :=
  .mk Brightness (.app (app2 (.prim (.ite Q0)) (ltE Dim.zero stepUp (.rep (.declRef dial))) stepUp) (.rep (.declRef dial)))

def slewDecls : List DesignDecl := [
  ⟨dial, ⟨.sem Brightness, []⟩, none⟩,
  ⟨light, ⟨.sem Brightness, []⟩, some (.mk Brightness (.rep (.declRef dial)))⟩,
  ⟨sw, ⟨.sem SwitchState, []⟩, none⟩,
  ⟨ang, ⟨.sem ServoAngle, []⟩, none⟩,
  ⟨spd, ⟨.sem MotorSpeed, []⟩, none⟩,
  ⟨limited, ⟨.sem Brightness, []⟩, some slewBody⟩]
def ΔSlew : DeclEnv := .ofList slewDecls
def βSlew : DriveEnv := .ofList [(limited, oLight)]
def RSlew : Realization := ⟨oLight, limited, pPwm, ePwm, pwm8⟩
def ΔSlewPwm : DeclEnv := lowerΔ ΔSlew RSlew specLight
/-- The dial sits at 40 % from tick 0. -/
def I40 : Input := fun d _ => if d = dial then .sem Brightness (.nat 40) else .nat 0

def runSlew (t : Nat) (e : Expr) : Option Value := evalF ΔSlewPwm I40 64 t [] e

theorem exE_slew :
    -- the design is well formed and causal (the self-reference is under `delay`)
    GlobalWF (fun _ _ _ => True) Θ ΔSlew ∧ Causal ΔSlew ∧ DriveWF Ω Κ ΔSlew βSlew ∧
    WF Θ ΔSlew Ω βSlew Κ RSlew specLight ∧
    -- the logical output ramps: 10, 20, 30, 40, 40 (product-observable)
    (match runSlew 0 (.declRef limited) with | some (.sem _ (.nat n)) => n | _ => 999) = 10 ∧
    (match runSlew 1 (.declRef limited) with | some (.sem _ (.nat n)) => n | _ => 999) = 20 ∧
    (match runSlew 3 (.declRef limited) with | some (.sem _ (.nat n)) => n | _ => 999) = 40 ∧
    (match runSlew 4 (.declRef limited) with | some (.sem _ (.nat n)) => n | _ => 999) = 40 ∧
    -- and the same pure encoder produces the ramped raw trace: 25, 51, 102
    (match runSlew 0 (.declRef ePwm) with | some (.nat n) => n | _ => 999) = 25 ∧
    (match runSlew 1 (.declRef ePwm) with | some (.nat n) => n | _ => 999) = 51 ∧
    (match runSlew 3 (.declRef ePwm) with | some (.nat n) => n | _ => 999) = 102 := by
  refine ⟨GlobalWF.ofList (by decide),
    Causal.ofList (fun d => if d = light ∨ d = limited then 1 else 0) 2 (by intro d; split <;> omega) (by decide),
    DriveWF.ofList (by decide),
    WF.of_driveWF (DriveWF.ofList (by decide)) rfl rfl rfl rfl (by decide) (infer_sound (by decide)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end BDL.Experiments.AdapterEx
