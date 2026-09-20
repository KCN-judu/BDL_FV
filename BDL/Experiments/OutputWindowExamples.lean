import BDL.Surface.OutputWindow
import BDL.Experiments.AdapterExamples

/-!
# Phase 17 — the occurrence-preserving realization, executed

Over Phase 14's design (the light at `40 + t` %, realized by 8-bit PWM,
output clock `c0` every tick) with a device domain `dc` on even ticks:

* A — **state vs occurrence**: at device tick 2 the sampled lowering
  (`lowerSync`) carries duty `104` (the command at tick 1); the window
  lowering carries `[102, 104]` (the commands at ticks 0 and 1); at tick
  4, `[107, 109]`.  Two output ticks, two commands, none collapsed.
* B — **multiplicity and order**: a dial that repeats a value gives a
  batch with the value twice, in tick order.
* C — **capacity**: a device on every second tick needs `cap = 2`
  (`CapacitySufficient`, decided); one on every third tick with `cap = 2`
  is refused — deployment infeasibility, not a semantic fault.
* D — **the adapter batch**: `[102, 306]` under `duty8` is
  `[set 102, refused]` and the line ends at 102.
* E — **the paired axis, batched**: two identity window realizations of
  one output carry equal batches at every device tick.
* F — **the structure**: refinement, global well-formedness, causality,
  clocking, drive edges and single-driver, instantiated.
-/

namespace BDL.Experiments.OutputWindowEx
open BDL BDL.Reactive BDL.Clock BDL.Output BDL.Stdlib BDL.Provision BDL.OutputRealization BDL.Adapter
open BDL.DeviceClock BDL.OutputWindow BDL.Validation.Capacity
open BDL.Experiments.OutputRealizationEx

def dc : ClockId := ⟨1⟩
/-- The output's clock every tick, the device on even ticks. -/
def Sw : Sched := fun c t => if c = c0 then true else t % 2 = 0
def wids : WIds := ⟨⟨20⟩, ⟨21⟩, ⟨22⟩, ⟨23⟩, ⟨24⟩⟩

def ΔW : DeclEnv := lowerWindowΔ Δ RPwm specLight wids
def ΩW : OutputEnv := lowerWindowΩ Ω RPwm dc
def βW : DriveEnv := lowerWindowβ β RPwm wids
def ΚW : ClockEnv := lowerWindowΚ Κ RPwm specLight dc wids

theorem freshW : Fresh Δ RPwm wids := ⟨by decide, by decide⟩

def natList? : Value → Option (List Nat)
  | .list vs => go vs
  | _ => none
where
  go : List Value → Option (List Nat)
    | [] => some []
    | .nat n :: vs => (go vs).map (n :: ·)
    | _ => none

def runW (t : Nat) : Option (List Nat) := (mevalF Sw ΔW I 200 dc t [] (.declRef wids.window)).bind natList?

/-- The sampled lowering, for comparison, with the same device domain. -/
def ΔS : DeclEnv := lowerSyncΔ Δ RPwm specLight ⟨lit Dim.zero 0, .nat 0, trivial, Ev.lit _ _⟩
def runS (t : Nat) : Option Nat := (mevalF Sw ΔS I 200 dc t [] (.declRef ePwm)).bind Value.toNat?

/-! ## A — state vs occurrence -/

theorem exA_window_vs_sample :
    runW 2 = some [102, 104] ∧ runW 4 = some [107, 109] ∧ runW 0 = some [] ∧
    runS 2 = some 104 ∧ runS 4 = some 109 ∧
    windowTicks Sw c0 dc 2 = [0, 1] ∧ windowTicks Sw c0 dc 4 = [2, 3] ∧ prevAct Sw c0 2 = some 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## B — multiplicity and order -/

/-- A dial that holds 40 for two ticks, then 42. -/
def Irep : Input := fun d t => if d = dial then .sem Brightness (.nat (if t < 2 then 40 else 42)) else I d t
def runWrep (t : Nat) : Option (List Nat) := (mevalF Sw ΔW Irep 200 dc t [] (.declRef wids.window)).bind natList?

theorem exB_multiplicity_order :
    runWrep 2 = some [102, 102] ∧ runWrep 4 = some [107, 107] := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## C — capacity -/

def Sw3 : Sched := fun c t => if c = c0 then true else t % 3 = 0

theorem exC_capacity :
    CapacitySufficient Sw c0 dc 2 12 ∧ ¬ CapacitySufficient Sw3 c0 dc 2 12 ∧ CapacitySufficient Sw3 c0 dc 3 12 := by
  refine ⟨by decide, by decide, by decide⟩

/-- The bound theorem, instantiated: every batch up to tick 12 has at most
    two commands. -/
theorem exC_bounded (t : Nat) (ht : t ≤ 12) (f : Nat → Value) :
    ((windowTicks Sw c0 dc t).map (RPwm.E.transfer ∘ f)).length ≤ 2 :=
  lowerWindow_bounded (R := RPwm) (spec := specLight) exC_capacity.1 ht

/-! ## D — the adapter batch -/

theorem exD_batch :
    batchOps duty8 [.nat 102, .nat 306] = [.set (.nat 102), .refused] ∧
    Value.beq (lineAfterBatch duty8 (.nat 0) [.nat 102, .nat 306]) (.nat 102) = true ∧
    Value.beq (lineAfterBatch clamp8 (.nat 0) [.nat 102, .nat 306]) (.nat 255) = true := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## E — the paired axis, batched -/

/-- The representation trace of the light under `I`: `40 + t`. -/
theorem traceI : RepTrace Sw Δ I Ω β RPwm specLight (fun t => .nat (40 + t)) := by
  intro u
  refine ⟨⟨_, rfl⟩, light, specLight, rfl, rfl, ?_⟩
  exact .refRealized rfl (.mk (.rep (.refInput rfl)))

def idEnc : Encoder where
  rep := Q0
  raw := Q0
  encode := .lam Q0 (.var 0)
  transfer := id
  rep_semFree := trivial
  rep_data := trivial
  raw_semFree := trivial
  raw_data := trivial
  encode_pure := trivial
  computes := by rintro v ⟨n, rfl⟩; exact .appClo .lam (.refInput rfl) (.var rfl)

def RM2 : Realization := ⟨oLight, light, ⟨30⟩, ⟨31⟩, idEnc⟩
def RM3 : Realization := ⟨oLight, light, ⟨32⟩, ⟨33⟩, idEnc⟩

theorem trace2 : RepTrace Sw Δ I Ω β RM2 specLight (fun t => .nat (40 + t)) := by
  intro u; refine ⟨⟨_, rfl⟩, light, specLight, rfl, rfl, ?_⟩; exact .refRealized rfl (.mk (.rep (.refInput rfl)))
theorem trace3 : RepTrace Sw Δ I Ω β RM3 specLight (fun t => .nat (40 + t)) := by
  intro u; refine ⟨⟨_, rfl⟩, light, specLight, rfl, rfl, ?_⟩; exact .refRealized rfl (.mk (.rep (.refInput rfl)))

/-- Two motors, one axis, every command: the two batches at every device
    tick are pointwise the two transfers of one value
    (`paired_batches_of_one_window`); with identity encoders, equal. -/
theorem exE_paired (t : Nat) :
    (windowTicks Sw specLight.clock dc t).map (RM2.E.transfer ∘ fun t => Value.nat (40 + t)) =
      (windowTicks Sw specLight.clock dc t).map (RM3.E.transfer ∘ fun t => Value.nat (40 + t)) := rfl

theorem exE_paired_theorem (t : Nat) :
    ∀ i (hi : i < (windowTicks Sw specLight.clock dc t).length), ∃ v,
      ((windowTicks Sw specLight.clock dc t).map (RM2.E.transfer ∘ fun t => Value.nat (40 + t)))[i]'(by simpa using hi) =
        RM2.E.transfer v ∧
      ((windowTicks Sw specLight.clock dc t).map (RM3.E.transfer ∘ fun t => Value.nat (40 + t)))[i]'(by simpa using hi) =
        RM3.E.transfer v :=
  (paired_batches_of_one_window β_single rfl trace2 trace3 t).2

/-! ## F — the structure -/

theorem nmW : ∀ x ∈ RPwm.e :: wids.list, NoMention Δ x :=
  fun x hx => NoMention.of_globalWF Δ_typed (by
    simp only [WIds.list, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)

theorem hIW : ∀ x ∈ RPwm.e :: wids.list, ∀ d t, Avoids x (I d t) := by
  intro x _ d t
  unfold I
  split
  · exact .sem (.nat _)
  · split
    · exact .sem (.bool _)
    · split
      · exact .sem (.nat _)
      · split
        · exact .sem (.pair (.bool _) (.nat _))
        · exact .nat _

/-- **The correspondence theorem, instantiated**: the sink carries the
    window of PWM commands at every tick. -/
theorem exF_correspondence (t : Nat) :
    PhysicalOutput Sw ΔW I ΩW βW RPwm.p t (.list ((windowTicks Sw c0 dc t).map (RPwm.E.transfer ∘ fun t => Value.nat (40 + t)))) :=
  lowerWindow_correspondence freshW wfPwm β_single nmW hIW traceI t

theorem exF_structure :
    EnvRefines Δ ΔW ∧ GlobalWF (fun _ _ _ => True) Θ ΔW ∧ Causal ΔW ∧ WellClocked ΚW ΔW ∧
    DriveWF ΩW ΚW ΔW βW ∧ SingleDriver βW :=
  ⟨lowerWindow_envRefines freshW wfPwm, lowerWindow_wf (Evidence.Monotone.of_const _) freshW Δ_typed wfPwm,
   lowerWindow_causal freshW wfPwm nmW Δ_causal, lowerWindow_wellClocked freshW wfPwm nmW Δ_clocked,
   lowerWindow_driveWF freshW wfPwm β_wf, (lowerWindow_singleDriver freshW wfPwm β_wf β_single).2⟩

/-- Behaviour unchanged: the light itself is the same in the window design. -/
theorem exF_transparent (t : Nat) :
    MEv Sw ΔW I c0 t [] (.declRef light) (.sem Brightness (.nat (40 + t))) :=
  (lowerWindow_decl_transparent freshW wfPwm nmW hIW (by decide)).mp (.refRealized rfl (.mk (.rep (.refInput rfl))))

end BDL.Experiments.OutputWindowEx
