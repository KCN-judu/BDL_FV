import BDL.Behavior.Producer
import BDL.Experiments.ConceptRef
import BDL.Experiments.ProducerAlternatives

/-!
# Phase 20 — one producer per concept, on the development's own designs

The invariant `ProducerUnique` (`Core/Producer`) applied to the designs
Phase 19 found to have several producers, each rewritten in the form the
invariant asks for — every candidate its own concept, the resolver the one
origin — with the same trace, executed:

* Phase 6's explicit composition `base, corr, final : MotorAngle` becomes
  `base : BaseAngle`, `corr : Correction`, `final : MotorAngle`
  (`composition_unique`); its priority design `emergencyTarget,
  normalTarget, selected : MotorAngle` becomes `EmergencyTarget`,
  `NormalTarget`, one `selected` (`priority_unique`).  Same motor value.
* Phase 14's `light := mk Brightness (rep dial)` becomes the wire
  `light := dial` (`rewrap_unique`).  Same light value.
* Phase 8a's lamp: with `Bright` shared by two dimmers the flattened design
  is not unique (`lamp_not_unique`); with `Bright` instance-private it is,
  by the checkable boundary rule (`private_lamp_unique`, one `decide`).
* The concept reference: in the sensor design `hot` may read `Temperature`
  by concept, and elaborates to `declRef temp` (`read_by_concept`); the
  value of `Temperature` at a tick is a function (`temperature_value`).
* A transport is a relay: the explicit initial value of a `sync` is its
  default, not an origin (`transport_unique`).
* The drive edge: the unique producer is not the driver — Phase 19's
  `one_origin_two_outputs` stands (`driver_independent`).
-/

namespace BDL.Experiments.ProducerUnique
open BDL BDL.Reactive BDL.Clock BDL.Output BDL.Stdlib BDL.ConceptRef
open BDL.Experiments.Output (actuatorClock motor Ωmotor baseAngle corrAngle finalAngle ΚA ΔB βB emergency emergencyTarget normalTarget selected Δsel βsel Κsel Isel readMotor)
open BDL.Experiments.Semantic (cMotor trivEv)
open BDL.Experiments.Clock (S₂)

/-! ## Phase 6 rewritten -/

def MotorAngle : Ty := .sem cMotor
def cBase : SemanticId := ⟨401⟩
def cCorr : SemanticId := ⟨402⟩
def cEm : SemanticId := ⟨403⟩
def cNorm : SemanticId := ⟨404⟩
def Θ6 : ConceptEnv := fun s =>
  if s = cMotor ∨ s = cBase ∨ s = cCorr ∨ s = cEm ∨ s = cNorm then some (.q Dim.Angle) else none

def ΔB' : DeclEnv := .ofList [
  ⟨baseAngle, ⟨.sem cBase, []⟩, none⟩, ⟨corrAngle, ⟨.sem cCorr, []⟩, none⟩,
  ⟨finalAngle, ⟨MotorAngle, []⟩, some
    (.mk cMotor (.app (.app (.prim (.add Dim.Angle)) (.rep (.declRef baseAngle))) (.rep (.declRef corrAngle))))⟩]

def I6 : Input := fun d _ =>
  if d = baseAngle then .sem cMotor (.nat 10) else if d = corrAngle then .sem cMotor (.nat 5) else .nat 0
def I6' : Input := fun d _ =>
  if d = baseAngle then .sem cBase (.nat 10) else if d = corrAngle then .sem cCorr (.nat 5) else .nat 0

def readAngle (Δ : DeclEnv) (I : Input) (d : DeclId) : Option Nat :=
  (evalF Δ I 32 0 [] (.declRef d)).bind fun v => match v with | .sem _ (.nat n) => some n | _ => none

/-- **Composition, one producer**: Phase 6's `ΔB` has two origins of
    `MotorAngle`; with the contributors as their own concepts the design is
    producer-unique, well formed, drives the motor through the same edge,
    and computes the same angle. -/
theorem composition_unique :
    ¬ ProducerUnique ΔB ∧ ProducerUnique ΔB' ∧ GlobalWF trivEv Θ6 ΔB' ∧
    DriveWF Ωmotor ΚA ΔB' βB ∧ SingleDriver βB ∧
    readAngle ΔB I6 finalAngle = some 15 ∧ readAngle ΔB' I6' finalAngle = some 15 := by
  refine ⟨BDL.Experiments.Producers.phase6_not_mkUnique, ProducerUnique.ofList (by decide),
    GlobalWF.ofList (by decide), DriveWF.ofList (by decide), SingleDriver.ofList (by decide), by decide, by decide⟩

def Δsel' : DeclEnv := .ofList [
  ⟨emergency, ⟨.bool, []⟩, none⟩, ⟨emergencyTarget, ⟨.sem cEm, []⟩, none⟩, ⟨normalTarget, ⟨.sem cNorm, []⟩, none⟩,
  ⟨selected, ⟨MotorAngle, []⟩, some (.mk cMotor
    (.app (.app (.app (.prim (.ite (.q Dim.Angle))) (.declRef emergency))
      (.rep (.declRef emergencyTarget))) (.rep (.declRef normalTarget))))⟩]

def Isel' (em : Bool) : Input := fun d _ =>
  if d = emergency then .bool em
  else if d = emergencyTarget then .sem cEm (.nat 0)
  else if d = normalTarget then .sem cNorm (.nat 90)
  else .nat 0

def readMotor' (I : Input) (t : Nat) : Option Nat :=
  (mevalF S₂ Δsel' I 32 actuatorClock t [] (.declRef selected)).bind fun v =>
    match v with | .sem _ (.nat n) => Option.some n | _ => Option.none

/-- **Priority, one producer**: the two targets as their own concepts, the
    selection the one origin of `MotorAngle`; the designer's condition
    reaches both outcomes as before. -/
theorem priority_unique :
    ¬ ProducerUnique Δsel ∧ ProducerUnique Δsel' ∧ GlobalWF trivEv Θ6 Δsel' ∧
    DriveWF Ωmotor Κsel Δsel' βsel ∧
    readMotor (Isel true) 0 = some 0 ∧ readMotor' (Isel' true) 0 = some 0 ∧
    readMotor (Isel false) 0 = some 90 ∧ readMotor' (Isel' false) 0 = some 90 := by
  refine ⟨fun hu => ?_, ProducerUnique.ofList (by decide), GlobalWF.ofList (by decide), DriveWF.ofList (by decide),
    by decide, by decide, by decide, by decide⟩
  have := hu cMotor emergencyTarget normalTarget (by decide) (by decide)
  exact absurd this (by decide)

/-! ## Phase 14 rewritten -/

open BDL.Experiments.OutputRealizationEx in
/-- The wire in place of the re-wrap: `light := dial`. -/
def Δ14 : DeclEnv := .ofList (decls.map fun h =>
  if h.id = light then ⟨light, ⟨.sem Brightness, []⟩, some (.declRef dial)⟩ else h)

open BDL.Experiments.OutputRealizationEx in
/-- **Re-wrap, one producer**: Phase 14's design has two origins of
    `Brightness`; the wire has one, and the light reads the same value. -/
theorem rewrap_unique :
    ¬ ProducerUnique Δ ∧ ProducerUnique Δ14 ∧ GlobalWF (fun _ _ _ => True) Θ Δ14 ∧
    DriveWF Ω Κ Δ14 β ∧
    runIs Δ 0 (.declRef light) (.sem Brightness (.nat 40)) = true ∧
    runIs Δ14 0 (.declRef light) (.sem Brightness (.nat 40)) = true := by
  refine ⟨fun hu => ?_, ProducerUnique.ofList (by decide), GlobalWF.ofList (by decide), DriveWF.ofList (by decide),
    by decide, by decide⟩
  have := hu Brightness dial light (by decide) (by decide)
  exact absurd this (by decide)

/-! ## Phase 8a: the lamp under the boundary rule -/

open BDL.Experiments.Behavior in
theorem lamp_not_unique : ¬ ProducerUnique lamp.flattenΔ :=
  BDL.Experiments.Producers.lamp_two_origins.2.2

open BDL.Experiments.Behavior in
/-- The finite presentation of the private lamp's templates. -/
def privateLampFinite : BDL.BehaviorSystem.Finite BDL.Experiments.Producers.privateLamp where
  decls := fun k => match k with
    | 0 => [⟨outP, ⟨.sem Tilt, []⟩, none⟩]
    | 1 | 2 => [⟨inP, ⟨.sem Tilt, []⟩, none⟩, ⟨outP, ⟨.sem Bright, []⟩, some (dimBody inP)⟩]
    | _ => []
  eq := by
    intro k I h
    simp only [BehaviorSystem.instAt, BDL.Experiments.Producers.privateLamp, lamp] at h
    match k, h with
    | 0, h => cases h; rfl
    | 1, h => cases h; rfl
    | 2, h => cases h; rfl
    | n + 3, h => simp at h

open BDL.Experiments.Behavior in
/-- **Reuse under the rule**: with `Bright` private to each dimmer, the
    flattened lamp is producer-unique — the templates are unique, no shared
    concept has two origins (`Tilt`'s only non-port origin is the source),
    every required port is bound, the bindings relay.  One `decide` over
    the finite presentation. -/
theorem private_lamp_unique : ProducerUnique BDL.Experiments.Producers.privateLamp.flattenΔ :=
  BDL.BehaviorSystem.flatten_producerUnique_ofB privateLampFinite (by decide)

/-! ## Reading a concept -/

open BDL.Experiments.Producers in
/-- In the sensor design (Phase 19, Model C form) `hot` may be written over
    the *concept* `Temperature`; it elaborates to the producer `temp`, and
    the kernel term is the one Phase 19 evaluated. -/
theorem read_by_concept :
    elabS [tA, tB, availA, temp, hot] ΔsensC (.cref Temperature) = some (.declRef temp) ∧
    elabS [tA, tB, availA, temp, hot] ΔsensC
      (.app (.app (.prim (.lt Dim.zero)) (.prim (.lit Dim.zero 300))) (.rep (.cref Temperature)))
      = some (ltE Dim.zero (lit 300) (.rep (.declRef temp))) ∧
    -- before the resolver exists the reference is open, not resolved to a sensor
    elabS [tA, tB, availA] (.ofList [⟨tA, ⟨.sem SensorA, []⟩, none⟩, ⟨tB, ⟨.sem SensorB, []⟩, none⟩])
      (.cref Temperature) = none := by
  refine ⟨elabS_cref sensorsC_mkUnique (by decide) (by decide), ?_, by decide⟩
  simp [elabS, ltE, app2, lit, producerOf]
  decide

open BDL.Experiments.Producers in
/-- *The* temperature at tick 1 is 310 (sensor A available) and at tick 2 is
    290 (sensor B): a function of the tick, through `producerOf`. -/
theorem temperature_value :
    (producerOf [tA, tB, availA, temp, hot] ΔsensC Temperature).bind
      (fun d => (evalF ΔsensC IsC 32 1 [] (.declRef d)).bind fun v => match v with | .sem _ (.nat n) => some n | _ => none)
      = some 310 ∧
    (producerOf [tA, tB, availA, temp, hot] ΔsensC Temperature).bind
      (fun d => (evalF ΔsensC IsC 32 2 [] (.declRef d)).bind fun v => match v with | .sem _ (.nat n) => some n | _ => none)
      = some 290 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **A transport is a relay.**  Phase 19's `Δsync` — `x : C := mk C 1` in
    `c₁`, `xS : C := sync c₁ (mk C 0) x` in `c₂` — has one producer: the
    transport's explicit initial value is its default, not an origin, so a
    concept value may cross domains without a second producer. -/
theorem transport_unique :
    ProducerUnique BDL.Experiments.Producers.Δsync ∧
    producerOf [BDL.Experiments.Producers.x, BDL.Experiments.Producers.xS] BDL.Experiments.Producers.Δsync
      BDL.Experiments.Producers.C = some BDL.Experiments.Producers.x :=
  ⟨ProducerUnique.ofList (by decide), by decide⟩

/-- The drive edge is not derived from the producer: Phase 19's design with
    one origin, two wires and two outputs is producer-unique, and neither
    driver is the producer. -/
theorem driver_independent :
    ProducerUnique BDL.Experiments.Producers.Δ2out ∧
    producerOf [BDL.Experiments.Producers.x, BDL.Experiments.Producers.xl, BDL.Experiments.Producers.xr]
      BDL.Experiments.Producers.Δ2out BDL.Experiments.Producers.C = some BDL.Experiments.Producers.x ∧
    BDL.Experiments.Producers.β2 BDL.Experiments.Producers.x = none :=
  ⟨BDL.Experiments.Producers.driver_not_origin, by decide, by decide⟩

end BDL.Experiments.ProducerUnique
