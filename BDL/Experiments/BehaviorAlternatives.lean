import BDL.Behavior.Semantics
import BDL.Behavior.Substitution

/-!
# Phase 8a — Behaviour systems: worked example and counterexamples

A concrete system built from the behaviour layer, checked by execution, and
the five negative examples the brief asks for:

1. two individually causal components whose feedback composition is cyclic;
2. a clock mismatch without `sync`;
3. accidental identity reuse (no freshening) causing aliasing;
4. an incompatible port binding;
5. a physical-output conflict after composition.

Everything here is on finite data; facts are established by `decide` or by
short direct proofs.  No composition hypothesis (`ComposeWF`) is *assumed*
in a negative example: each exhibits the concrete failing kernel judgment.
-/

namespace BDL.Experiments.Behavior
open BDL BDL.Reactive BDL.Clock BDL.Output BDL.BehaviorSystem

/-! ## §1 Global vocabulary -/

/-- Shared concepts (below the system width). -/
def Tilt : SemanticId := ⟨1⟩
def Bright : SemanticId := ⟨2⟩
/-- System clock domains (below the width). -/
def fastClk : ClockId := ⟨1⟩
def slowClk : ClockId := ⟨2⟩
/-- An external sink. -/
def light : OutputId := ⟨1⟩

def Θg : ConceptEnv := fun s =>
  if s = Tilt then some (.q Dim.Angle) else if s = Bright then some (.q Dim.zero) else none

def Ωg : OutputEnv := fun o => if o = light then some ⟨.sem Bright, fastClk⟩ else none

/-- Width: above every global identity and every template width. -/
def W : Nat := 8

/-! ## §2 Two component templates -/

/-- Local identities of the templates (all `< W`). -/
def inP : DeclId := ⟨0⟩     -- required port
def outP : DeclId := ⟨1⟩    -- provided port
def c0 : ClockId := ⟨0⟩     -- clock parameter

/-- Dimensionless gain `1 : q (0 − Angle)`. -/
def gain : Expr := .prim (.lit (Dim.sub Dim.zero Dim.Angle) 1)
/-- `bright := mk Bright (rep tilt · gain)`: the dimensioned formula of Phase 3. -/
def dimBody (tilt : DeclId) : Expr :=
  .mk Bright (.app (.app (.prim (.mul Dim.Angle (Dim.sub Dim.zero Dim.Angle))) (.rep (.declRef tilt))) gain)

/-- `Dimmer`: `tilt : Tilt` required, `bright : Bright := mk Bright (rep tilt · gain)`
    provided, both in clock parameter `c0`.  A relabelling that its own
    signature licenses, with a unit gain. -/
def dimmerDesign : Design where
  Δ := .ofList [⟨inP, ⟨.sem Tilt, []⟩, none⟩, ⟨outP, ⟨.sem Bright, []⟩, some (dimBody inP)⟩]
  Θ := Θg
  Κ := fun d => if d = inP ∨ d = outP then some c0 else none
  Ω := fun _ => none
  β := fun _ => none

def dimmer : BehaviorComponent where
  iface :=
    { required := [⟨inP, ⟨.sem Tilt, []⟩, some c0⟩]
      provided := [⟨outP, ⟨.sem Bright, []⟩, some c0⟩]
      params := []
      clockParams := [c0] }
  design := dimmerDesign
  width := 2
  internalSem := fun _ => false
  internalOut := fun _ => false

/-- `Source`: an open provider — `tilt : Tilt` is an unresolved provided
    port (the system's external input), in clock parameter `c0`. -/
def sourceDesign : Design where
  Δ := .ofList [⟨outP, ⟨.sem Tilt, []⟩, none⟩]
  Θ := Θg
  Κ := fun d => if d = outP then some c0 else none
  Ω := fun _ => none
  β := fun _ => none

def source : BehaviorComponent where
  iface :=
    { required := []
      provided := [⟨outP, ⟨.sem Tilt, []⟩, some c0⟩]
      params := []
      clockParams := [c0] }
  design := sourceDesign
  width := 2
  internalSem := fun _ => false
  internalOut := fun _ => false

/-! ## §3 A system: one source, two dimmers (reuse), two bindings -/

def κfast : ClockId → ClockId := fun _ => fastClk

/-- Instance 0: source; instances 1 and 2: two dimmers from one template. -/
def lamp : BehaviorSystem where
  W := W
  insts := [⟨source, κfast⟩, ⟨dimmer, κfast⟩, ⟨dimmer, κfast⟩]
  bindings := [⟨.port 0 outP, 1, inP, none⟩, ⟨.port 0 outP, 2, inP, none⟩]
  Θg := Θg
  Ωg := Ωg

/-- **Theorem A, concretely.**  The two dimmer instances own disjoint
    declarations, and neither collides with the source. -/
theorem lamp_ids_disjoint :
    lamp.declOf 1 inP ≠ lamp.declOf 2 inP ∧ lamp.declOf 1 outP ≠ lamp.declOf 2 outP ∧
    lamp.declOf 0 outP ≠ lamp.declOf 1 inP := by decide

/-- The fresh identities, for the record: instance `k`, local `n` ↦ `8·(k+1)+n`. -/
theorem lamp_ids : lamp.declOf 0 outP = ⟨9⟩ ∧ lamp.declOf 1 inP = ⟨16⟩ ∧ lamp.declOf 2 outP = ⟨25⟩ := by decide

/-- Flattening realizes each bound port with a reference to the source. -/
theorem lamp_binding_bodies :
    lamp.flattenΔ.realizationOf (lamp.declOf 1 inP) = some (.declRef (lamp.declOf 0 outP)) ∧
    lamp.flattenΔ.realizationOf (lamp.declOf 2 inP) = some (.declRef (lamp.declOf 0 outP)) := by decide

/-- The source port stays open (Theorem H, concretely). -/
theorem lamp_source_open : lamp.flattenΔ.realizationOf (lamp.declOf 0 outP) = none := by decide

/-- Shared concepts are not renamed; the dimmer's output is `Bright` in both instances. -/
theorem lamp_shared_concepts :
    lamp.flattenΔ.tyView (lamp.declOf 1 outP) = some (.sem Bright) ∧
    lamp.flattenΔ.tyView (lamp.declOf 2 outP) = some (.sem Bright) := by decide

/-- Clock parameters are substituted: everything runs in `fastClk`. -/
theorem lamp_clocks :
    lamp.unionΚ (lamp.declOf 0 outP) = some fastClk ∧ lamp.unionΚ (lamp.declOf 2 inP) = some fastClk := by decide

/-- The flattened design is well clocked and causal, checked directly on the
    finite list of its declarations. -/
def lampDecls : List DesignDecl :=
  [⟨lamp.declOf 0 outP, ⟨.sem Tilt, []⟩, none⟩,
   ⟨lamp.declOf 1 inP, ⟨.sem Tilt, []⟩, some (.declRef (lamp.declOf 0 outP))⟩,
   ⟨lamp.declOf 1 outP, ⟨.sem Bright, []⟩, some (dimBody (lamp.declOf 1 inP))⟩,
   ⟨lamp.declOf 2 inP, ⟨.sem Tilt, []⟩, some (.declRef (lamp.declOf 0 outP))⟩,
   ⟨lamp.declOf 2 outP, ⟨.sem Bright, []⟩, some (dimBody (lamp.declOf 2 inP))⟩]

theorem lamp_flatten_is_lampDecls : ∀ d ∈ lampDecls, lamp.flattenΔ d.id = some d := by decide

theorem lamp_flatten_typed : GlobalWF (fun _ _ _ => True) Θg (.ofList lampDecls) := GlobalWF.ofList (by decide)

theorem lamp_flatten_clocked : wellClockedCheck lamp.unionΚ lampDecls = true := by decide

def lampRank : DeclId → Nat := fun d => if d.n = 9 then 0 else if d.n = 16 ∨ d.n = 24 then 1 else 2

theorem lamp_flatten_causal : causalCheck lampDecls lampRank = true := by decide

/-! ### Execution: flattened vs modular (Theorem J, concretely) -/

/-- The system input: the source reports tilt `t` at tick `t`. -/
def I : Input := fun d t => if d = lamp.declOf 0 outP then .sem Tilt (.nat t) else .nat 0

/-- A consistent modular input: the two bound ports are fed the source's value. -/
def I' : Input := fun d t =>
  if d = lamp.declOf 0 outP ∨ d = lamp.declOf 1 inP ∨ d = lamp.declOf 2 inP then .sem Tilt (.nat t) else .nat 0

def brightOf : Value → Option Nat
  | .sem s (.nat n) => if s = Bright then some n else none
  | _ => none

def runFlat (d : DeclId) (t : Nat) : Option Nat := (evalF lamp.flattenΔ I 32 t [] (.declRef d)).bind brightOf
def runInst (k : Nat) (d : DeclId) (t : Nat) : Option Nat := (evalF (lamp.instΔ k) I' 32 t [] (.declRef d)).bind brightOf

/-- Both dimmers relabel the source's tilt as brightness, tick by tick, in
    the flattened design ... -/
theorem lamp_flat_trace :
    [runFlat (lamp.declOf 1 outP) 0, runFlat (lamp.declOf 1 outP) 3, runFlat (lamp.declOf 2 outP) 3] =
      [some 0, some 3, some 3] := by decide

/-- ... and in each instance evaluated alone under the consistent input. -/
theorem lamp_modular_trace :
    [runInst 1 (lamp.declOf 1 outP) 0, runInst 1 (lamp.declOf 1 outP) 3, runInst 2 (lamp.declOf 2 outP) 3] =
      [some 0, some 3, some 3] := by decide

/-- Consistency of `I'` at the two bound ports, at the sampled ticks. -/
theorem lamp_consistent_sample :
    (evalF (lamp.instΔ 0) I' 32 3 [] (.declRef (lamp.declOf 0 outP))).bind
        (fun v => match v with | .sem s (.nat n) => some (s.n, n) | _ => none) = some (Tilt.n, 3) := by decide

/-! ## §4 Counterexample 1 — feedback between two causal components -/

/-- `Pass`: `out := in`, causal on its own. -/
def passDesign : Design where
  Δ := .ofList [⟨inP, ⟨.nat, []⟩, none⟩, ⟨outP, ⟨.nat, []⟩, some (.declRef inP)⟩]
  Θ := fun _ => none
  Κ := fun d => if d = inP ∨ d = outP then some c0 else none
  Ω := fun _ => none
  β := fun _ => none

def pass : BehaviorComponent where
  iface :=
    { required := [⟨inP, ⟨.nat, []⟩, some c0⟩]
      provided := [⟨outP, ⟨.nat, []⟩, some c0⟩]
      params := []
      clockParams := [c0] }
  design := passDesign
  width := 2
  internalSem := fun _ => false
  internalOut := fun _ => false

theorem pass_causal : Causal passDesign.Δ :=
  Causal.ofList (fun d => if d = outP then 1 else 0) 2 (by intro d; split <;> omega) (by decide)

/-- Two passes in feedback: `A.in := B.out`, `B.in := A.out`. -/
def feedback : BehaviorSystem where
  W := W
  insts := [⟨pass, κfast⟩, ⟨pass, κfast⟩]
  bindings := [⟨.port 1 outP, 0, inP, none⟩, ⟨.port 0 outP, 1, inP, none⟩]
  Θg := fun _ => none
  Ωg := fun _ => none

/-- The inter-instance graph has the cycle `0 → 1 → 0`, so `InstAcyclic` fails. -/
theorem feedback_instDep : InstDep feedback 0 1 ∧ InstDep feedback 1 0 :=
  ⟨⟨⟨.port 1 outP, 0, inP, none⟩, by simp [feedback], rfl, rfl, outP, rfl⟩,
   ⟨⟨.port 0 outP, 1, inP, none⟩, by simp [feedback], rfl, rfl, outP, rfl⟩⟩

theorem feedback_not_instAcyclic : ¬ InstAcyclic feedback := by
  rintro ⟨irank, R, -, hdep⟩
  have h₁ := hdep 0 1 feedback_instDep.1
  have h₂ := hdep 1 0 feedback_instDep.2
  omega

/-- The flattened design has a strict instantaneous cycle
    `A.out → A.in → B.out → B.in → A.out`. -/
theorem feedback_edges :
    InstDependsOn feedback.flattenΔ (feedback.declOf 0 outP) (feedback.declOf 0 inP) ∧
    InstDependsOn feedback.flattenΔ (feedback.declOf 0 inP) (feedback.declOf 1 outP) ∧
    InstDependsOn feedback.flattenΔ (feedback.declOf 1 outP) (feedback.declOf 1 inP) ∧
    InstDependsOn feedback.flattenΔ (feedback.declOf 1 inP) (feedback.declOf 0 outP) := by decide

/-- **Counterexample 1.**  Each component is causal; their feedback
    composition is not.  The condition of `flatten_causal` is necessary. -/
theorem feedback_composition_not_causal : ¬ Causal feedback.flattenΔ := by
  rintro ⟨rank, R, -, hr⟩
  obtain ⟨e₁, e₂, e₃, e₄⟩ := feedback_edges
  have := hr _ _ e₁; have := hr _ _ e₂; have := hr _ _ e₃; have := hr _ _ e₄
  omega

/-- The repair: one of the two bindings through `sync` (explicit transport,
    initial value `0`).  No direct edge remains, so the inter-instance graph
    is trivially acyclic, and the flattened design is causal. -/
def feedbackSync : BehaviorSystem :=
  { feedback with bindings := [⟨.port 1 outP, 0, inP, some (.natLit 0)⟩, ⟨.port 0 outP, 1, inP, none⟩] }

theorem feedbackSync_instAcyclic : InstAcyclic feedbackSync := by
  refine ⟨fun k => if k = 0 then 0 else 1, 2, fun k => by show (if k = 0 then 0 else 1) < 2; split <;> omega, ?_⟩
  rintro i j ⟨b, hb, hi, ht, id, hs⟩
  simp [feedbackSync, feedback] at hb
  rcases hb with rfl | rfl
  · simp at ht
  · simp at hs hi
    obtain ⟨rfl, -⟩ := hs
    subst hi
    decide

/-! ## §5 Counterexample 2 — clock mismatch without `sync` -/

/-- Two passes in different system domains, bound directly. -/
def κslow : ClockId → ClockId := fun _ => slowClk

def clockMismatch : BehaviorSystem where
  W := W
  insts := [⟨pass, κfast⟩, ⟨pass, κslow⟩]
  bindings := [⟨.port 0 outP, 1, inP, none⟩]
  Θg := fun _ => none
  Ωg := fun _ => none

/-- The binding is not well formed: the source is in `fastClk`, the
    destination in `slowClk`, and no transport is declared. -/
theorem clockMismatch_binding_rejected (ev : Evidence) :
    ¬ BindingWF ev clockMismatch ⟨.port 0 outP, 1, inP, none⟩ := by
  rintro ⟨Id, hId, pd, hpd, -, Is, hIs, ps, hps, -, -, -, hclk⟩
  simp [clockMismatch, instAt] at hId hIs
  subst hId; subst hIs
  simp [pass] at hpd hps
  subst hpd; subst hps
  revert hclk; decide

/-- And the flattened design is not well clocked: the direct wire reads
    `fastClk` from `slowClk`. -/
theorem clockMismatch_not_wellClocked : ¬ WellClocked clockMismatch.unionΚ clockMismatch.flattenΔ := by
  intro h
  have := h (clockMismatch.declOf 1 inP) (.declRef (clockMismatch.declOf 0 outP)) (by decide)
  revert this; decide

/-! ## §6 Counterexample 3 — identity reuse without freshening -/

/-- With fresh identities the two dimmers are distinct declarations
    (`lamp_ids_disjoint`).  With the *identity* renaming they would
    coincide: instantiation by name alone aliases every instance of a
    template onto the first. -/
theorem identity_renaming_aliases : Ren.id.d inP = Ren.id.d inP ∧ (Ren.inst dimmer W 1 κfast).d inP ≠ (Ren.inst dimmer W 2 κfast).d inP :=
  ⟨rfl, by decide⟩

/-- A concept flagged *internal* is freshened per instance: two instances of
    a template do not share it merely because it came from the same
    template.  (A concept meant to be shared must be flagged global.) -/
def privateDimmer : BehaviorComponent := { dimmer with internalSem := fun s => s = Bright }

theorem internal_concept_not_shared :
    (Ren.inst privateDimmer W 1 κfast).s Bright ≠ (Ren.inst privateDimmer W 2 κfast).s Bright ∧
    (Ren.inst dimmer W 1 κfast).s Bright = (Ren.inst dimmer W 2 κfast).s Bright := by decide

/-! ## §7 Counterexample 4 — incompatible port binding -/

/-- `Motor`: requires `angle : MotorAngle`. -/
def MotorAngle : SemanticId := ⟨3⟩

def motorDesign : Design where
  Δ := .ofList [⟨inP, ⟨.sem MotorAngle, []⟩, none⟩]
  Θ := Θg
  Κ := fun d => if d = inP then some c0 else none
  Ω := fun _ => none
  β := fun _ => none

def motor : BehaviorComponent where
  iface :=
    { required := [⟨inP, ⟨.sem MotorAngle, []⟩, some c0⟩]
      provided := []
      params := []
      clockParams := [c0] }
  design := motorDesign
  width := 2
  internalSem := fun _ => false
  internalOut := fun _ => false

/-- Wiring the source's `Tilt` port straight into the motor's `MotorAngle` port. -/
def tiltToMotor : BehaviorSystem where
  W := W
  insts := [⟨source, κfast⟩, ⟨motor, κfast⟩]
  bindings := [⟨.port 0 outP, 1, inP, none⟩]
  Θg := Θg
  Ωg := fun _ => none

/-- The binding is rejected on types: `Tilt ≠ MotorAngle`, shared
    representation notwithstanding. -/
theorem tiltToMotor_binding_rejected (ev : Evidence) :
    ¬ BindingWF ev tiltToMotor ⟨.port 0 outP, 1, inP, none⟩ := by
  rintro ⟨Id, hId, pd, hpd, -, Is, hIs, ps, hps, -, hty, -⟩
  simp [tiltToMotor, instAt] at hId hIs
  subst hId; subst hIs
  simp [source, motor] at hpd hps
  subst hpd; subst hps
  revert hty; decide

/-- And had the binding been applied anyway, the destination's realization
    would not type-check against its interface. -/
theorem tiltToMotor_forced_ill_typed :
    ¬ HasType tiltToMotor.unionΘ tiltToMotor.flattenΔ (Grant.of (.sem MotorAngle)) []
        (.declRef (tiltToMotor.declOf 0 outP)) (.sem MotorAngle) := by decide

/-! ## §8 Counterexample 5 — physical-output conflict after composition -/

/-- `Driver`: `out : Bright := mk Bright (rep in)` drives the *external* sink `light`. -/
def driverDesign : Design where
  Δ := dimmerDesign.Δ
  Θ := Θg
  Κ := dimmerDesign.Κ
  Ω := fun o => if o = light then some ⟨.sem Bright, c0⟩ else none
  β := fun d => if d = outP then some light else none

def driver : BehaviorComponent := { dimmer with design := driverDesign }

/-- Each driver alone is single-driver. -/
theorem driver_singleDriver : SingleDriver driverDesign.β := by
  intro d₁ d₂ o h₁ h₂
  simp [driverDesign] at h₁ h₂
  rw [h₁.1, h₂.1]

/-- Two drivers of the same external light. -/
def twoDrivers : BehaviorSystem where
  W := W
  insts := [⟨driver, κfast⟩, ⟨driver, κfast⟩]
  bindings := []
  Θg := Θg
  Ωg := Ωg

/-- **Counterexample 5.**  After composition the light has two drivers:
    the union of the drive edges violates single-driver, although each
    component satisfied it.  `ExternalSingleDriver` is necessary. -/
theorem twoDrivers_not_singleDriver : ¬ SingleDriver twoDrivers.unionβ := by
  intro h
  have := h (twoDrivers.declOf 0 outP) (twoDrivers.declOf 1 outP) light (by decide) (by decide)
  revert this; decide

theorem twoDrivers_not_externalSingleDriver : ¬ ExternalSingleDriver twoDrivers := by
  intro h
  have := h 0 ⟨driver, κfast⟩ outP 1 ⟨driver, κfast⟩ outP light rfl rfl rfl rfl rfl rfl
  omega

/-- The repair is the Phase-6 principle: one final target.  With a private
    sink per instance (two lights), single-driver holds. -/
def privateDriver : BehaviorComponent := { driver with internalOut := fun o => o = light }

def twoLights : BehaviorSystem := { twoDrivers with insts := [⟨privateDriver, κfast⟩, ⟨privateDriver, κfast⟩] }

theorem twoLights_distinct_sinks :
    twoLights.unionβ (twoLights.declOf 0 outP) ≠ twoLights.unionβ (twoLights.declOf 1 outP) := by decide

end BDL.Experiments.Behavior
