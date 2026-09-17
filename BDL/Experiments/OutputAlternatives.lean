import BDL.Core.Output
import BDL.Experiments.ClockAlternatives

/-!
# Phase 6 — Physical outputs and the single-driver discipline

A declaration computes a *value*; it does not move hardware.  Physical
effect occurs only when an explicit **drive edge** binds a declaration to a
**physical sink**.  The smallest model tested here:

* `OutputId` — nominal identity of a physical sink (resource identity, not
  semantic identity, not a design relationship);
* `OutputEnv Ω : OutputId → Option OutputSpec` — what a sink accepts: a
  target `Ty` and a `ClockId` (deployment-declared resource description);
* `DriveEnv β : DeclId → Option OutputId` — which declaration drives which
  sink (per-declaration projection, like `Κ`);
* `DriveWF` — a drive edge is well formed iff the driver has exactly the
  sink's accepted type and lives in the sink's domain (ordinary typing
  equality: no coercion, no synchronization inside the binding);
* `SingleDriver β` — at most one driver per sink (**global**, not typing);
* `CompleteOutputs β req` — every required sink is driven (executable
  designs only).

Everything that combines several behaviours into one target is ordinary
value computation upstream of the single drive edge.

The model itself (identities, `DriveWF`, `SingleDriver`, `CompleteOutputs`,
the refinement lemma, partial vs executable, physical output semantics and
its determinism) was promoted to `BDL/Core/Output.lean`.  This file keeps:
§2 output identity alternatives (D); §3 Counterexamples A, B; §4 hidden
arbitration (C) and explicit priority; §5 semantic identity, dimension, grant
(E); §6 clocks (G); §7 rebinding (F); §8 partial vs executable examples;
§9 effect rows and action values; §10 StateHandler remainder; §11 two
drivers, two outputs.
-/

namespace BDL.Experiments.Output
open BDL BDL.Reactive BDL.Clock BDL.Output BDL.Experiments.Semantic BDL.Experiments.Reactive BDL.Experiments.Clock

/-! ## §2 Output identity — the alternatives (Counterexample D) -/

def leftServo  : OutputId := ⟨0⟩
def rightServo : OutputId := ⟨1⟩
def actuatorClock : ClockId := slow

/-- Two sinks accepting exactly the same semantic type and domain. -/
def Ωservos : OutputEnv := .ofList [(leftServo, ⟨MotorAngle, actuatorClock⟩), (rightServo, ⟨MotorAngle, actuatorClock⟩)]

def leftTarget : DeclId := ⟨200⟩
def rightTarget : DeclId := ⟨201⟩
def dLeft : DesignDecl := ⟨leftTarget, ⟨MotorAngle, []⟩, none⟩
def dRight : DesignDecl := ⟨rightTarget, ⟨MotorAngle, []⟩, none⟩
def Δservos : DeclEnv := .ofList [dLeft, dRight]
def Κservos : ClockEnv := fun d => if d = leftTarget ∨ d = rightTarget then Option.some actuatorClock else Option.none

/-- **Counterexample D — same type does not identify a sink.**  Under a
    type-keyed binding ("drive *the* MotorAngle sink") the two servos are one
    sink and the two legitimate drivers collide; under nominal `OutputId` the
    design is fine. -/
def typeKeyedDrive : List (Ty × DeclId) := [(MotorAngle, leftTarget), (MotorAngle, rightTarget)]

theorem type_keyed_binding_collides :
    ((typeKeyedDrive.map Prod.fst).Nodup = false) ∧
    SingleDriver (.ofList [(leftTarget, leftServo), (rightTarget, rightServo)]) ∧
    DriveWF Ωservos Κservos Δservos (.ofList [(leftTarget, leftServo), (rightTarget, rightServo)]) :=
  ⟨by decide, SingleDriver.ofList (by decide), DriveWF.ofList (by decide)⟩

/-- Using `SemanticId` as the sink identity conflates concept and hardware:
    one concept (`MotorAngle`) feeds two devices, so "the MotorAngle output"
    is not a sink.  Using `DeclId` conflates relationship and resource: two
    declarations that both mean to drive the steering motor become two
    *different* "sinks" and the conflict of Counterexample A cannot even be
    stated.  Both are recorded as arguments; the mechanized content is that
    the nominal model expresses both designs and the type-keyed one does not. -/
example : True := trivial

/-! ## §3 Counterexamples A and B -/

def motor : OutputId := ⟨2⟩
def Ωmotor : OutputEnv := .ofList [(motor, ⟨MotorAngle, actuatorClock⟩)]

def baseAngle : DeclId := ⟨210⟩      -- slow input : MotorAngle
def corrAngle : DeclId := ⟨211⟩      -- slow input : MotorAngle
def driveA : DeclId := ⟨212⟩
def driveB : DeclId := ⟨213⟩
def finalAngle : DeclId := ⟨214⟩
def dBase : DesignDecl := ⟨baseAngle, ⟨MotorAngle, []⟩, none⟩
def dCorr : DesignDecl := ⟨corrAngle, ⟨MotorAngle, []⟩, none⟩
def dDriveA : DesignDecl := ⟨driveA, ⟨MotorAngle, []⟩, some (.declRef baseAngle)⟩
def dDriveB : DesignDecl := ⟨driveB, ⟨MotorAngle, []⟩, some (.declRef corrAngle)⟩
/-- `final := mk MotorAngle (rep base + rep corr)` — explicit composition,
    constructed under `final`'s own grant. -/
def dFinal : DesignDecl := ⟨finalAngle, ⟨MotorAngle, []⟩, some
  (.mk cMotor (.app (.app (.prim (.add Dim.Angle)) (.rep (.declRef baseAngle))) (.rep (.declRef corrAngle))))⟩

def ΚA : ClockEnv := fun d =>
  if d = baseAngle ∨ d = corrAngle ∨ d = driveA ∨ d = driveB ∨ d = finalAngle then Option.some actuatorClock else Option.none

def ΔA : DeclEnv := .ofList [dBase, dCorr, dDriveA, dDriveB]
def βA : DriveEnv := .ofList [(driveA, motor), (driveB, motor)]

/-- **Counterexample A — two direct drivers.**  Everything local passes:
    global typing, clocks, causality, each drive edge individually.  Only the
    global single-driver invariant fails.  Local typing is insufficient. -/
theorem two_direct_drivers_locally_fine :
    GlobalWF trivEv Dimension.Θdim ΔA ∧ WellClocked ΚA ΔA ∧ Causal ΔA ∧
    DriveWF Ωmotor ΚA ΔA βA :=
  ⟨GlobalWF.ofList (by decide), WellClocked.ofList (by decide),
   Causal.ofList (fun d => if d = driveA ∨ d = driveB then 1 else 0) 2
     (by intro d; show (if _ then 1 else 0) < 2; split <;> decide) (by decide),
   DriveWF.ofList (by decide)⟩

theorem multiple_direct_drivers_rejected : ¬ SingleDriver βA := by
  intro h
  have := h driveA driveB motor (by decide) (by decide)
  exact absurd this (by decide)

/-- **Counterexample B — explicit composition is valid.**  Two contributors,
    one `add`, one target, one drive edge; no arbitration anywhere. -/
def ΔB : DeclEnv := .ofList [dBase, dCorr, dFinal]
def βB : DriveEnv := .ofList [(finalAngle, motor)]

theorem explicit_target_composition_accepted :
    GlobalWF trivEv Dimension.Θdim ΔB ∧ WellClocked ΚA ΔB ∧ Causal ΔB ∧
    DriveWF Ωmotor ΚA ΔB βB ∧ SingleDriver βB ∧ CompleteOutputs βB [motor] :=
  ⟨GlobalWF.ofList (by decide), WellClocked.ofList (by decide),
   Causal.ofList (fun d => if d = finalAngle then 1 else 0) 2
     (by intro d; show (if _ then 1 else 0) < 2; split <;> decide) (by decide),
   DriveWF.ofList (by decide), SingleDriver.ofList (by decide),
   fun o ho => by simp at ho; subst ho; exact ⟨finalAngle, by decide⟩⟩

/-- The contributors are upstream *dependencies* of the driver, not drivers:
    the dependency graph is not the writer graph. -/
theorem contributors_are_not_drivers :
    DependsOn ΔB finalAngle baseAngle ∧ DependsOn ΔB finalAngle corrAngle ∧
    βB baseAngle = Option.none ∧ βB corrAngle = Option.none := by decide

/-! ## §4 Hidden arbitration is observable (Counterexample C); explicit priority -/

/-- Toy runtime policies over the values of several would-be drivers. -/
def firstWins (vs : List Nat) : Option Nat := vs.head?
def lastWins  (vs : List Nat) : Option Nat := vs.getLast?
def maxWins   (vs : List Nat) : Option Nat := vs.foldl (fun acc x => Option.some (match acc with | Option.some a => max a x | Option.none => x)) Option.none

/-- **Counterexample C.**  The same value graph (`driveA = 10`, `driveB = 40`)
    under three hidden policies produces three different physical outputs.
    Arbitration policy is semantic design information. -/
theorem hidden_arbitration_observable :
    firstWins [10, 40] = some 10 ∧ lastWins [10, 40] = some 40 ∧ maxWins [10, 40] = some 40 ∧
    (10 : Nat) ≠ 40 := by decide

/-- The explicit alternative: priority as an ordinary conditional in a
    single driver.  `emergency` selects between two ordinary targets. -/
def emergency : DeclId := ⟨220⟩      -- bool input
def emergencyTarget : DeclId := ⟨221⟩  -- MotorAngle input
def normalTarget : DeclId := ⟨222⟩     -- MotorAngle input
def selected : DeclId := ⟨223⟩
def dEmergency : DesignDecl := ⟨emergency, ⟨.bool, []⟩, none⟩
def dEmT : DesignDecl := ⟨emergencyTarget, ⟨MotorAngle, []⟩, none⟩
def dNormT : DesignDecl := ⟨normalTarget, ⟨MotorAngle, []⟩, none⟩
def dSelected : DesignDecl := ⟨selected, ⟨MotorAngle, []⟩, some
  (.app (.app (.app (.prim (.ite MotorAngle)) (.declRef emergency)) (.declRef emergencyTarget)) (.declRef normalTarget))⟩
def Δsel : DeclEnv := .ofList [dEmergency, dEmT, dNormT, dSelected]
def βsel : DriveEnv := .ofList [(selected, motor)]
def Κsel : ClockEnv := fun _ => Option.some actuatorClock

def Isel (em : Bool) : Input := fun d _ =>
  if d = emergency then .bool em
  else if d = emergencyTarget then .sem cMotor (.nat 0)
  else if d = normalTarget then .sem cMotor (.nat 90)
  else .nat 0

def readMotor (I : Input) (t : Nat) : Option Nat :=
  (mevalF S₂ Δsel I 32 actuatorClock t [] (.declRef selected)).bind fun v =>
    match v with | .sem _ (.nat n) => Option.some n | _ => Option.none

/-- **Explicit priority**: one driver, the policy visible in the graph, both
    outcomes reachable by the *designer's* condition — no runtime policy. -/
theorem explicit_priority_single_driver :
    SingleDriver βsel ∧ DriveWF Ωmotor Κsel Δsel βsel ∧
    readMotor (Isel true) 0 = some 0 ∧ readMotor (Isel false) 0 = some 90 :=
  ⟨SingleDriver.ofList (by decide), DriveWF.ofList (by decide), by decide, by decide⟩

/-- `max`, weighted blend, additive correction, `clamp (sum …)` are the same
    shape: ordinary declarations of the target type.  Two of them, typed. -/
def blended : DeclId := ⟨224⟩
def dBlended : DesignDecl := ⟨blended, ⟨MotorAngle, []⟩, some
  (.mk cMotor (.app (.app (.prim (.div Dim.Angle Dim.zero))
    (.app (.app (.prim (.add Dim.Angle)) (.rep (.declRef emergencyTarget))) (.rep (.declRef normalTarget))))
    (.prim (.lit Dim.zero 2))))⟩
def maxed : DeclId := ⟨225⟩
def dMaxed : DesignDecl := ⟨maxed, ⟨MotorAngle, []⟩, some
  (.mk cMotor (.app (.app (.app (.prim (.ite (.q Dim.Angle)))
    (.app (.app (.prim (.lt Dim.Angle)) (.rep (.declRef emergencyTarget))) (.rep (.declRef normalTarget))))
    (.rep (.declRef normalTarget))) (.rep (.declRef emergencyTarget))))⟩
theorem blend_and_max_are_ordinary_targets :
    GlobalWF trivEv Dimension.Θdim (.ofList [dEmT, dNormT, dBlended, dMaxed]) := GlobalWF.ofList (by decide)

/-! ## §5 Semantic identity, dimension, grant (Counterexample E) -/

def tiltTarget : DeclId := ⟨230⟩
def angleTarget : DeclId := ⟨231⟩
def lengthTarget : DeclId := ⟨232⟩
def dTiltT : DesignDecl := ⟨tiltTarget, ⟨Tilt, []⟩, none⟩
def dAngleT : DesignDecl := ⟨angleTarget, ⟨.q Dim.Angle, []⟩, none⟩
def dLengthT : DesignDecl := ⟨lengthTarget, ⟨.q Dim.Length, []⟩, none⟩
def ΔE : DeclEnv := .ofList [dTiltT, dAngleT, dLengthT, dFinal, dBase, dCorr]
def ΚE : ClockEnv := fun _ => Option.some actuatorClock

/-- **Counterexample E — binding does not manufacture identity.**  A `Tilt`
    value, a bare `q Angle`, or a `q Length` cannot be bound to the
    `MotorAngle` sink; only a declaration *already typed* `MotorAngle` can —
    and that declaration obtained its `MotorAngle` under its own grant
    (`dFinal`).  The binding is a type *equality*, not a coercion. -/
theorem output_binding_preserves_semantic_identity_and_dimension :
    ¬ DriveWF Ωmotor ΚE ΔE (.ofList [(tiltTarget, motor)]) ∧
    ¬ DriveWF Ωmotor ΚE ΔE (.ofList [(angleTarget, motor)]) ∧
    ¬ DriveWF Ωmotor ΚE ΔE (.ofList [(lengthTarget, motor)]) ∧
    DriveWF Ωmotor ΚE ΔE (.ofList [(finalAngle, motor)]) := by
  refine ⟨?_, ?_, ?_, DriveWF.ofList (by decide)⟩
  · intro h
    obtain ⟨spec, hΩ, hty, _⟩ := h tiltTarget motor (by decide)
    have : spec = ⟨MotorAngle, actuatorClock⟩ := by
      simp [Ωmotor, OutputEnv.ofList] at hΩ; exact hΩ.symm
    subst this
    exact absurd hty (by decide)
  · intro h
    obtain ⟨spec, hΩ, hty, _⟩ := h angleTarget motor (by decide)
    have : spec = ⟨MotorAngle, actuatorClock⟩ := by
      simp [Ωmotor, OutputEnv.ofList] at hΩ; exact hΩ.symm
    subst this
    exact absurd hty (by decide)
  · intro h
    obtain ⟨spec, hΩ, hty, _⟩ := h lengthTarget motor (by decide)
    have : spec = ⟨MotorAngle, actuatorClock⟩ := by
      simp [Ωmotor, OutputEnv.ofList] at hΩ; exact hΩ.symm
    subst this
    exact absurd hty (by decide)

/-- A sink accepting a *representation* (`q Angle`) is legitimate — it just
    describes a different device — and then a `MotorAngle` value needs an
    explicit `rep` in a declaration of that type before it can drive it.
    Hardware representation vs semantic target stays explicit. -/
def rawServo : OutputId := ⟨3⟩
def Ωraw : OutputEnv := .ofList [(rawServo, ⟨.q Dim.Angle, actuatorClock⟩)]
def rawCmd : DeclId := ⟨233⟩
def dRawCmd : DesignDecl := ⟨rawCmd, ⟨.q Dim.Angle, []⟩, some (.rep (.declRef finalAngle))⟩
theorem representation_sink_needs_explicit_rep :
    ¬ DriveWF Ωraw ΚE (.ofList [dFinal, dRawCmd, dBase, dCorr]) (.ofList [(finalAngle, rawServo)]) ∧
    DriveWF Ωraw ΚE (.ofList [dFinal, dRawCmd, dBase, dCorr]) (.ofList [(rawCmd, rawServo)]) := by
  refine ⟨?_, DriveWF.ofList (by decide)⟩
  intro h
  obtain ⟨spec, hΩ, hty, _⟩ := h finalAngle rawServo (by decide)
  have : spec = ⟨.q Dim.Angle, actuatorClock⟩ := by
    simp [Ωraw, OutputEnv.ofList] at hΩ; exact hΩ.symm
  subst this
  exact absurd hty (by decide)

/-! ## §6 Clock domains (Counterexample G) -/

def tracking : DeclId := ⟨240⟩      -- fast : MotorAngle
def userCmd : DeclId := ⟨241⟩       -- slow : MotorAngle
def fastFinal : DeclId := ⟨242⟩     -- fast driver (wrong domain)
def unsyncFinal : DeclId := ⟨243⟩   -- slow, reads tracking without sync (wrong)
def syncFinal : DeclId := ⟨244⟩     -- slow, syncs tracking first (right)
def dTracking : DesignDecl := ⟨tracking, ⟨MotorAngle, []⟩, none⟩
def dUserCmd : DesignDecl := ⟨userCmd, ⟨MotorAngle, []⟩, none⟩
def initMotor : Expr := .mk cMotor (.prim (.lit Dim.Angle 0))
def combine (a b : Expr) : Expr :=
  .mk cMotor (.app (.app (.prim (.add Dim.Angle)) (.rep a)) (.rep b))
def dFastFinal : DesignDecl := ⟨fastFinal, ⟨MotorAngle, []⟩, some (combine (.declRef tracking) (.declRef tracking))⟩
def dUnsync : DesignDecl := ⟨unsyncFinal, ⟨MotorAngle, []⟩, some (combine (.declRef tracking) (.declRef userCmd))⟩
def dSync : DesignDecl := ⟨syncFinal, ⟨MotorAngle, []⟩, some (combine (.sync fast initMotor (.declRef tracking)) (.declRef userCmd))⟩
def ΔG : DeclEnv := .ofList [dTracking, dUserCmd, dFastFinal, dUnsync, dSync]
def ΚG : ClockEnv := fun d =>
  if d = tracking ∨ d = fastFinal then Option.some fast
  else if d = userCmd ∨ d = unsyncFinal ∨ d = syncFinal then Option.some slow
  else Option.none

/-- **Counterexample G — synchronize before you drive.**  A fast driver
    cannot drive the slow sink (clock mismatch in `DriveWF`); a slow driver
    that reads the fast value directly is not well-clocked; the slow driver
    that `sync`s the fast contributor first passes both checks.  The binding
    never synchronizes anything itself. -/
theorem output_binding_respects_clock_domain :
    ¬ DriveWF Ωmotor ΚG ΔG (.ofList [(fastFinal, motor)]) ∧
    ¬ Clocked ΚG (ΚG unsyncFinal) (combine (.declRef tracking) (.declRef userCmd)) ∧
    Clocked ΚG (ΚG syncFinal) (combine (.sync fast initMotor (.declRef tracking)) (.declRef userCmd)) ∧
    DriveWF Ωmotor ΚG ΔG (.ofList [(syncFinal, motor)]) := by
  refine ⟨?_, by decide, by decide, DriveWF.ofList (by decide)⟩
  intro h
  obtain ⟨spec, hΩ, _, hclk⟩ := h fastFinal motor (by decide)
  have : spec = ⟨MotorAngle, actuatorClock⟩ := by
    simp [Ωmotor, OutputEnv.ofList] at hΩ; exact hΩ.symm
  subst this
  exact absurd hclk (by decide)

/-! ## §7 Refinement vs edit (Counterexample F) -/

/-- Binding a second driver to a driven sink is *invalid* (not an edit that
    might be rechecked — the invariant is false). -/
theorem second_binding_invalid : ¬ SingleDriver (βB.bind driveB motor) := by
  intro h
  have := h finalAngle driveB motor (by decide) (by decide)
  exact absurd this (by decide)

/-- **Counterexample F — rebinding invalidates an unchanged design.**
    (a) retargeting the sink's accepted type in `Ω` breaks `DriveWF` of the
    untouched driver; (b) renaming the sink leaves the drive edge dangling;
    (c) detaching the edge breaks completeness. -/
def Ωmotor' : OutputEnv := .ofList [(motor, ⟨.q Dim.Angle, actuatorClock⟩)]   -- (a)
def motorRenamed : OutputId := ⟨4⟩
def Ωrenamed : OutputEnv := .ofList [(motorRenamed, ⟨MotorAngle, actuatorClock⟩)]  -- (b)

theorem rebinding_invalidates_design :
    DriveWF Ωmotor ΚA ΔB βB ∧
    ¬ DriveWF Ωmotor' ΚA ΔB βB ∧
    ¬ DriveWF Ωrenamed ΚA ΔB βB ∧
    ¬ CompleteOutputs (βB.bind finalAngle motor |> fun _ => DriveEnv.none) [motor] := by
  refine ⟨DriveWF.ofList (by decide), ?_, ?_, ?_⟩
  · intro h
    obtain ⟨spec, hΩ, hty, _⟩ := h finalAngle motor (by decide)
    have : spec = ⟨.q Dim.Angle, actuatorClock⟩ := by simp [Ωmotor', OutputEnv.ofList] at hΩ; exact hΩ.symm
    subst this; exact absurd hty (by decide)
  · intro h
    obtain ⟨spec, hΩ, _, _⟩ := h finalAngle motor (by decide)
    simp [Ωrenamed, OutputEnv.ofList, motor, motorRenamed] at hΩ
  · intro h
    obtain ⟨d, hd⟩ := h motor (by simp)
    simp [DriveEnv.none] at hd

/-! ## §8 Partial vs executable -/

/-- **`partial_design_allows_unbound_output`**: the design with no drive
    edge at all is a valid partial design … -/
theorem partial_design_allows_unbound_output : PartialOutputWF Ωmotor ΚA ΔB DriveEnv.none :=
  ⟨fun _ _ h => by simp [DriveEnv.none] at h, fun _ _ _ h => by simp [DriveEnv.none] at h⟩

/-- … but **`executable_design_requires_complete_outputs`**: not executable. -/
theorem executable_design_requires_complete_outputs :
    ¬ ExecutableOutputs Ωmotor ΚA ΔB DriveEnv.none [motor] ∧
    ExecutableOutputs Ωmotor ΚA ΔB βB [motor] :=
  ⟨fun h => by obtain ⟨d, hd⟩ := h.2 motor (by simp); simp [DriveEnv.none] at hd,
   ⟨⟨DriveWF.ofList (by decide), SingleDriver.ofList (by decide)⟩,
    fun o ho => by simp at ho; subst ho; exact ⟨finalAngle, by decide⟩⟩⟩

/-! ## §9 Effect rows and action values (toys) -/

/-- Direct effect row: the sinks a declaration itself drives. -/
def directRow (β : DriveEnv) (d : DeclId) : List OutputId :=
  match β d with | some o => [o] | none => []

/-- Propagated row: also the sinks driven by declarations it references. -/
def propRow (Δ : DeclEnv) (β : DriveEnv) (d : DeclId) : List OutputId :=
  directRow β d ++ (match Δ.realizationOf d with
    | some b => b.refs.flatMap (directRow β)
    | none => [])

/-- **`effect_rows_add_no_new_rejection`**: single-driver is exactly
    disjointness of direct rows — the effect row duplicates `β`. -/
theorem single_driver_iff_direct_rows_disjoint (β : DriveEnv) :
    SingleDriver β ↔ ∀ d₁ d₂ o, d₁ ≠ d₂ → o ∈ directRow β d₁ → o ∉ directRow β d₂ := by
  constructor
  · intro hs d₁ d₂ o hne h₁ h₂
    simp only [directRow] at h₁ h₂
    split at h₁ <;> simp at h₁
    subst h₁
    split at h₂ <;> simp at h₂
    subst h₂
    exact hne (hs d₁ d₂ _ (by assumption) (by assumption))
  · intro hd d₁ d₂ o h₁ h₂
    by_cases hne : d₁ = d₂
    · exact hne
    · exact absurd (by simp [directRow, h₂] : o ∈ directRow β d₂) (hd d₁ d₂ o hne (by simp [directRow, h₁]))

/-- A *propagated* row flags a valid design: a display that merely reads
    the driver's value inherits `motor` and "conflicts" with it. -/
def display : DeclId := ⟨250⟩
def dDisplay : DesignDecl := ⟨display, ⟨MotorAngle, []⟩, some (.declRef finalAngle)⟩
def ΔRow : DeclEnv := .ofList [dBase, dCorr, dFinal, dDisplay]

theorem propagated_effect_rows_false_positive :
    SingleDriver βB ∧ display ≠ finalAngle ∧
    motor ∈ propRow ΔRow βB display ∧ motor ∈ propRow ΔRow βB finalAngle :=
  ⟨SingleDriver.ofList (by decide), by decide, by decide, by decide⟩

/-- Action values relocate the conflict: two requests for one sink in one
    instant are a multiset any deterministic collector must *order* — which
    is Counterexample C again. -/
abbrev Request := OutputId × Nat
def collect (policy : List Nat → Option Nat) (rs : List Request) (o : OutputId) : Option Nat :=
  policy ((rs.filter fun r => r.1 = o).map Prod.snd)

theorem action_values_relocate_conflict :
    collect firstWins [(motor, 10), (motor, 40)] motor = some 10 ∧
    collect lastWins [(motor, 10), (motor, 40)] motor = some 40 := by decide

/-! ## §10 StateHandler remainder: latched activation, exit-wins, output choice -/

def enterEv : DeclId := ⟨260⟩   -- bool input
def exitEv : DeclId := ⟨261⟩    -- bool input
def activeD : DeclId := ⟨262⟩
def heldT : DeclId := ⟨263⟩     -- MotorAngle input
def restT : DeclId := ⟨264⟩     -- MotorAngle input
def innerCond : DeclId := ⟨265⟩ -- bool input
def altT : DeclId := ⟨266⟩      -- MotorAngle input
def choiceD : DeclId := ⟨267⟩
def nestedD : DeclId := ⟨268⟩

def dEnter : DesignDecl := ⟨enterEv, ⟨.bool, []⟩, none⟩
def dExit : DesignDecl := ⟨exitEv, ⟨.bool, []⟩, none⟩
/-- Event-latched activation, **exit wins**:
    `active = (enter ∨ delay false active) ∧ ¬ exit`. -/
def dActive : DesignDecl := ⟨activeD, ⟨.bool, []⟩, some
  (and' (or' (.declRef enterEv) (.delay (.boolLit false) (.declRef activeD))) (not' (.declRef exitEv)))⟩
def dHeldT : DesignDecl := ⟨heldT, ⟨MotorAngle, []⟩, none⟩
def dRestT : DesignDecl := ⟨restT, ⟨MotorAngle, []⟩, none⟩
def dInner : DesignDecl := ⟨innerCond, ⟨.bool, []⟩, none⟩
def dAltT : DesignDecl := ⟨altT, ⟨MotorAngle, []⟩, none⟩
/-- State-local output choice: one driver selects by activation. -/
def dChoice : DesignDecl := ⟨choiceD, ⟨MotorAngle, []⟩, some
  (ite' MotorAngle (.declRef activeD) (.declRef heldT) (.declRef restT))⟩
/-- Nested handler with output: the inner choice is nested in the outer one. -/
def dNested : DesignDecl := ⟨nestedD, ⟨MotorAngle, []⟩, some
  (ite' MotorAngle (.declRef activeD) (ite' MotorAngle (.declRef innerCond) (.declRef heldT) (.declRef altT)) (.declRef restT))⟩
def ΔSH : DeclEnv := .ofList [dEnter, dExit, dActive, dHeldT, dRestT, dInner, dAltT, dChoice, dNested]
def βSH : DriveEnv := .ofList [(nestedD, motor)]
def ΚSH : ClockEnv := fun _ => Option.some actuatorClock

/-- enter at 1 and 5, exit at 3 and 5 (simultaneous at 5: exit wins). -/
def ISH : Input := fun d t =>
  if d = enterEv then .bool (t = 1 ∨ t = 5)
  else if d = exitEv then .bool (t = 3 ∨ t = 5)
  else if d = innerCond then .bool (t = 2)
  else if d = heldT then .sem cMotor (.nat 90)
  else if d = restT then .sem cMotor (.nat 0)
  else if d = altT then .sem cMotor (.nat 45)
  else .nat 0

def rb (d : DeclId) (t : Nat) : Option Bool := (evalF ΔSH ISH 64 t [] (.declRef d)).bind Value.toBool?
def rm (d : DeclId) (t : Nat) : Option Nat :=
  (evalF ΔSH ISH 64 t [] (.declRef d)).bind fun v => match v with | .sem _ (.nat n) => Option.some n | _ => Option.none

theorem statehandler_output_cases :
    GlobalWF trivEv Dimension.Θdim ΔSH ∧ SingleDriver βSH ∧ DriveWF Ωmotor ΚSH ΔSH βSH ∧
    [rb activeD 0, rb activeD 1, rb activeD 2, rb activeD 3, rb activeD 4, rb activeD 5]
      = [some false, some true, some true, some false, some false, some false] ∧
    [rm choiceD 0, rm choiceD 1, rm choiceD 3] = [some 0, some 90, some 0] ∧
    [rm nestedD 1, rm nestedD 2, rm nestedD 3] = [some 45, some 90, some 0] :=
  ⟨GlobalWF.ofList (by decide), SingleDriver.ofList (by decide), DriveWF.ofList (by decide),
   by decide, by decide, by decide⟩

/-! ## §11 Physical output semantics and determinism -/

/-- And without it the output is *not* a function: Counterexample A's two
    drivers deliver `base` and `corr`, which differ. -/
def IA : Input := fun d _ =>
  if d = baseAngle then .sem cMotor (.nat 10) else if d = corrAngle then .sem cMotor (.nat 40) else .nat 0

theorem two_drivers_two_outputs :
    PhysicalOutput S₂ ΔA IA Ωmotor βA motor 0 (.sem cMotor (.nat 10)) ∧
    PhysicalOutput S₂ ΔA IA Ωmotor βA motor 0 (.sem cMotor (.nat 40)) := by
  constructor
  · refine ⟨driveA, ⟨MotorAngle, actuatorClock⟩, by decide, by decide, ?_⟩
    have h : MEv S₂ ΔA IA actuatorClock 0 [] (.declRef driveA) (IA baseAngle 0) :=
      .refRealized (b := .declRef baseAngle) (by decide) (.refInput (by decide))
    simpa [IA] using h
  · refine ⟨driveB, ⟨MotorAngle, actuatorClock⟩, by decide, by decide, ?_⟩
    have h : MEv S₂ ΔA IA actuatorClock 0 [] (.declRef driveB) (IA corrAngle 0) :=
      .refRealized (b := .declRef corrAngle) (by decide) (.refInput (by decide))
    simpa [IA, baseAngle, corrAngle] using h

end BDL.Experiments.Output
