import BDL.Core.Clock
import BDL.Experiments.ReactiveAlternatives

/-!
# Phase 5 — Clock domains and synchronization

Time model: one global base tick; a **schedule** `S : ClockId → Nat → Bool`
says at which global ticks each domain activates.  No physical time, no
numeric rates in the kernel (a period *induces* a schedule, `Sched.periodic`).

Clock identity is nominal (`ClockId`), attached to declarations through a
projection `ClockEnv Κ : DeclId → Option ClockId` (`none` = domain-agnostic
pure mapping).  A separate **domain judgment** `Clocked` (Model D) checks
that every reference stays in its domain unless it goes through the one
transport primitive

    sync src init e    -- e at the last activation of src strictly before now; init if none

`Ty`, `HasType`, `tyView` are unchanged.

The general theory (schedules, `Clocked`, `MEv`, determinism, embedding,
`delay = sync`, provenance, totality, the window identity) was promoted to
`BDL/Core/Clock.lean`.  This file keeps the concrete designs and the
rejected alternatives:

* §6 counterexamples A, B, E, F and the direct-wire/transport results;
* §7 concept identity and dimension across domains (typing);
* §10 event transport: `opt` under `sync` loses events; the window example;
  policies compared;
* §11 clocks in types (toy).
-/

namespace BDL.Experiments.Clock
open BDL BDL.Reactive BDL.Clock BDL.Experiments.Semantic BDL.Experiments.Reactive

/-! ## §6 The concrete multi-rate design and the counterexamples -/

def fast : ClockId := ⟨0⟩
def slow : ClockId := ⟨1⟩
def other : ClockId := ⟨2⟩

/-- `fast` every tick, `slow` every third tick, `other` on odd ticks. -/
def S₂ : Sched := fun c t =>
  if c = slow then decide (t % 3 = 0) else if c = other then decide (t % 2 = 1) else true

def xF   : DeclId := ⟨100⟩   -- fast input, value = t
def yS   : DeclId := ⟨101⟩   -- slow, transported from xF
def zS   : DeclId := ⟨102⟩   -- slow, delayed yS
def wireS : DeclId := ⟨103⟩  -- slow, *direct* wire to xF (rejected)
def pureM : DeclId := ⟨104⟩  -- agnostic mapping
def useF : DeclId := ⟨105⟩   -- fast use of the mapping
def useS : DeclId := ⟨106⟩   -- slow use of the mapping

def dXF : DesignDecl := ⟨xF, ⟨Q0, []⟩, none⟩
def dYS : DesignDecl := ⟨yS, ⟨Q0, []⟩, some (.sync fast lit0 (.declRef xF))⟩
def dZS : DesignDecl := ⟨zS, ⟨Q0, []⟩, some (.delay lit0 (.declRef yS))⟩
def dWireS : DesignDecl := ⟨wireS, ⟨Q0, []⟩, some (.declRef xF)⟩
def dPure : DesignDecl := ⟨pureM, ⟨.arr Q0 Q0, []⟩, some (.lam Q0 (add0 (.var 0) lit1))⟩
def dUseF : DesignDecl := ⟨useF, ⟨Q0, []⟩, some (.app (.declRef pureM) (.declRef xF))⟩
def dUseS : DesignDecl := ⟨useS, ⟨Q0, []⟩, some (.app (.declRef pureM) (.declRef yS))⟩

def Κ₁ : ClockEnv := fun d =>
  if d = xF ∨ d = useF then Option.some fast
  else if d = yS ∨ d = zS ∨ d = wireS ∨ d = useS then Option.some slow
  else Option.none   -- pureM agnostic

def Δgood : DeclEnv := .ofList [dXF, dYS, dZS, dPure, dUseF, dUseS]
def Δbad  : DeclEnv := .ofList [dXF, dWireS]

/-- Typing is blind to domains: both designs are globally well typed. -/
theorem both_well_typed : GlobalWF trivEv ConceptEnv.empty Δgood ∧ GlobalWF trivEv ConceptEnv.empty Δbad :=
  ⟨GlobalWF.ofList (by decide), GlobalWF.ofList (by decide)⟩

/-- **`cross_domain_direct_wire_rejected`** — the temporal analogue of
    Phase 2's "same representation ≠ same concept identity": same value type
    does not imply connectability across domains. -/
theorem cross_domain_direct_wire_rejected : ¬ Clocked Κ₁ (Κ₁ wireS) (.declRef xF) := by decide

/-- **`explicit_transport_accepted`**, and an agnostic mapping serves both
    domains with a single declaration (§11 contrasts this with clocked types). -/
theorem explicit_transport_accepted : WellClocked Κ₁ Δgood := WellClocked.ofList (by decide)

def I₂ : Input := fun d t => if d = xF then .nat t else .nat 0
def run (Δ : DeclEnv) (I : Input) (c : ClockId) (d : DeclId) (t : Nat) : Option Nat :=
  (mevalF S₂ Δ I 64 c t [] (.declRef d)).bind Value.toNat?

/-- Zero-order hold: at slow ticks 0, 3, 6 the slow side sees `x` at fast
    ticks —, 2, 5 (strictly before), with the explicit initial value first. -/
theorem transport_trace : [run Δgood I₂ slow yS 0, run Δgood I₂ slow yS 3, run Δgood I₂ slow yS 6] = [some 0, some 2, some 5] := by
  decide

/-- **`delay_is_domain_relative`**: a slow `delay` reads the previous *slow*
    activation (three global ticks back), with the same syntax as a fast one. -/
theorem delay_is_domain_relative :
    [run Δgood I₂ slow zS 3, run Δgood I₂ slow zS 6] = [some 0, some 2] ∧
    [run Δgood I₂ fast useF 3, run Δgood I₂ fast useF 4] = [some 4, some 5] := by
  decide

/-- **Counterexample A — the unpolicied wire is ambiguous.**  Between the
    slow activations at 0 and 3 the fast source produced `[0, 1, 2]`; every
    one of these "obvious" readings is type-correct at `q 0` and they all
    differ.  The representation type cannot choose. -/
def windowVals (S : Sched) (src : ClockId) (lo hi : Nat) (h : Nat → Nat) : List Nat :=
  ((List.range hi).filter fun u => decide (lo ≤ u) && S src u).map h

theorem unpolicied_wire_ambiguous :
    let w := windowVals S₂ fast 0 3 (fun t => t)
    w = [0, 1, 2] ∧
    w.getLast? = some 2 ∧ w.head? = some 0 ∧ w.length = 3 ∧ w.sum = 3 ∧
    (2 : Nat) ≠ 0 ∧ (2 : Nat) ≠ 3 := by
  decide

/-- **Counterexample B — equal rate is not the same domain.**  `fast` and a
    clone with the same schedule are different `ClockId`s: a direct wire
    between them is rejected; and a clone shifted in phase (`other`, odd
    ticks) shows why identity, not rate, is what transport reads. -/
def fastClone : ClockId := ⟨3⟩
def S₃ : Sched := fun c t => if c = fastClone then S₂ fast t else S₂ c t
def xC : DeclId := ⟨107⟩
def dXC : DesignDecl := ⟨xC, ⟨Q0, []⟩, some (.declRef xF)⟩
def Κ₂ : ClockEnv := fun d => if d = xF then Option.some fast else if d = xC then Option.some fastClone else Option.none

theorem equal_rate_not_same_domain :
    (∀ t, S₃ fast t = S₃ fastClone t) ∧ ¬ Clocked Κ₂ (Κ₂ xC) (.declRef xF) := by
  refine ⟨fun t => by simp [S₃, S₂, fast, fastClone, slow, other], by decide⟩

/-- Same nominal rate, different phase: reading `x` from `other` (odd ticks)
    through `sync` sees the value from the previous *fast* tick — a
    same-domain read would see the current one.  Rate equality would have
    hidden this. -/
def xO : DeclId := ⟨108⟩
def dXO : DesignDecl := ⟨xO, ⟨Q0, []⟩, some (.sync fast lit0 (.declRef xF))⟩
def Δphase : DeclEnv := .ofList [dXF, dXO]
theorem phase_matters : [run Δphase I₂ other xO 1, run Δphase I₂ other xO 3] = [some 0, some 2] := by decide

/-- **Counterexample E — changing a producer's domain invalidates unchanged
    clients.**  Move `xF` to `slow`: `useF` (fast, untouched) is no longer
    well-clocked; `yS`'s transport now names the wrong source domain too. -/
def Κ₁' : ClockEnv := fun d => if d = xF then Option.some slow else Κ₁ d
theorem clock_change_invalidates_clients :
    Clocked Κ₁ (Κ₁ useF) (.app (.declRef pureM) (.declRef xF)) ∧
    ¬ Clocked Κ₁' (Κ₁' useF) (.app (.declRef pureM) (.declRef xF)) := by
  decide

/-- Assigning a domain to an agnostic declaration also invalidates clients in
    other domains: `pureM` served both; pinned to `fast`, `useS` breaks. -/
def Κ₁'' : ClockEnv := fun d => if d = pureM then Option.some fast else Κ₁ d
theorem clock_assignment_invalidates_clients :
    Clocked Κ₁ (Κ₁ useS) (.app (.declRef pureM) (.declRef yS)) ∧
    ¬ Clocked Κ₁'' (Κ₁'' useS) (.app (.declRef pureM) (.declRef yS)) := by
  decide

/-! ### Counterexample F — same-tick visibility makes scheduler order semantic

An alternative transport that lets a domain see a *simultaneously* active
source's current value must decide who runs first.  Encode "who runs first"
as a priority and show two priorities give two outputs.  `MEv` has no such
parameter: strictly-before reads are order-free (`MEv.det`). -/

/-- Last activation of `c` at or before `t`. -/
def lastActLE (S : Sched) (c : ClockId) (t : Nat) : Option Nat :=
  if S c t then Option.some t else prevAct S c t

/-- Same-tick-visible transport with a priority: a lower-priority source
    (evaluated earlier in the same instant) is read at-or-before `t`. -/
inductive MEvLE (S : Sched) (pri : ClockId → Nat) (Δ : DeclEnv) (I : Input) : ClockId → Nat → Expr → Value → Prop where
  | prim {c t p} : MEvLE S pri Δ I c t (.prim p) (applyPrim p [])
  | refInput {c t d} : Δ.realizationOf d = none → MEvLE S pri Δ I c t (.declRef d) (I d t)
  | refRealized {c t d b v} : Δ.realizationOf d = some b → MEvLE S pri Δ I c t b v → MEvLE S pri Δ I c t (.declRef d) v
  | syncEarlier {c c' t t' i e v} : pri c' < pri c → lastActLE S c' t = Option.some t' →
      MEvLE S pri Δ I c' t' e v → MEvLE S pri Δ I c t (.sync c' i e) v
  | syncLater {c c' t t' i e v} : ¬ pri c' < pri c → prevAct S c' t = Option.some t' →
      MEvLE S pri Δ I c' t' e v → MEvLE S pri Δ I c t (.sync c' i e) v
  | syncLaterNone {c c' t i e v} : ¬ pri c' < pri c → prevAct S c' t = Option.none →
      MEvLE S pri Δ I c t i v → MEvLE S pri Δ I c t (.sync c' i e) v

def aF : DeclId := ⟨110⟩
def xOin : DeclId := ⟨111⟩   -- input in `other`, value = t
def dXOin : DesignDecl := ⟨xOin, ⟨Q0, []⟩, none⟩
def dAF : DesignDecl := ⟨aF, ⟨Q0, []⟩, some (.sync other lit0 (.declRef xOin))⟩
def Δorder : DeclEnv := .ofList [dXOin, dAF]
def Iorder : Input := fun d t => if d = xOin then .nat t else .nat 0
def priA : ClockId → Nat := fun c => if c = other then 0 else 1   -- `other` first
def priB : ClockId → Nat := fun c => if c = other then 1 else 0   -- `fast` first

/-- At tick 1 both `fast` and `other` are active (first activation of
    `other`).  With `other` first the transport delivers `x 1 = 1`; with
    `fast` first there is no earlier `other` activation and the initial value
    `0` is delivered.  Two orders, two outputs: the order is observable. -/
theorem scheduling_order_observable :
    MEvLE S₂ priA Δorder Iorder fast 1 (.declRef aF) (.nat 1) ∧
    MEvLE S₂ priB Δorder Iorder fast 1 (.declRef aF) (.nat 0) := by
  have hA : Δorder.realizationOf aF = some (.sync other lit0 (.declRef xOin)) := by decide
  have hX : Δorder.realizationOf xOin = none := by decide
  constructor
  · exact .refRealized hA (.syncEarlier (c' := other) (t' := 1) (by decide) (by decide) (.refInput hX))
  · have hlit : MEvLE S₂ priB Δorder Iorder fast 1 lit0 (.nat 0) := by
      have := @MEvLE.prim S₂ priB Δorder Iorder fast 1 (.lit Dim.zero 0)
      simpa [lit0, applyPrim, Prim.arity, Prim.compute] using this
    exact .refRealized hA (.syncLaterNone (c' := other) (by decide) (by decide) hlit)

/-! ## §7 Concept identity and dimension across domains (typing) -/

def tiltFast : DeclId := ⟨120⟩
def tiltSlow : DeclId := ⟨121⟩
def lenFast : DeclId := ⟨122⟩
def ΔsemX : DeclEnv := .ofList [⟨tiltFast, ⟨Tilt, []⟩, none⟩, ⟨lenFast, ⟨.q Dim.Length, []⟩, none⟩]

/-- **`transport_preserves_semantic_identity`** and **`transport_preserves_dimension`**:
    `Tilt@fast → Tilt@slow` and `q Length@fast → q Length@slow` are typed;
    a clock crossing authorizes neither `Tilt → MotorAngle` (needs the grant)
    nor `q Length → q Time`. -/
theorem transport_preserves_semantic_identity_and_dimension :
    HasType Dimension.Θdim ΔsemX (Grant.of Tilt) [] (.sync fast initTilt (.declRef tiltFast)) Tilt ∧
    ¬ HasType Dimension.Θdim ΔsemX Grant.none [] (.mk cMotor (.rep (.sync fast initTilt (.declRef tiltFast)))) MotorAngle ∧
    ¬ HasType Dimension.Θdim ΔsemX (Grant.of (Ty.arr Tilt Brightness)) []
        (.mk cMotor (.rep (.sync fast initTilt (.declRef tiltFast)))) MotorAngle ∧
    HasType ConceptEnv.empty ΔsemX Grant.none [] (.sync fast (.prim (.lit Dim.Length 0)) (.declRef lenFast)) (.q Dim.Length) ∧
    ¬ HasType ConceptEnv.empty ΔsemX Grant.none [] (.sync fast (.prim (.lit Dim.Time 0)) (.declRef lenFast)) (.q Dim.Time) := by
  decide

/-! ## §10 Event transport: `opt` under `sync`, and what buffering needs -/

def evF : DeclId := ⟨130⟩   -- fast event input
def evS : DeclId := ⟨131⟩   -- slow, transported
def dEvF : DesignDecl := ⟨evF, ⟨.opt Q0, []⟩, none⟩
def dEvS : DesignDecl := ⟨evS, ⟨.opt Q0, []⟩, some (.sync fast (.prim (.none Q0)) (.declRef evF))⟩
def Δev : DeclEnv := .ofList [dEvF, dEvS]

/-- Fast events at ticks 1 and 2 … -/
def Iev₁ : Input := fun d t => if d = evF then (if t = 1 ∨ t = 2 then .some (.nat t) else .none) else .nat 0
/-- … at tick 2 only … -/
def Iev₂ : Input := fun d t => if d = evF then (if t = 2 then .some (.nat t) else .none) else .nat 0
/-- … at tick 1 only. -/
def Iev₃ : Input := fun d t => if d = evF then (if t = 1 then .some (.nat t) else .none) else .nat 0

def runOpt (I : Input) (t : Nat) : Option (Option Nat) :=
  (mevalF S₂ Δev I 64 slow t [] (.declRef evS)).map fun v =>
    match v with
    | .some (.nat n) => Option.some n
    | _ => Option.none

/-- **Counterexample C — `opt` under zero-order hold loses events.**  Two
    events (ticks 1, 2) and one event (tick 2) are indistinguishable at the
    slow activation (tick 3), and a single event at tick 1 is *dropped*
    outright — the last fast value before 3 was `none`. -/
theorem opt_loses_multiplicity_under_sync :
    runOpt Iev₁ 3 = some (some 2) ∧ runOpt Iev₂ 3 = some (some 2) ∧ runOpt Iev₃ 3 = some none ∧
    Iev₁ evF 1 ≠ Iev₂ evF 1 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  simp [Iev₁, Iev₂]

/-- On the running example: the slow window at tick 3 is the fast ticks
    `[0, 1, 2]`; `latest` keeps one, `count + latest` two numbers, a list all. -/
theorem window_example : windowTicks S₂ fast slow 3 = [0, 1, 2] ∧ windowTicks S₂ fast slow 6 = [3, 4, 5] := by
  decide

/-- Policies as functions of the occurrence window (values at window ticks
    that carry an event).  Only the list is injective; `latest`, `count`,
    `count + latest` each identify distinct windows. -/
def occurrences (h : Nat → Option Nat) (w : List Nat) : List Nat := w.filterMap h

theorem policies_lose_information :
    let h₁ : Nat → Option Nat := fun t => if t = 1 ∨ t = 2 then some t else none
    let h₂ : Nat → Option Nat := fun t => if t = 2 then some t else none
    let h₄ : Nat → Option Nat := fun t => if t = 0 ∨ t = 2 then some t else none
    let w := [0, 1, 2]
    (occurrences h₁ w).getLast? = (occurrences h₂ w).getLast? ∧          -- latest loses
    (occurrences h₁ w).length = (occurrences h₄ w).length ∧              -- count loses
    ((occurrences h₁ w).length, (occurrences h₁ w).getLast?) =
      ((occurrences h₄ w).length, (occurrences h₄ w).getLast?) ∧         -- count + latest loses
    occurrences h₁ w ≠ occurrences h₂ w ∧ occurrences h₁ w ≠ occurrences h₄ w := by  -- the list does not
  decide

/-! ## §11 Clocks in types — a toy comparison

Under a clock-indexed type `(c, τ)`, a declaration has one type, hence one
clock; a pure mapping used from two domains needs two declarations or clock
polymorphism (the paper's `∀δ`).  Under the domain judgment, one agnostic
declaration serves both (`explicit_transport_accepted`: `pureM` is used by
`useF` and `useS`).  This is an expressiveness/minimality argument, not a
soundness one: clocked types are not *wrong*; they cost polymorphism that
the judgment does not need. -/

structure ClockedTy where
  clock : ClockId
  ty : Ty
  deriving DecidableEq

/-- A use site in domain `c` may reference a declaration of clocked type `κ`
    iff the clocks agree. -/
def usableAt (κ : ClockedTy) (c : ClockId) : Prop := κ.clock = c

theorem clocked_type_forces_polymorphism (κ : ClockedTy) : ¬ (usableAt κ fast ∧ usableAt κ slow) := by
  rintro ⟨h₁, h₂⟩
  simp only [usableAt] at h₁ h₂
  rw [h₁] at h₂
  exact absurd h₂ (by decide)

end BDL.Experiments.Clock
