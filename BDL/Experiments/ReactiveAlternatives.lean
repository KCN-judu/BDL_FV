import BDL.Core.Reactive
import BDL.Experiments.DimensionAlternatives

/-!
# Phase 4 — Reactive Core

One logical tick domain.  Every declaration denotes a stream; unresolved
declarations are the *inputs* (their values come from an `Input`); realized
declarations are re-evaluated at every tick.  The single temporal primitive
under test is

    delay init e        -- the value of `e` one tick ago; `init` at tick 0

`Ty` is unchanged: "signalness" lives in the execution judgment, not in the
type (§A below).  Events are `opt τ` streams (§E).

The general theory (values, `Ev`, determinism, totality, provenance,
unfolding vs stepping) was promoted to `BDL/Core/Reactive.lean`.  This file
keeps the concrete designs and the rejected alternatives:

* §2  Cycles: an algebraic loop (no value), a delayed loop and a self-delay
      (run), a mixed graph (rejected), and the lambda-guarded gap.
* §5  Derived operators: `previous`, `hold`, `count`, `since`, `once`,
      `every`, `rise`, and a StateHandler-style scoped reset counter — each
      a declaration graph with a self-delayed cycle, checked by execution.
* §6  Initialization alternatives.  §7  Event vs `opt`.
* §9  Delay vs dimensions, semantic types, refinement.  §10  Signal as a type.
-/

namespace BDL.Experiments.Reactive
open BDL BDL.Reactive BDL.Experiments.Semantic

/-! ## §2 Cycles -/

def A : DeclId := ⟨70⟩
def B : DeclId := ⟨71⟩

/-- `A := B`, `B := A` — well typed, structurally *and* instantaneously cyclic. -/
def Δalg : DeclEnv := .ofList
  [⟨A, ⟨.q Dim.zero, []⟩, some (.declRef B)⟩, ⟨B, ⟨.q Dim.zero, []⟩, some (.declRef A)⟩]

theorem algebraic_loop_well_typed : GlobalWF trivEv ConceptEnv.empty Δalg := GlobalWF.ofList (by decide)
theorem algebraic_loop_strict_cyclic : StrictReaches Δalg A A := ⟨B, by decide, .single (by decide)⟩
theorem algebraic_loop_no_value (I : Input) (t : Nat) : ¬ ∃ v, Ev Δalg I t [] (.declRef A) v :=
  Ev.not_of_strictCyclic algebraic_loop_strict_cyclic t []

/-- `A := delay 0 B`, `B := A` — the same structural cycle through a delay. -/
def Δdel : DeclEnv := .ofList
  [⟨A, ⟨.q Dim.zero, []⟩, some (.delay (.prim (.lit Dim.zero 0)) (.declRef B))⟩,
   ⟨B, ⟨.q Dim.zero, []⟩, some (.declRef A)⟩]

theorem delayed_loop_well_typed : GlobalWF trivEv ConceptEnv.empty Δdel := GlobalWF.ofList (by decide)

/-- Structurally it is still a cycle (Phase 1: no unfolding) … -/
theorem delayed_loop_structurally_cyclic : Reaches Δdel A A := ⟨B, by decide, .single (by decide)⟩
theorem delayed_loop_does_not_unfold : ¬ ∃ e', Unfolds Δdel (.declRef A) e' :=
  Unfolds.not_of_cyclic delayed_loop_structurally_cyclic

/-- … but instantaneously it is not: only `B → A` is an instantaneous edge. -/
theorem delayed_loop_causal : Causal Δdel :=
  ⟨fun d => if d = B then 1 else 0, 2, by intro d; by_cases h : d = B <;> simp [h], by
    intro a b hab
    have : (a = B ∧ b = A) := by
      obtain ⟨e, he, hb⟩ := InstDependsOn.iff.mp hab
      simp only [DeclEnv.realizationOf, Option.bind_eq_some_iff] at he
      obtain ⟨dh, hdh, hre⟩ := he
      obtain ⟨hmem, hid⟩ := DeclEnv.ofList_some hdh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · simp at hre; subst hre; simp [Expr.instRefs] at hb
      · simp at hre; subst hre; simp [Expr.instRefs] at hb; subst hb; exact ⟨hid.symm, rfl⟩
    obtain ⟨rfl, rfl⟩ := this
    decide⟩

/-- **`delayed_cycle_is_causal`**: and it *runs* — `A` is `0` at every tick
    (proved by induction on the tick, not by fuel). -/
theorem Δdel_A : Δdel.realizationOf A = some (.delay (.prim (.lit Dim.zero 0)) (.declRef B)) := by decide
theorem Δdel_B : Δdel.realizationOf B = some (.declRef A) := by decide

theorem delayed_loop_runs (I : Input) : ∀ t, Ev Δdel I t [] (.declRef A) (.nat 0) := by
  intro t
  induction t with
  | zero => exact .refRealized Δdel_A (.delayZero (Ev.lit _ _))
  | succ t ih => exact .refRealized Δdel_A (.delaySucc (.refRealized Δdel_B ih))

/-- Self-delay, the smallest legal cycle: `A := delay 0 A`. -/
def Δself : DeclEnv := .ofList [⟨A, ⟨.q Dim.zero, []⟩, some (.delay (.prim (.lit Dim.zero 0)) (.declRef A))⟩]
theorem self_delay_causal : Causal Δself :=
  ⟨fun _ => 0, 1, fun _ => Nat.zero_lt_one, by
    intro a b hab
    obtain ⟨e, he, hb⟩ := InstDependsOn.iff.mp hab
    simp only [DeclEnv.realizationOf, Option.bind_eq_some_iff] at he
    obtain ⟨dh, hdh, hre⟩ := he
    obtain ⟨hmem, _⟩ := DeclEnv.ofList_some hdh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    subst hmem; simp at hre; subst hre; simp [Expr.instRefs] at hb⟩
theorem Δself_A : Δself.realizationOf A = some (.delay (.prim (.lit Dim.zero 0)) (.declRef A)) := by decide

theorem self_delay_runs (I : Input) : ∀ t, Ev Δself I t [] (.declRef A) (.nat 0) := by
  intro t
  induction t with
  | zero => exact .refRealized Δself_A (.delayZero (Ev.lit _ _))
  | succ t ih => exact .refRealized Δself_A (.delaySucc ih)

/-- Mixed: `A := delay 0 B`, `B := A + C`, `C := B` — the cycle `B → C → B`
    is instantaneous, so the design is rejected even though another cycle
    is delayed.  Removing delayed edges must leave the *whole* graph acyclic. -/
def C : DeclId := ⟨72⟩
def Δmixed : DeclEnv := .ofList
  [⟨A, ⟨.q Dim.zero, []⟩, some (.delay (.prim (.lit Dim.zero 0)) (.declRef B))⟩,
   ⟨B, ⟨.q Dim.zero, []⟩, some (.app (.app (.prim (.add Dim.zero)) (.declRef A)) (.declRef C))⟩,
   ⟨C, ⟨.q Dim.zero, []⟩, some (.declRef B)⟩]
theorem mixed_strict_cyclic : StrictReaches Δmixed B B := ⟨C, by decide, .single (by decide)⟩
theorem mixed_no_value (I : Input) (t : Nat) : ¬ ∃ v, Ev Δmixed I t [] (.declRef B) v :=
  Ev.not_of_strictCyclic mixed_strict_cyclic t []

/-- The gap between the two criteria: `A := λx. A x` is *not* causal (its
    body refers to `A` instantaneously), yet `declRef A` evaluates — to a
    closure.  Only applying it diverges.  `Causal` is conservative here;
    the negative theorem covers only strict cycles.  Recorded, not hidden. -/
def Δlamloop : DeclEnv := .ofList
  [⟨A, ⟨.arr (.q Dim.zero) (.q Dim.zero), []⟩, some (.lam (.q Dim.zero) (.app (.declRef A) (.var 0)))⟩]
theorem lamloop_inst_cyclic : InstDependsOn Δlamloop A A := by decide
theorem lamloop_not_strict_cyclic : ¬ StrictDependsOn Δlamloop A A := by decide
theorem lamloop_evaluates (I : Input) (t : Nat) :
    Ev Δlamloop I t [] (.declRef A) (.clo [] (.app (.declRef A) (.var 0))) :=
  .refRealized (b := .lam (.q Dim.zero) (.app (.declRef A) (.var 0))) (by decide) .lam

/-! ## §5 Derived operators — every one a self-delayed declaration

With `delay` as the only state primitive and the plain operators of
`Prim`, the designer-facing temporal vocabulary is a set of declaration
shapes.  Each is checked by execution on a concrete input trace. -/

def xIn   : DeclId := ⟨80⟩   -- q 0 input
def evIn  : DeclId := ⟨81⟩   -- opt (q 0) input: an event
def bIn   : DeclId := ⟨82⟩   -- bool input
def prevD : DeclId := ⟨83⟩
def prevO : DeclId := ⟨84⟩
def holdD : DeclId := ⟨85⟩
def countD : DeclId := ⟨86⟩
def sinceD : DeclId := ⟨87⟩
def onceD : DeclId := ⟨88⟩
def everyD : DeclId := ⟨89⟩
def riseD : DeclId := ⟨90⟩
def enterD : DeclId := ⟨91⟩
def cntD : DeclId := ⟨92⟩

abbrev Q0 : Ty := .q Dim.zero
def lit0 : Expr := .prim (.lit Dim.zero 0)
def lit1 : Expr := .prim (.lit Dim.zero 1)
def lit2 : Expr := .prim (.lit Dim.zero 2)
def add0 (a b : Expr) : Expr := .app (.app (.prim (.add Dim.zero)) a) b
def ite' (τ : Ty) (c a b : Expr) : Expr := .app (.app (.app (.prim (.ite τ)) c) a) b
def isSome' (τ : Ty) (e : Expr) : Expr := .app (.prim (.isSome τ)) e
def getD' (τ : Ty) (o d : Expr) : Expr := .app (.app (.prim (.getD τ)) o) d
def and' (a b : Expr) : Expr := .app (.app (.prim .and) a) b
def or' (a b : Expr) : Expr := .app (.app (.prim .or) a) b
def not' (a : Expr) : Expr := .app (.prim .not) a
def eq0 (a b : Expr) : Expr := .app (.app (.prim (.eq Dim.zero)) a) b

/-- `previous x` with an initial value **is** `delay`. -/
def dPrev  : DesignDecl := ⟨prevD, ⟨Q0, []⟩, some (.delay lit0 (.declRef xIn))⟩
/-- `previous x` without an initial value is `delay none (some x)`: the
    absence is pushed to the consumer as an `opt` (Model B of §6). -/
def dPrevO : DesignDecl := ⟨prevO, ⟨.opt Q0, []⟩, some (.delay (.prim (.none Q0)) (.app (.prim (.some Q0)) (.declRef xIn)))⟩
/-- `hold init ev`: latch the last occurrence.  Self-delayed. -/
def dHold  : DesignDecl := ⟨holdD, ⟨Q0, []⟩, some (getD' Q0 (.declRef evIn) (.delay lit0 (.declRef holdD)))⟩
/-- `count ev`: occurrences so far.  Self-delayed. -/
def dCount : DesignDecl := ⟨countD, ⟨Q0, []⟩, some
  (ite' Q0 (isSome' Q0 (.declRef evIn)) (add0 lit1 (.delay lit0 (.declRef countD))) (.delay lit0 (.declRef countD)))⟩
/-- `since ev`: ticks since the last occurrence (0 at an occurrence). -/
def dSince : DesignDecl := ⟨sinceD, ⟨Q0, []⟩, some
  (ite' Q0 (isSome' Q0 (.declRef evIn)) lit0 (add0 lit1 (.delay lit0 (.declRef sinceD))))⟩
/-- `once ev`: has it ever occurred — a latched boolean. -/
def dOnce  : DesignDecl := ⟨onceD, ⟨.bool, []⟩, some (or' (.delay (.boolLit false) (.declRef onceD)) (isSome' Q0 (.declRef evIn)))⟩
/-- `every 3`: a modulo-3 tick counter; "fires" when it reads 0. -/
def dEvery : DesignDecl := ⟨everyD, ⟨Q0, []⟩, some
  (ite' Q0 (eq0 (.delay lit2 (.declRef everyD)) lit2) lit0 (add0 lit1 (.delay lit2 (.declRef everyD))))⟩
/-- `rise b`: the event of `b` becoming true. -/
def dRise  : DesignDecl := ⟨riseD, ⟨.opt .bool, []⟩, some
  (ite' (.opt .bool) (and' (.declRef bIn) (not' (.delay (.boolLit false) (.declRef bIn))))
    (.app (.prim (.some .bool)) (.boolLit true)) (.prim (.none .bool)))⟩
/-- StateHandler-style scope: while `bIn` holds, count ticks, **reset on
    entry**, zero when inactive.  Activation is a boolean; entry is its rising
    edge; the local state is a delayed cell gated by activation. -/
def dEnter : DesignDecl := ⟨enterD, ⟨.bool, []⟩, some (and' (.declRef bIn) (not' (.delay (.boolLit false) (.declRef bIn))))⟩
def dCnt   : DesignDecl := ⟨cntD, ⟨Q0, []⟩, some
  (ite' Q0 (.declRef bIn) (ite' Q0 (.declRef enterD) lit0 (add0 lit1 (.delay lit0 (.declRef cntD)))) lit0)⟩

def dX  : DesignDecl := ⟨xIn, ⟨Q0, []⟩, none⟩
def dEv : DesignDecl := ⟨evIn, ⟨.opt Q0, []⟩, none⟩
def dB  : DesignDecl := ⟨bIn, ⟨.bool, []⟩, none⟩

def Δops : DeclEnv := .ofList [dX, dEv, dB, dPrev, dPrevO, dHold, dCount, dSince, dOnce, dEvery, dRise, dEnter, dCnt]

/-- All derived operators are well typed with `Ty` unchanged: no `Signal`,
    no `Event`, no operator-specific rule. -/
theorem ops_well_typed : GlobalWF trivEv ConceptEnv.empty Δops := GlobalWF.ofList (by decide)

/-- Inputs at rank 0, derived declarations at rank 1, the scoped counter
    (which reads `enterD` instantaneously) at rank 2. -/
def opsRank : DeclId → Nat := fun d =>
  if d = cntD then 2 else if d = xIn ∨ d = evIn ∨ d = bIn then 0 else 1

theorem ops_causal : Causal Δops :=
  Causal.ofList opsRank 3 (by intro d; unfold opsRank; split <;> (try split) <;> decide) (by decide)

/-- Every one of them is a *structural* cycle: none unfolds (Phase 1). -/
theorem count_does_not_unfold : ¬ ∃ e', Unfolds Δops (.declRef countD) e' :=
  Unfolds.not_of_cyclic ⟨countD, by decide, .refl _⟩

/-- Concrete inputs: `x = t`, events at ticks 1, 2 and 4, `b` true at 1–3 and 5. -/
def Iops : Input := fun d t =>
  if d = xIn then .nat t
  else if d = evIn then (if t = 1 ∨ t = 2 ∨ t = 4 then .some (.nat t) else .none)
  else if d = bIn then .bool (t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 5)
  else .nat 0

/-- Read a numeric declaration at a tick through the interpreter. -/
def runNat (d : DeclId) (t : Nat) : Option Nat := (evalF Δops Iops 64 t [] (.declRef d)).bind Value.toNat?
def runBool (d : DeclId) (t : Nat) : Option Bool := (evalF Δops Iops 64 t [] (.declRef d)).bind Value.toBool?

theorem previous_trace : [runNat prevD 0, runNat prevD 1, runNat prevD 2, runNat prevD 3] = [some 0, some 0, some 1, some 2] := by decide
theorem hold_trace     : [runNat holdD 0, runNat holdD 1, runNat holdD 2, runNat holdD 3, runNat holdD 4] = [some 0, some 1, some 2, some 2, some 4] := by decide
theorem count_trace    : [runNat countD 0, runNat countD 1, runNat countD 2, runNat countD 3, runNat countD 4] = [some 0, some 1, some 2, some 2, some 3] := by decide
theorem since_trace    : [runNat sinceD 0, runNat sinceD 1, runNat sinceD 2, runNat sinceD 3, runNat sinceD 4] = [some 1, some 0, some 0, some 1, some 0] := by decide
theorem once_trace     : [runBool onceD 0, runBool onceD 1, runBool onceD 2, runBool onceD 3] = [some false, some true, some true, some true] := by decide
theorem every_trace    : [runNat everyD 0, runNat everyD 1, runNat everyD 2, runNat everyD 3, runNat everyD 4] = [some 0, some 1, some 2, some 0, some 1] := by decide
theorem enter_trace    : [runBool enterD 0, runBool enterD 1, runBool enterD 2, runBool enterD 3, runBool enterD 4, runBool enterD 5] = [some false, some true, some false, some false, some false, some true] := by decide
/-- Reset on entry, counting while active, zero when inactive. -/
theorem scoped_counter_trace :
    [runNat cntD 0, runNat cntD 1, runNat cntD 2, runNat cntD 3, runNat cntD 4, runNat cntD 5] = [some 0, some 0, some 1, some 2, some 0, some 0] := by decide

/-! ## §6 Initialization alternatives

* A — `delay init e` (chosen): total and deterministic from tick 0.
* B — `previous : τ → opt τ`: derivable as `delay none (some e)` (`dPrevO`);
  the first-tick case is pushed to every consumer.
* C — declaration-level initial state: the same as A once state is per
  declaration (a `delay` is per declaration).
* D — no initial value: either *undefined* or *nondeterministic* at tick 0. -/

/-- Toy: a bare `pre` with no init, as a stream relation. -/
inductive PreUndef (src : Nat → Value) : Nat → Value → Prop where
  | succ {t} : PreUndef src (t + 1) (src t)

theorem first_tick_undefined_without_init (src : Nat → Value) : ¬ ∃ v, PreUndef src 0 v := by
  rintro ⟨v, h⟩; cases h

/-- Toy: a bare `pre` whose first value is "anything". -/
inductive PreAny (src : Nat → Value) : Nat → Value → Prop where
  | zero (v : Value) : PreAny src 0 v
  | succ {t} : PreAny src (t + 1) (src t)

theorem first_tick_nondeterministic_without_init (src : Nat → Value) :
    ∃ v₁ v₂, PreAny src 0 v₁ ∧ PreAny src 0 v₂ ∧ v₁ ≠ v₂ :=
  ⟨.nat 0, .nat 1, .zero _, .zero _, by simp⟩

/-! ## §7 Event vs `opt` — the observation model decides

In one logical domain an input delivers one value per tick (`Input`), so an
event input is an `opt` stream *by construction*.  Multiplicity ("two
occurrences between sampling points") is only observable when a source
ticks faster than its observer — a cross-domain notion, deferred to Phase 5
where the paper itself places it (§4.8.2). -/

/-- Cross-domain observation: a multiset of occurrences per tick. -/
abbrev MultiStream := Nat → List Value
/-- Single-domain observation. -/
abbrev OptStream := Nat → Option Value

def optToList : Option Value → List Value
  | Option.none => []
  | Option.some v => [v]

theorem optToList_injective {a b : Option Value} (h : optToList a = optToList b) : a = b := by
  cases a <;> cases b <;> simp [optToList] at h ⊢; exact h

/-- **`event_encoding_equivalent`** (single domain): the `opt` encoding is
    exactly the multiplicity-≤1 streams. -/
theorem event_encoding_equivalent (f : MultiStream) :
    (∀ t, (f t).length ≤ 1) ↔ ∃ g : OptStream, ∀ t, optToList (g t) = f t := by
  constructor
  · intro h
    refine ⟨fun t => (f t).head?, fun t => ?_⟩
    have := h t
    cases hf : f t with
    | nil => simp only [hf, List.head?_nil, optToList]
    | cons a l => rw [hf] at this; cases l with
      | nil => simp only [hf, List.head?_cons, optToList]
      | cons _ _ => simp at this
  · rintro ⟨g, hg⟩ t
    rw [← hg t]; cases g t <;> simp [optToList]

/-- **`event_encoding_loses_multiplicity`** (cross-domain): with two
    occurrences in one observation interval there is no `opt` preimage. -/
theorem event_encoding_loses_multiplicity :
    ∃ f : MultiStream, ¬ ∃ g : OptStream, ∀ t, optToList (g t) = f t := by
  refine ⟨fun _ => [.nat 0, .nat 1], ?_⟩
  rintro ⟨g, hg⟩
  have := hg 0
  cases hg0 : g 0 <;> rw [hg0] at this <;> simp [optToList] at this

/-- Consumption vs persistence is a *derived* distinction: `dHold` persists,
    `dCount` consumes; both are declaration shapes over `opt`, not event
    primitives. -/
example : True := trivial

/-! ## §8 Unfolding and stepping

* Structural acyclicity implies causality (`Causal.of_acyclic_bounded`):
  every design Phase 1 could unfold can be stepped.
* A delayed cycle steps but does not unfold (`delayed_loop_runs`,
  `delayed_loop_does_not_unfold`).
* For *wiring* designs — no lambdas, no variables — stepping over
  references and stepping over the unfolded program agree. -/

/-! ## §9 Temporal structure vs semantic types, dimensions, and refinement -/

/-- **`delay_preserves_type`** is the typing rule itself: `delay : τ → τ → τ`
    for data `τ`.  In particular dimensions do not drift … -/
theorem delay_preserves_dimension :
    HasType ConceptEnv.empty Dimension.Δdim Grant.none [] (.delay (.prim (.lit Dim.Length 0)) (.declRef Dimension.lenSensor)) (.q Dim.Length) ∧
    ¬ HasType ConceptEnv.empty Dimension.Δdim Grant.none [] (.delay (.prim (.lit Dim.Time 0)) (.declRef Dimension.lenSensor)) (.q Dim.Length) ∧
    ¬ HasType ConceptEnv.empty Dimension.Δdim Grant.none [] (.delay (.prim (.lit Dim.Length 0)) (.declRef Dimension.lenSensor)) (.q Dim.Time) := by
  decide

/-- … and time-related operations generate dimensions through the ordinary
    algebra: a backward difference divided by a time step has dimension
    `Length − Time`.  No derivative primitive is needed for the representation
    to support one. -/
def dtDecl : DeclId := ⟨95⟩
def Δrate : DeclEnv := .ofList [Dimension.dLen, ⟨dtDecl, ⟨.q Dim.Time, []⟩, none⟩]
theorem backward_difference_rate_typed :
    HasType ConceptEnv.empty Δrate Grant.none []
      (.app (.app (.prim (.div Dim.Length Dim.Time))
        (.app (.app (.prim (.sub Dim.Length)) (.declRef Dimension.lenSensor))
          (.delay (.prim (.lit Dim.Length 0)) (.declRef Dimension.lenSensor))))
        (.declRef dtDecl))
      (.q (Dim.Length.sub Dim.Time)) := by
  decide

/-- Semantic values can be delayed (they are data) and the grant discipline
    is untouched: re-labelling a *stored* tilt as a motor angle still needs
    the construction grant, and `previous (rep x)` equals `rep (previous x)`
    — representation access is not stateful. -/
def tiltSensorD : DesignDecl := ⟨tiltSensor, ⟨Tilt, []⟩, none⟩
def Δsem : DeclEnv := .ofList [tiltSensorD]
def initTilt : Expr := .mk cTilt (.prim (.lit Dim.Angle 0))

theorem semantic_delay_typed_and_isolated :
    HasType Dimension.Θdim Δsem (Grant.of Tilt) [] (.delay initTilt (.declRef tiltSensor)) Tilt ∧
    ¬ HasType Dimension.Θdim Δsem Grant.none [] (.mk cMotor (.rep (.delay initTilt (.declRef tiltSensor)))) MotorAngle ∧
    ¬ HasType Dimension.Θdim Δsem (Grant.of (Ty.arr Tilt Brightness)) []
        (.mk cMotor (.rep (.delay initTilt (.declRef tiltSensor)))) MotorAngle := by
  decide

/-- **Temporal changes are edits.**  Adding a delay, removing one, or
    changing an initial value replaces the realization, which is write-once
    (Phase 1): none is a `DeclLeq` step, so none is covered by the
    preservation theorems and all require rechecking dependents. -/
theorem temporal_change_is_edit :
    ¬ DeclLeq ⟨prevD, ⟨Q0, []⟩, some (.declRef xIn)⟩ dPrev ∧                      -- add a delay
    ¬ DeclLeq dPrev ⟨prevD, ⟨Q0, []⟩, some (.declRef xIn)⟩ ∧                      -- remove it
    ¬ DeclLeq dPrev ⟨prevD, ⟨Q0, []⟩, some (.delay lit1 (.declRef xIn))⟩ := by  -- change init
  decide

/-! ## §10 Signal as a type — not needed in one domain

Everything above is typed with `Ty` unchanged.  A constructor `Signal τ`
would, under this semantics, be inhabited by exactly the terms of type `τ`
(every declaration is a stream; a constant is a constant stream), so it
would distinguish nothing and reject nothing.  Where a signal type *does*
carry information is the domain index `Signal[d]` of Phase 5 — which is
information about *which clock*, not about *being a stream*.  Claim
strength: engineering preference, supported by the fact that no result in
this file needed the constructor. -/

end BDL.Experiments.Reactive
