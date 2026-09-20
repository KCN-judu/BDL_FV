import BDL.Surface.SourceBoundary
import BDL.Experiments.ProviderExamples
import BDL.Experiments.ProvisionExamples

/-!
# Phase 18 — the Source-side boundary, executed

* A — **provider state**: a low-pass filter as a `Machine` from its term;
  the Source provisioned from the provider running it below the raw
  reading and the Source realized from the filter placed upstream give
  the same trace and the same consumer (`exA_filter`,
  `provider_state_movable` instantiated).  Debouncing, quadrature
  decoding with accumulation and reset, and hysteresis as upstream
  designs, executed; the parameters that change the semantic trace
  (`exA_debounce_param`, `exA_hysteresis_param`) and the state that reads
  a design value and therefore cannot be a provider's (the fault latch,
  `exA_latch_reads_design`).
* B — **the Source-side device clock**: a temperature read in a provider
  domain on even ticks, the Source every tick — sampled strictly before,
  with a supplied initial reading (`exB_sampled`) and with the optional
  form, where the Source reads *unavailable* until the first sample
  (`exB_unavailable`); encoder edges in a fast provider domain windowed
  into the Source's domain and accumulated — no edge lost
  (`exB_window_edges`).
* C — **commitment discharge** at three levels on one property (a
  temperature at most 450): static from the saturating transducer,
  trusted from a declared device range, checked by a validating provider.
* D — **`computes`**: the thermistor channel built from its term
  (`exD_ofTerm`); a supplied transfer function decided at `bool`
  (`exD_bool`, a right one and a wrong one).
* E — **out-of-type readings**: a malformed and an out-of-range delivery
  refused, the flag raised, the items typed; the optional Source reads
  `none` and the design's `available` says so (`exE_checked`).
* F — **the motion state under two providers**: feedback delivered as
  batches sampled by `chLatest` and as single readings through the
  identity channel — one `fb` trace, one `doneM` trace (`exF_two_providers`).
-/

namespace BDL.Experiments.SourceBoundaryEx
open BDL BDL.Reactive BDL.Clock BDL.Output BDL.Stdlib BDL.Provision BDL.Assignment BDL.Provider BDL.SourceBoundary
open BDL.Buffer (Ids logDecl logDDecl seenDecl cursorDecl windowDecl Realized)
open BDL.DeviceClock
open BDL.Experiments.Communication (Q0 nat? bool? runB runN motionDecls ΔM fb doneM settled inM sample Sample Fb)

def lit (n : Nat) : Expr := .prim (.lit Dim.zero n)
def c0 : ClockId := ⟨0⟩
def Θ0 : ConceptEnv := fun _ => none

/-! ## A — provider state -/

/-- The low-pass filter `y := (3·prev + x) / 4` as a machine: state and
    output are the filtered value. -/
def filterStep : Expr :=
  .lam (.prod Q0 Q0)
    (pairE Q0 Q0
      (app2 (.prim (.div Dim.zero Dim.zero))
        (app2 (.prim (.add Dim.zero))
          (app2 (.prim (.mul Dim.zero Dim.zero)) (fstE Q0 Q0 (.var 0)) (lit 3)) (sndE Q0 Q0 (.var 0))) (lit 4))
      (app2 (.prim (.div Dim.zero Dim.zero))
        (app2 (.prim (.add Dim.zero))
          (app2 (.prim (.mul Dim.zero Dim.zero)) (fstE Q0 Q0 (.var 0)) (lit 3)) (sndE Q0 Q0 (.var 0))) (lit 4)))

/-- The filtered value on numbers. -/
def filterF (s x : Value) : Value × Value :=
  match s, x with
  | .nat a, .nat b => (.nat ((a * 3 + b) / 4), .nat ((a * 3 + b) / 4))
  | s, x => (s, x)

def filter : Machine Q0 Q0 Q0 where
  step := filterStep
  stepF := filterF
  init := ⟨lit 0, .nat 0, trivial, Ev.lit _ _⟩
  σ_data := trivial
  raw_data := trivial
  step_pure := by simp [filterStep, pairE, app2, fstE, sndE, lit, Expr.Pure]
  init_ty := ⟨0, rfl⟩
  computes := by
    rintro s x ⟨a, rfl⟩ ⟨b, rfl⟩
    have hfst := Ev.appPrim (Δ := DeclEnv.empty) (I := fun _ _ => Value.pair (.nat a) (.nat b)) (t := 0)
      (ρ := [.pair (.nat a) (.nat b)]) (f := .prim (.fst Q0 Q0)) (a := .var 0) (p := .fst Q0 Q0) (args := [])
      (va := .pair (.nat a) (.nat b)) .prim (.var rfl)
    have hsnd := Ev.appPrim (Δ := DeclEnv.empty) (I := fun _ _ => Value.pair (.nat a) (.nat b)) (t := 0)
      (ρ := [.pair (.nat a) (.nat b)]) (f := .prim (.snd Q0 Q0)) (a := .var 0) (p := .snd Q0 Q0) (args := [])
      (va := .pair (.nat a) (.nat b)) .prim (.var rfl)
    have hval := Ev.prim2 (p := .div Dim.zero Dim.zero) rfl
      (Ev.prim2 (p := .add Dim.zero) rfl (Ev.prim2 (p := .mul Dim.zero Dim.zero) rfl hfst (Ev.lit Dim.zero 3)) hsnd)
      (Ev.lit Dim.zero 4)
    have h := Ev.appClo (Δ := DeclEnv.empty) (I := fun _ _ => Value.pair (.nat a) (.nat b)) (t := 0) (ρ := [])
      (f := filterStep) (a := .declRef ⟨0⟩) (ρ' := []) (body := _) (va := .pair (.nat a) (.nat b)) .lam (.refInput rfl)
      (Ev.prim2 (p := .pair Q0 Q0) rfl hval hval)
    unfold Transduces filterF
    simpa [filterStep, pairE, fstE, sndE, app2, lit, applyPrim, Prim.arity, Prim.compute] using h
  preserves := by rintro s x ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- The physical reading: a step from 0 to 400 at tick 1. -/
def xA : Nat → Value := fun t => .nat (if t = 0 then 0 else 400)

theorem exA_filter_run :
    (filter.out xA 0).toNat? = some 0 ∧ (filter.out xA 1).toNat? = some 100 ∧
    (filter.out xA 2).toNat? = some 175 ∧ (filter.out xA 3).toNat? = some 231 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

-- the abstract design: a temperature Source and a consumer
def temp : DeclId := ⟨0⟩
def hot : DeclId := ⟨1⟩
def rA : DeclId := ⟨10⟩     -- the provider's reading (filtered)
def rA' : DeclId := ⟨11⟩    -- the physical reading
def mA : DeclId := ⟨12⟩     -- the filter upstream
def ΔA : DeclEnv := .ofList [⟨temp, ⟨Q0, []⟩, none⟩, ⟨hot, ⟨.bool, []⟩, some (ltE Dim.zero (lit 200) (.declRef temp))⟩]

def chId : Channel Q0 where
  rep := Q0
  tr := .lam Q0 (.var 0)
  transfer := id
  rep_semFree := trivial
  rep_data := trivial
  tr_pure := trivial
  computes := by rintro v ⟨n, rfl⟩; exact .appClo .lam (.refInput rfl) (.var rfl)

def ΔA0 : DeclEnv := withMachine ΔA filter rA' mA
def ΔBelow : DeclEnv := provision ΔA0 (Provision.one rA temp (some c0) chId)
def ΔUp : DeclEnv := upstreamΔ ΔA filter chId rA' mA temp
def baseA : Input := fun d t => if d = rA' then xA t else .nat 0
def IA : Input := belowInput filter rA rA' baseA

theorem wfA : WF Θ0 ΔA0 (Provision.one rA temp (some c0) chId) :=
  WF.one (h := ⟨temp, ⟨Q0, []⟩, none⟩) rfl trivial trivial rfl rfl rfl (infer_sound (by decide))

/-- **The filter below or above the reading**: the Source and the consumer
    agree tick by tick; `provider_state_movable` says every evaluation of
    the provisioned design holds in the upstream one. -/
theorem exA_filter :
    runN ΔBelow IA temp 2 = some 175 ∧ runN ΔUp IA temp 2 = some 175 ∧
    runB ΔBelow IA hot 2 = some false ∧ runB ΔUp IA hot 2 = some false ∧
    runB ΔBelow IA hot 3 = some true ∧ runB ΔUp IA hot 3 = some true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem exA_filter_theorem {c : ClockId} {t : Nat} {e : Expr} {v : Value} :
    MEv Sched.always ΔBelow IA c t [] e v → MEv Sched.always ΔUp IA c t [] e v :=
  provider_state_movable filter chId wfA (by decide) (by decide) (by decide) (by decide) trivial
    (fun d t => by unfold baseA; split <;> (intro h; cases h))
    (fun t => by simp [baseA, xA]; split <;> exact ⟨_, rfl⟩)
    (fun t => (filter.run_typed (fun t => by simp [baseA, xA]; split <;> exact ⟨_, rfl⟩) t).2)

/-- Provider state is a function of the physical stream alone: two streams
    equal up to `t` give the same run — a provider cannot read the design. -/
theorem Machine.run_congr {σ raw raw' : Ty} (M : Machine σ raw raw') {x x' : Nat → Value} :
    ∀ t, (∀ u ≤ t, x u = x' u) → M.run x t = M.run x' t
  | 0, h => by simp [Machine.run, h 0 (Nat.le_refl _)]
  | t + 1, h => by
    simp only [Machine.run]
    rw [Machine.run_congr M t (fun u hu => h u (Nat.le_succ_of_le hu)), h (t + 1) (Nat.le_refl _)]

/-! ### Debouncing, decoding, accumulation, hysteresis — upstream, executed -/

def rawL : DeclId := ⟨20⟩     -- bool: the bouncing contact
def stable : DeclId := ⟨21⟩   -- bool: the debounced level
def cnt : DeclId := ⟨22⟩      -- Q0: consecutive samples differing from `stable`

/-- Debounce with threshold `n`: the level flips after `n` consecutive
    differing samples. -/
def debounceDecls (n : Nat) : List DesignDecl := [
  ⟨rawL, ⟨.bool, []⟩, none⟩,
  ⟨cnt, ⟨Q0, []⟩, some (iteE Q0 (eqE .bool trivial (.declRef rawL) (.delay (.boolLit false) (.declRef stable)))
    (lit 0) (app2 (.prim (.add Dim.zero)) (.delay (lit 0) (.declRef cnt)) (lit 1)))⟩,
  ⟨stable, ⟨.bool, []⟩, some (iteE .bool (ltE Dim.zero (.declRef cnt) (lit n))
    (.delay (.boolLit false) (.declRef stable)) (.declRef rawL))⟩]

def Ibounce : Input := fun d t => if d = rawL then .bool (t = 1 ∨ t ≥ 3) else .nat 0

/-- The contact bounces once at tick 1 and settles high from tick 3. With
    threshold 2 the level rises at tick 4; with threshold 1 the bounce
    itself is a press at tick 1 — the threshold is in the semantic trace,
    so whether it is the product's decision or the device's is a design
    question, not a placement one. -/
theorem exA_debounce_param :
    runB (.ofList (debounceDecls 2)) Ibounce stable 1 = some false ∧
    runB (.ofList (debounceDecls 2)) Ibounce stable 3 = some false ∧
    runB (.ofList (debounceDecls 2)) Ibounce stable 4 = some true ∧
    runB (.ofList (debounceDecls 1)) Ibounce stable 1 = some true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

def phase : DeclId := ⟨23⟩    -- prod bool bool: the quadrature phases
def delta : DeclId := ⟨24⟩    -- Q0: 1 on a forward edge (A rises while B low), else 0
def reset : DeclId := ⟨25⟩    -- bool: homing
def pos : DeclId := ⟨26⟩      -- Q0: the accumulated position

def quadDecls : List DesignDecl := [
  ⟨phase, ⟨.prod .bool .bool, []⟩, none⟩,
  ⟨reset, ⟨.bool, []⟩, none⟩,
  ⟨delta, ⟨Q0, []⟩, some (iteE Q0
    (andE (andE (fstE .bool .bool (.declRef phase)) (notE (fstE .bool .bool (.delay (pairE .bool .bool (.boolLit false) (.boolLit false)) (.declRef phase)))))
      (notE (sndE .bool .bool (.declRef phase))))
    (lit 1) (lit 0))⟩,
  ⟨pos, ⟨Q0, []⟩, some (iteE Q0 (.declRef reset) (lit 0)
    (app2 (.prim (.add Dim.zero)) (.delay (lit 0) (.declRef pos)) (.declRef delta)))⟩]

/-- Phase A rises at ticks 1 and 3 (B low), homing at tick 4. -/
def Iquad : Input := fun d t =>
  if d = phase then .pair (.bool (t = 1 ∨ t = 3)) (.bool false) else if d = reset then .bool (t = 4) else .nat 0

/-- **Decoding is representation; accumulation and homing are behaviour**:
    the edge is a function of two consecutive phase readings (a provider
    may compute it), the position reads `reset` — a design value no provider
    sees — and is reset by it. -/
theorem exA_quadrature :
    runN (.ofList quadDecls) Iquad delta 1 = some 1 ∧ runN (.ofList quadDecls) Iquad delta 2 = some 0 ∧
    runN (.ofList quadDecls) Iquad pos 3 = some 2 ∧ runN (.ofList quadDecls) Iquad pos 4 = some 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

def level : DeclId := ⟨27⟩   -- Q0: a noisy level
def high : DeclId := ⟨28⟩    -- bool: Schmitt output with thresholds lo/hi

def schmittDecls (lo hi : Nat) : List DesignDecl := [
  ⟨level, ⟨Q0, []⟩, none⟩,
  ⟨high, ⟨.bool, []⟩, some (iteE .bool (.delay (.boolLit false) (.declRef high))
    (notE (ltE Dim.zero (.declRef level) (lit lo))) (ltE Dim.zero (lit hi) (.declRef level)))⟩]

def Inoisy : Input := fun d t => if d = level then .nat ([30, 65, 55, 35, 45] |>.getD t 45) else .nat 0

/-- The thresholds are in the semantic trace: `(40, 60)` and `(50, 60)`
    disagree at tick 3 on the same physical level. -/
theorem exA_hysteresis_param :
    runB (.ofList (schmittDecls 40 60)) Inoisy high 1 = some true ∧
    runB (.ofList (schmittDecls 40 60)) Inoisy high 3 = some false ∧
    runB (.ofList (schmittDecls 40 60)) Inoisy high 2 = some true ∧
    runB (.ofList (schmittDecls 50 60)) Inoisy high 3 = some false ∧
    runB (.ofList (schmittDecls 30 60)) Inoisy high 3 = some true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **A latch that reads the design cannot be a provider's**: the fault
    latch's body mentions `reset`, a design declaration; a channel term is
    pure and mentions no declaration (`Channel.tr_pure`,
    `Expr.Pure.refs_nil`). -/
theorem exA_latch_reads_design :
    reset ∈ (iteE Q0 (.declRef reset) (lit 0) (app2 (.prim (.add Dim.zero)) (.delay (lit 0) (.declRef pos)) (.declRef delta))).refs ∧
    ∀ (raw : Ty) (ch : Channel raw), reset ∉ ch.tr.refs :=
  ⟨by simp [iteE, app3, app2, lit, Expr.refs], fun _ ch => by rw [Expr.Pure.refs_nil ch.tr_pure]; simp⟩

/-! ## B — the Source-side device clock -/

def pc : ClockId := ⟨1⟩
/-- The Source's domain every tick; the provider's on even ticks. -/
def Sp : Sched := fun c t => if c = pc then t % 2 = 0 else true
def rB : DeclId := ⟨30⟩
def tempB : DeclId := ⟨31⟩
def ΔB : DeclEnv := .ofList [⟨tempB, ⟨Q0, []⟩, none⟩]
def init250 : InitRep := ⟨lit 250, .nat 250, trivial, Ev.lit _ _⟩
def ΔBs : DeclEnv := provisionSync ΔB rB tempB pc init250 chId
/-- The device reads `300 + t` at its activations. -/
def IB : Input := fun d t => if d = rB then .nat (300 + t) else .nat 0

/-- **Sampled strictly before, initial value explicit**: at tick 0 the
    Source carries the supplied initial reading 250 (no activation of the
    provider's domain before 0); at tick 1 the reading of tick 0; at tick 3
    the reading of tick 2. -/
def runSp (Δ : DeclEnv) (I : Input) (d : DeclId) (t : Nat) : Option Value := mevalF Sp Δ I 64 c0 t [] (.declRef d)

theorem exB_sampled :
    (runSp ΔBs IB tempB 0).bind nat? = some 250 ∧ (runSp ΔBs IB tempB 1).bind nat? = some 300 ∧
    (runSp ΔBs IB tempB 2).bind nat? = some 300 ∧ (runSp ΔBs IB tempB 3).bind nat? = some 302 ∧
    prevAct Sp pc 2 = some 0 ∧ prevAct Sp pc 3 = some 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem exB_structure :
    Causal ΔBs ∧ WellClocked (provisionSyncΚ (fun _ => some c0) rB pc) ΔBs := by
  refine ⟨provisionSync_causal (by decide) trivial ?_, provisionSync_wellClocked rfl (by decide) trivial ?_ ?_⟩
  · exact Causal.ofList (fun _ => 0) 1 (fun _ => Nat.zero_lt_one) (by decide)
  · exact NoMention.of_globalWF (GlobalWF.ofList (ev := fun _ _ _ => True) (Θ := Θ0) (by decide)) rfl
  · exact WellClocked.ofList (by decide)

/-- The optional form: raw `opt Q0`, initial `none`; the Source is
    *unavailable* at tick 0 and the design says so. -/
def chOpt : Channel (.opt Q0) where
  rep := .opt Q0
  tr := .lam (.opt Q0) (.var 0)
  transfer := id
  rep_semFree := trivial
  rep_data := trivial
  tr_pure := trivial
  computes := by intro v _; exact .appClo .lam (.refInput rfl) (.var rfl)
def tempO : DeclId := ⟨32⟩
def avail : DeclId := ⟨33⟩
def ΔO : DeclEnv := provisionSync (.ofList [⟨tempO, ⟨.opt Q0, []⟩, none⟩,
  ⟨avail, ⟨.bool, []⟩, some (.app (.prim (.isSome Q0)) (.declRef tempO))⟩]) rB tempO pc
  ⟨noneE Q0, .none, trivial, .prim⟩ chOpt
def IO : Input := fun d t => if d = rB then .some (.nat (300 + t)) else .nat 0

theorem exB_unavailable :
    (runSp ΔO IO avail 0).bind bool? = some false ∧ (runSp ΔO IO avail 1).bind bool? = some true ∧
    (runSp ΔO IO avail 3).bind bool? = some true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Encoder edges in the fast provider domain (every tick), windowed into
    a Source domain on every third tick and summed upstream. -/
def cw : ClockId := ⟨2⟩
def Sw : Sched := fun c t => if c = cw then t % 3 = 0 else true
def rE : DeclId := ⟨40⟩
def wids : Buffer.Ids := ⟨rE, ⟨41⟩, ⟨42⟩, ⟨43⟩, ⟨44⟩, ⟨45⟩⟩
def edges : DeclId := ⟨46⟩    -- list Q0: the edges since the last activation
def posW : DeclId := ⟨47⟩     -- Q0: accumulated
def chList : Channel (.list Q0) where
  rep := .list Q0
  tr := .lam (.list Q0) (.var 0)
  transfer := id
  rep_semFree := trivial
  rep_data := trivial
  tr_pure := trivial
  computes := by intro v _; exact .appClo .lam (.refInput rfl) (.var rfl)
def ΔW0 : DeclEnv := .ofList [⟨edges, ⟨.list Q0, []⟩, none⟩,
  ⟨posW, ⟨Q0, []⟩, some (app2 (.prim (.add Dim.zero)) (.delay (lit 0) (.declRef posW)) (.app (sumF Dim.zero) (.declRef edges)))⟩]
def ΔW : DeclEnv := provisionWindow ΔW0 rE edges pc wids chList
/-- One edge at ticks 1, 2, 4, 5 (none at 0, 3). -/
def IW : Input := fun d t => if d = rE then .nat (if t % 3 = 0 then 0 else 1) else .nat 0
def natList? : Value → Option (List Nat)
  | .list vs => go vs
  | _ => none
where
  go : List Value → Option (List Nat)
    | [] => some []
    | .nat n :: vs => (go vs).map (n :: ·)
    | _ => none

/-- **No edge lost across the crossing**: at the Source's tick 3 the window
    is the edges of ticks 0–2, `[0, 1, 1]`, and the position 2; at tick 6,
    `[0, 1, 1]` again and 4. -/
theorem exB_window_edges :
    (mevalF Sw ΔW IW 100 cw 3 [] (.declRef edges)).bind natList? = some [0, 1, 1] ∧
    (mevalF Sw ΔW IW 100 cw 3 [] (.declRef posW)).bind nat? = some 2 ∧
    (mevalF Sw ΔW IW 100 cw 6 [] (.declRef posW)).bind nat? = some 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## C — commitment discharge at three levels -/

open BDL.Experiments.ProvisionEx (saturating satTransfer Θ tempSensor rawT RoomTemp)

/-- The property: a temperature at most 450 (as a representation, or wrapped). -/
def AtMost450 : PropertyId → Value → Prop := fun _ v =>
  match v with | .sem _ (.nat n) => n ≤ 450 | .nat n => n ≤ 450 | _ => False

/-- The canonical evidence sound under an assumption: exactly the values
    the term takes under readings satisfying it. -/
def rangeEvidence (R : PropertyId → Value → Prop) (r : DeclId) (A : Value → Prop) : Evidence :=
  fun Δ e p => ∀ (S : Sched) (I : Input) c t v, (∀ t, A (I r t)) → MEv S Δ I c t [] e v → R p v

theorem rangeEvidence_sound (R : PropertyId → Value → Prop) (r : DeclId) (A : Value → Prop) :
    RangeSoundUnder (rangeEvidence R r A) R r A := fun _ _ _ h => h

def PT : Provision Q0 := BDL.Experiments.ProvisionEx.PS
def ΔT : DeclEnv := BDL.Experiments.ProvisionEx.Δ

theorem wfT : WF Θ ΔT PT := BDL.Experiments.ProvisionEx.wfS

/-- **Static**: the saturating transducer never exceeds 450 — from its
    definition alone, no assumption on the device. -/
theorem exC_static (p : PropertyId) :
    rangeEvidence AtMost450 rawT (TyVal Q0) (provision ΔT PT) (realizeAt (.sem RoomTemp) saturating.tr rawT) p :=
  discharge_static wfT (rangeEvidence_sound _ _ _) saturating (.sem RoomTemp) (by
    rintro v ⟨n, rfl⟩
    by_cases hn : n < 100 <;> simp [saturating, satTransfer, wrapAt, AtMost450, hn] <;> omega)

/-- **Trusted**: the identity channel keeps whatever the device sends; the
    property holds only under the assumed range `≤ 450` — the assumption is
    the hypothesis of the evidence, never discharged here. -/
def PId : Provision Q0 := .one rawT tempSensor (some ⟨0⟩) BDL.Experiments.ProvisionEx.wrongRep
theorem exC_trusted (p : PropertyId) (wf : WF Θ ΔT PId) :
    rangeEvidence AtMost450 rawT (fun v => TyVal Q0 v ∧ (match v with | .nat n => n ≤ 450 | _ => False))
      (provision ΔT PId) (realizeAt (.sem RoomTemp) BDL.Experiments.ProvisionEx.wrongRep.tr rawT) p :=
  discharge_trusted wf (rangeEvidence_sound _ _ _) BDL.Experiments.ProvisionEx.wrongRep (.sem RoomTemp) (by
    rintro v ⟨n, rfl⟩ h
    simpa [BDL.Experiments.ProvisionEx.wrongRep, wrapAt, AtMost450] using h)

/-- **Checked**: a validating provider admits only readings `≤ 450`
    (`ok`); the identity channel then discharges the property, the
    assumption being established by construction (`checked_items_ok`). -/
def ok450 : Value → Bool := fun v => match v with | .nat n => decide (n ≤ 450) | _ => false
theorem exC_checked (p : PropertyId) (wf : WF Θ ΔT PId) :
    rangeEvidence AtMost450 rawT (fun v => ok450 v = true) (provision ΔT PId)
      (realizeAt (.sem RoomTemp) BDL.Experiments.ProvisionEx.wrongRep.tr rawT) p :=
  discharge_checked (ok := ok450) wf (fun v h => by
      unfold ok450 at h; split at h
      · exact ⟨_, rfl⟩
      · exact nomatch h)
    (rangeEvidence_sound _ _ _) BDL.Experiments.ProvisionEx.wrongRep (.sem RoomTemp) (by
      intro v h
      unfold ok450 at h; split at h
      · simpa [BDL.Experiments.ProvisionEx.wrongRep, wrapAt, AtMost450] using h
      · exact nomatch h)

/-- The checking provider's items are `ok` — the construction behind the
    checked level, executed: a reading of 1000 and a malformed one refused. -/
def dv (token : Nat) (v : Value) : Delivery := ⟨0, token, v⟩
theorem exC_provider_checks :
    ((checkedProvide ⟨4⟩ ok450 [] [dv 1 (.nat 300), dv 2 (.nat 1000), dv 3 (.bool true), dv 4 (.nat 450)]).1.items.map Value.toNat?)
      = [some 300, some 450] ∧
    (checkedProvide ⟨4⟩ ok450 [] [dv 1 (.nat 300), dv 2 (.nat 1000), dv 3 (.bool true), dv 4 (.nat 450)]).2.1 = true := by
  refine ⟨by decide, by decide⟩

/-! ## D — `computes` -/

/-- A channel from its term alone: the transfer function is the
    evaluation, `computes` derived; totality at a finite raw type is checked
    by evaluating each value. -/
def gpioOfTerm : Channel .bool :=
  Channel.ofTerm .bool .bool (.lam .bool (.var 0)) 8 trivial trivial trivial
    (by rintro v ⟨b, rfl⟩; cases b <;> exact ⟨_, rfl⟩)

theorem exD_ofTerm : (gpioOfTerm.transfer (.bool true)).toBool? = some true ∧
    (gpioOfTerm.transfer (.bool false)).toBool? = some false := by
  refine ⟨?_, ?_⟩ <;> decide

/-- A supplied transfer function at `bool`, decided: the identity is right,
    the negation is wrong. -/
theorem exD_bool :
    computesBool (.lam .bool (.var 0)) 8 id = true ∧
    computesBool (.lam .bool (.var 0)) 8 (fun v => match v with | .bool b => .bool (!b) | v => v) = false := by
  refine ⟨by decide, by decide⟩

theorem exD_bool_computes : ∀ v, TyVal .bool v → Transduces (.lam .bool (.var 0)) v (id v) :=
  computes_of_bool exD_bool.1

/-! ## E — out-of-type readings into an optional Source -/

def rS : DeclId := ⟨50⟩
def tempS : DeclId := ⟨51⟩
def availS : DeclId := ⟨52⟩
/-- A batch of naturals sampled into `opt Q0`: `none` when the provider
    delivered nothing this tick. -/
def ΔS : DeclEnv := provision (.ofList [⟨tempS, ⟨.opt Q0, []⟩, none⟩,
  ⟨availS, ⟨.bool, []⟩, some (.app (.prim (.isSome Q0)) (.declRef tempS))⟩])
  (Provision.one rS tempS (some c0) (BDL.Experiments.Provider.chLatest Q0 trivial trivial))
/-- Tick 0: a good reading; tick 1: only a malformed and an out-of-range
    reading; tick 2: nothing. -/
def dsS : Nat → List Delivery := fun t =>
  if t = 0 then [dv 1 (.nat 300)] else if t = 1 then [dv 2 (.bool true), dv 3 (.nat 1000)] else []
/-- The checking provider's reading, tick by tick (state threaded). -/
def checkedRun : Nat → Batch × Bool × Seen
  | 0 => checkedProvide ⟨4⟩ ok450 [] (dsS 0)
  | t + 1 => checkedProvide ⟨4⟩ ok450 (checkedRun t).2.2 (dsS (t + 1))
def IS : Input := fun d t => if d = rS then (checkedRun t).1.value else .nat 0

/-- **Malformed readings never become values**: at tick 1 both deliveries
    are refused, the Source is `none`, `available` is false, and the design
    knows; at tick 0 it reads 300. -/
theorem exE_checked :
    runB ΔS IS availS 0 = some true ∧ runB ΔS IS availS 1 = some false ∧ runB ΔS IS availS 2 = some false ∧
    (checkedRun 1).2.1 = true ∧ (checkedRun 0).2.1 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## F — the motion state under two providers -/

open BDL.Experiments.Provider (chLatest sm)

def rF1 : DeclId := ⟨60⟩
def rF2 : DeclId := ⟨61⟩
/-- Provider 1: batches, sampled by `chLatest`. -/
def PM1 : Provision (batchTy Sample) := .one rF1 fb (some c0) (chLatest Sample (by decide) (by decide))
/-- Provider 2: one optional reading per tick through the identity. -/
def chOptS : Channel (.opt Sample) where
  rep := .opt Sample
  tr := .lam (.opt Sample) (.var 0)
  transfer := id
  rep_semFree := by decide
  rep_data := by decide
  tr_pure := trivial
  computes := by intro v _; exact .appClo .lam (.refInput rfl) (.var rfl)
def PM2 : Provision (.opt Sample) := .one rF2 fb (some c0) chOptS

def ΔM1 : DeclEnv := provision ΔM PM1
def ΔM2 : DeclEnv := provision ΔM PM2
/-- Motor feedback: two samples in tick 0 (the last at 10, at rest), one at
    tick 1, silence after. -/
def dsM : Nat → List Delivery := fun t =>
  if t = 0 then [sm 0 1 3 2, sm 0 2 10 0] else if t = 1 then [sm 0 3 10 0] else []
def baseM : Input := inM (fun _ => none) (fun _ => 10) (fun _ => false) (fun _ => false)
def IM1 : Input := rawInput ⟨2⟩ dsM rF1 baseM
def IM2 : Input := fun d t => if d = rF2 then
    (if t = 0 then .some (sample 10 0 false) else if t = 1 then .some (sample 10 0 false) else .none)
  else baseM d t

/-- **Two providers, one trace, one controller**: `fb` and `doneM` agree
    tick by tick under the batch provider and the scalar provider. -/
theorem exF_two_providers :
    (∀ t ∈ [0, 1, 2, 3], runB ΔM1 IM1 doneM t = runB ΔM2 IM2 doneM t ∧ runN ΔM1 IM1 settled t = runN ΔM2 IM2 settled t) ∧
    runB ΔM1 IM1 doneM 1 = some true ∧ runN ΔM1 IM1 settled 3 = some 4 := by
  refine ⟨by decide, ?_, ?_⟩ <;> decide

end BDL.Experiments.SourceBoundaryEx
