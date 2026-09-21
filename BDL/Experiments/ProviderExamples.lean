import BDL.Surface.Provider
import BDL.Experiments.CommunicationExamples
import BDL.Behavior.System

/-!
# Phase 17 — the provider's occurrence contract, executed

The auto_typer input side over Phase 16's queue and motion designs:

* A — one occurrence; two identical payloads with distinct identities are
  two; a retransmission (the same identity) is none.
* B — two commands in one base tick, in arrival order: `[A, B]` and
  `[B, A]` are two batches; a retried `A` between them does not appear.
* C — two raw sources before one activation: source order is one
  explicit merge; a per-source reading is insensitive to the merge.
* D — the bound: `cap = 2` cuts the third fresh delivery and raises the
  flag; `cap = 3` delivers all.
* E — **host command ingress into the queue design**: the batch provision
  feeds `submit` and `submitOver`; the queue trace under a delivery
  stream with a retransmission equals the trace without it, tick by tick
  (`run_retry`, executed) and the `two_providers_same_behavior` instance
  is stated (`exE_theorem`); the overflow flag reaches the design.
* F — **motor feedback from two raw sources**: two batch providers,
  sampled by `chLatest` into `fb2 : opt Sample` and `fb3`, so the motion
  state's freshness counts silence as before; two samples in one tick
  give the last; a retried sample is not a new one.

What is the provider's: identities, deduplication, the bound, the merge
policy.  What is state: the batches, `queue`, `age`.  What is behaviour:
everything Phase 16 executed.  Nothing about TCP or CAN is written.
-/

namespace BDL.Experiments.Provider
open BDL BDL.Reactive BDL.Clock BDL.Output BDL.Stdlib BDL.Provision BDL.Assignment BDL.Provider
open BDL.Experiments.Communication

def dl (src token : Nat) (i d : Nat) : Delivery := ⟨src, token, .pair (.nat i) (.nat d)⟩
def C2 : Contract := ⟨2⟩
def C3 : Contract := ⟨3⟩

def items? (b : Batch) : Option (List (Nat × Nat)) := jobs? (.list b.items)

/-! ## A — one occurrence, two identical, a retry -/

/-- Job 1 at tick 0; jobs 2 and 3 with the same payload at tick 1; the
    transport retransmits token 2 at tick 2 (and token 1). -/
def dsA : Nat → List Delivery := fun t =>
  if t = 0 then [dl 0 1 1 10] else if t = 1 then [dl 0 2 7 10, dl 0 3 7 10]
  else if t = 2 then [dl 0 2 7 10, dl 0 1 1 10] else []

theorem exA_occurrences :
    items? (batch C2 dsA 0) = some [(1, 10)] ∧ (batch C2 dsA 0).overflow = false ∧
    items? (batch C2 dsA 1) = some [(7, 10), (7, 10)] ∧
    items? (batch C2 dsA 2) = some [] ∧ (batch C2 dsA 2).overflow = false ∧
    items? (batch C2 dsA 3) = some [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## B — order within a tick; a retry between two commands -/

def dsB_AB : Nat → List Delivery := fun t => if t = 1 then [dl 0 1 1 10, dl 0 2 2 30] else []
def dsB_BA : Nat → List Delivery := fun t => if t = 1 then [dl 0 2 2 30, dl 0 1 1 10] else []
/-- `A`, a retransmitted `A`, then `B`. -/
def dsB_ArB : Nat → List Delivery := fun t => if t = 1 then [dl 0 1 1 10, dl 0 1 1 10, dl 0 2 2 30] else []

theorem exB_order :
    items? (batch C2 dsB_AB 1) = some [(1, 10), (2, 30)] ∧
    items? (batch C2 dsB_BA 1) = some [(2, 30), (1, 10)] ∧
    items? (batch C2 dsB_ArB 1) = some [(1, 10), (2, 30)] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The retry stream is `dsB_AB` with a retransmission inserted:
    `run_retry` gives every batch equal, not only tick 1. -/
theorem exB_retry_is_Retry : Retry dsB_AB dsB_ArB 1 (dl 0 1 1 10) [dl 0 1 1 10] [dl 0 2 2 30] :=
  ⟨rfl, rfl, fun u hu => by simp [dsB_AB, dsB_ArB, hu], Or.inr ⟨dl 0 1 1 10, List.mem_singleton.mpr rfl, rfl⟩⟩

theorem exB_all_ticks : ∀ u, batch C2 dsB_ArB u = batch C2 dsB_AB u := batch_retry C2 exB_retry_is_Retry

/-! ## C — two raw sources before one activation -/

def fromHost : List Delivery := [dl 0 1 1 10]
def fromPanel : List Delivery := [dl 1 9 2 30]

theorem two_interleaving (m : List Delivery) (h0 : m.filter (fun d => d.src = 0) = fromHost)
    (h1 : m.filter (fun d => d.src = 1) = fromPanel) : Interleaving [fromHost, fromPanel] m := by
  intro i hi
  match i, hi with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | n + 2, h => exact absurd h (by simp)

theorem exC_merge :
    mergeBySource [fromHost, fromPanel] = [dl 0 1 1 10, dl 1 9 2 30] ∧
    Interleaving [fromHost, fromPanel] (mergeBySource [fromHost, fromPanel]) ∧
    -- the other interleaving, panel first, is a different batch …
    Interleaving [fromHost, fromPanel] [dl 1 9 2 30, dl 0 1 1 10] ∧
    -- … with the same per-source subsequences
    (mergeBySource [fromHost, fromPanel]).filter (fun d => d.src = 0) =
      [dl 1 9 2 30, dl 0 1 1 10].filter (fun d => d.src = 0) ∧
    (mergeBySource [fromHost, fromPanel]).filter (fun d => d.src = 1) =
      [dl 1 9 2 30, dl 0 1 1 10].filter (fun d => d.src = 1) :=
  ⟨rfl, two_interleaving _ rfl rfl, two_interleaving _ rfl rfl,
    perSource_of_interleaving (two_interleaving _ rfl rfl) (two_interleaving _ rfl rfl) 0 (by decide),
    perSource_of_interleaving (two_interleaving _ rfl rfl) (two_interleaving _ rfl rfl) 1 (by decide)⟩

/-! ## D — the bound -/

def dsD : Nat → List Delivery := fun t => if t = 0 then [dl 0 1 1 10, dl 0 2 2 30, dl 0 3 3 5] else []

theorem exD_bound :
    items? (batch C2 dsD 0) = some [(1, 10), (2, 30)] ∧ (batch C2 dsD 0).overflow = true ∧
    items? (batch C3 dsD 0) = some [(1, 10), (2, 30), (3, 5)] ∧ (batch C3 dsD 0).overflow = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## E — host command ingress into the queue design -/

def submitOver : DeclId := ⟨11⟩
def rHost : DeclId := ⟨70⟩

/-- The queue design with the overflow flag as a second Source. -/
def ΔQP : DeclEnv := .ofList (queueDecls (.declRef submit) false ++ [⟨submitOver, ⟨.bool, []⟩, none⟩])
theorem ΔQP_typed : GlobalWF (fun _ _ _ => True) Θ ΔQP := GlobalWF.ofList (by decide)

def PHost : Provision (batchTy JobT) := batchProvision JobT (by decide) (by decide) rHost submit submitOver (some c0)

theorem wfHost : WF Θ ΔQP PHost := by
  refine ⟨rfl, by decide, by decide, fun s ch hc => ?_⟩
  by_cases hs : s = submit
  · subst hs
    have : ch = chItems JobT (by decide) (by decide) := by
      simp [PHost, batchProvision, Provision.ofList, List.find?] at hc; exact hc.symm
    subst this
    exact ⟨_, rfl, rfl, rfl, infer_sound (by decide)⟩
  by_cases ho : s = submitOver
  · subst ho
    have : ch = chOverflow JobT := by
      simp [PHost, batchProvision, Provision.ofList, List.find?, submit, submitOver] at hc; exact hc.symm
    subst this
    exact ⟨_, rfl, rfl, rfl, infer_sound (by decide)⟩
  have hs' : ¬ submit = s := fun e => hs e.symm
  have ho' : ¬ submitOver = s := fun e => ho e.symm
  simp [PHost, batchProvision, Provision.ofList, List.find?, hs', ho'] at hc

/-- The base input: no cancellation; the active job completes at tick 3. -/
def baseE : Input := inQ (fun _ => []) (fun _ => none) (fun t => t = 3)

/-- Host deliveries: `A` at tick 1, `B` at tick 2 — and, in the retry
    stream, `A` again at tick 2 (the host heard no answer). -/
def dsE : Nat → List Delivery := fun t => if t = 1 then [dl 0 1 1 10] else if t = 2 then [dl 0 2 2 30] else []
def dsE' : Nat → List Delivery := fun t => if t = 1 then [dl 0 1 1 10] else if t = 2 then [dl 0 1 1 10, dl 0 2 2 30] else []

def IE : Input := rawInput C2 dsE rHost baseE
def IE' : Input := rawInput C2 dsE' rHost baseE
def ΔE : DeclEnv := provision ΔQP PHost

/-- **Ingress, executed**: the provisioned design queues `A` then `B`,
    reaches 10 then 40; under the retry stream the queue is the same at
    every tick shown — the retransmission never became a job — and the
    overflow flag is false throughout. -/
theorem exE_ingress :
    runQ ΔE IE 2 = some [(1, 10), (2, 30)] ∧ runD ΔE IE 2 = some 10 ∧ runD ΔE IE 4 = some 40 ∧
    runQ ΔE IE' 2 = some [(1, 10), (2, 30)] ∧ runD ΔE IE' 4 = some 40 ∧
    runB ΔE IE submitOver 2 = some false ∧ runB ΔE IE' submitOver 2 = some false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem exE_retry : Retry dsE dsE' 2 (dl 0 1 1 10) [] [dl 0 2 2 30] :=
  ⟨rfl, rfl, fun u hu => by simp [dsE, dsE', hu], Or.inl ⟨1, by decide, dl 0 1 1 10, List.mem_singleton.mpr rfl, rfl⟩⟩

theorem baseE_noClo (d : DeclId) (t : Nat) : (baseE d t).NoClo := by
  unfold baseE inQ
  split
  · exact TyVal.noClo (τ := Jobs) (by decide) (jobsV_tyVal [])
  · split
    · split <;> (intro h; cases h <;> (rename_i h'; cases h'))
    · split <;> (intro h; cases h)

theorem dl_tyVal (src token i d : Nat) : TyVal JobT (dl src token i d).payload := ⟨_, _, rfl, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

theorem dsE_typed : Typed JobT dsE := by
  intro t d hd
  unfold dsE at hd
  split at hd
  · rw [List.mem_singleton] at hd; subst hd; exact dl_tyVal ..
  · split at hd
    · rw [List.mem_singleton] at hd; subst hd; exact dl_tyVal ..
    · exact absurd hd List.not_mem_nil
theorem dsE'_typed : Typed JobT dsE' := by
  intro t d hd
  unfold dsE' at hd
  split at hd
  · rw [List.mem_singleton] at hd; subst hd; exact dl_tyVal ..
  · split at hd
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact dl_tyVal ..
      · rw [List.mem_singleton] at hd; subst hd; exact dl_tyVal ..
    · exact absurd hd List.not_mem_nil

/-- **`two_providers_same_behavior`, through the provider**: the retry
    stream and the plain stream induce the same trace (`retry_invisible`),
    so every declaration of the queue design evaluates alike. -/
theorem exE_theorem (d : DeclId) (hd : ΔQP d ≠ none) (c : ClockId) (t : Nat) (v : Value) :
    MEv Sched.always ΔE IE' c t [] (.declRef d) v ↔ MEv Sched.always ΔE IE c t [] (.declRef d) v :=
  two_providers_same_behavior wfHost wfHost (NoMention.of_globalWF ΔQP_typed rfl) (NoMention.of_globalWF ΔQP_typed rfl)
    (rawInput_rawInput dsE'_typed (by decide) (by decide) C2 baseE_noClo)
    (rawInput_rawInput dsE_typed (by decide) (by decide) C2 baseE_noClo)
    (retry_invisible (by decide) (by decide) C2 exE_retry (by decide) (by decide))
    (by simp [Expr.refs]; intro h; exact hd (h ▸ wfHost.fresh))
    (by simp [Expr.refs]; intro h; exact hd (h ▸ wfHost.fresh))
    (fun _ h => by simp at h) (fun _ h => by simp at h)

/-- The flag reaches the design: three jobs in one tick under `cap = 2`
    queue two and raise `submitOver`. -/
def dsE3 : Nat → List Delivery := fun t => if t = 1 then [dl 0 1 1 10, dl 0 2 2 30, dl 0 3 3 5] else []
theorem exE_overflow :
    runQ ΔE (rawInput C2 dsE3 rHost baseE) 1 = some [(1, 10), (2, 30)] ∧
    runB ΔE (rawInput C2 dsE3 rHost baseE) submitOver 1 = some true := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## F — motor feedback from two raw sources -/

/-- The scalar sampling of a batch: the last item as an option — a
    `fb : opt Sample` Source from a batch provider. -/
def chLatest (τ : Ty) (hs : τ.SemFree) (hd : τ.Data) : Channel (batchTy τ) where
  rep := .opt τ
  tr := .lam (batchTy τ) (.app (.prim (.head τ)) (.app (.prim (.reverse τ)) (.app (.prim (.fst (.list τ) .bool)) (.var 0))))
  transfer := fun v => match v with
    | .pair (.list vs) _ => (match vs.reverse with | x :: _ => .some x | [] => .none)
    | v => v
  rep_semFree := hs
  rep_data := hd
  tr_pure := by simp [Expr.Pure]
  computes := by
    rintro v ⟨a, b, rfl, ⟨vs, rfl, _⟩, _⟩
    have h := Ev.appClo (Δ := DeclEnv.empty) (I := fun _ _ => Value.pair (.list vs) b) (t := 0) (ρ := [])
      (f := .lam (batchTy τ) (.app (.prim (.head τ)) (.app (.prim (.reverse τ)) (.app (.prim (.fst (.list τ) .bool)) (.var 0)))))
      (a := .declRef ⟨0⟩) (ρ' := []) (body := _) (va := .pair (.list vs) b) .lam (.refInput rfl)
      (Ev.appPrim .prim (Ev.appPrim .prim (Ev.appPrim .prim (.var rfl))))
    unfold Transduces
    cases hr : vs.reverse with
    | nil => simpa [applyPrim, Prim.arity, Prim.compute, hr] using h
    | cons x xs => simpa [applyPrim, Prim.arity, Prim.compute, hr] using h

def rFb2 : DeclId := ⟨71⟩
def rFb3 : DeclId := ⟨72⟩
def fb2 : DeclId := ⟨36⟩
def fb3 : DeclId := ⟨37⟩

/-- Two feedback Sources, one per motor. -/
def ΔF : DeclEnv := .ofList [⟨fb2, ⟨Fb, []⟩, none⟩, ⟨fb3, ⟨Fb, []⟩, none⟩]
def P2 : Provision (batchTy Sample) := .one rFb2 fb2 (some c0) (chLatest Sample (by decide) (by decide))
def P3 : Provision (batchTy Sample) := .one rFb3 fb3 (some c0) (chLatest Sample (by decide) (by decide))
def ΔF' : DeclEnv := provision (provision ΔF P2) P3

def sm (src token p v : Nat) : Delivery := ⟨src, token, sample p v false⟩
/-- Motor 2 reports twice in tick 0 and once in tick 1, then falls silent;
    motor 3 reports once, and its transport retransmits it. -/
def dsF2 : Nat → List Delivery := fun t => if t = 0 then [sm 0 1 3 2, sm 0 2 5 1] else if t = 1 then [sm 0 3 8 0] else []
def dsF3 : Nat → List Delivery := fun t => if t = 0 then [sm 1 1 4 1] else if t = 1 then [sm 1 1 4 1] else []
def IF : Input := rawInput C2 dsF3 rFb3 (rawInput C2 dsF2 rFb2 (fun _ _ => .nat 0))

def sample? : Value → Option (Option (Nat × Nat))
  | .none => some none
  | .some (.pair (.nat p) (.pair (.nat v) _)) => some (some (p, v))
  | _ => none

/-- **Two samples in one tick give the last; a retransmitted sample is not
    a new one; silence is `none`** — what `age` then counts. -/
theorem exF_feedback :
    (evalF ΔF' IF 64 0 [] (.declRef fb2)).bind sample? = some (some (5, 1)) ∧
    (evalF ΔF' IF 64 1 [] (.declRef fb2)).bind sample? = some (some (8, 0)) ∧
    (evalF ΔF' IF 64 2 [] (.declRef fb2)).bind sample? = some none ∧
    (evalF ΔF' IF 64 0 [] (.declRef fb3)).bind sample? = some (some (4, 1)) ∧
    (evalF ΔF' IF 64 1 [] (.declRef fb3)).bind sample? = some none := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## G — one controller, two axes: the motion state as a reusable component -/

/-- The Phase-16 motion state as a behaviour component: `fb`, `target`,
    `reset`, `ackNow` required; `doneM`, `fault`, `settled` provided; all
    in the clock parameter `c0`.  Nothing is changed in the declarations. -/
def motionDesign : BDL.Design where
  Δ := .ofList (motionDecls none)
  Θ := Θ
  Κ := fun _ => some c0
  Ω := fun _ => none
  β := fun _ => none

def motion : BDL.BehaviorComponent where
  iface :=
    { required := [⟨fb, ⟨Fb, []⟩, some c0⟩, ⟨target, ⟨Q0, []⟩, some c0⟩, ⟨reset, ⟨.bool, []⟩, some c0⟩,
        ⟨ackNow, ⟨.bool, []⟩, some c0⟩]
      provided := [⟨doneM, ⟨.bool, []⟩, some c0⟩, ⟨fault, ⟨.bool, []⟩, some c0⟩, ⟨settled, ⟨Q0, []⟩, some c0⟩]
      params := []
      clockParams := [c0] }
  design := motionDesign
  width := 40
  internalConcept := fun _ => false
  internalOut := fun _ => false

/-- An axis's inputs: four open ports (the system's Sources). -/
def fbP : DeclId := ⟨0⟩
def tgP : DeclId := ⟨1⟩
def rsP : DeclId := ⟨2⟩
def akP : DeclId := ⟨3⟩
def feedDesign : BDL.Design where
  Δ := .ofList [⟨fbP, ⟨Fb, []⟩, none⟩, ⟨tgP, ⟨Q0, []⟩, none⟩, ⟨rsP, ⟨.bool, []⟩, none⟩, ⟨akP, ⟨.bool, []⟩, none⟩]
  Θ := Θ
  Κ := fun _ => some c0
  Ω := fun _ => none
  β := fun _ => none
def feed : BDL.BehaviorComponent where
  iface :=
    { required := []
      provided := [⟨fbP, ⟨Fb, []⟩, some c0⟩, ⟨tgP, ⟨Q0, []⟩, some c0⟩, ⟨rsP, ⟨.bool, []⟩, some c0⟩,
        ⟨akP, ⟨.bool, []⟩, some c0⟩]
      params := []
      clockParams := [c0] }
  design := feedDesign
  width := 40
  internalConcept := fun _ => false
  internalOut := fun _ => false

/-- Two axes: instances 0 and 1 feed, instances 2 and 3 control. -/
def axes : BDL.BehaviorSystem where
  W := 40
  insts := [⟨feed, id⟩, ⟨feed, id⟩, ⟨motion, id⟩, ⟨motion, id⟩]
  bindings := [
    ⟨.port 0 fbP, 2, fb, none⟩, ⟨.port 0 tgP, 2, target, none⟩, ⟨.port 0 rsP, 2, reset, none⟩, ⟨.port 0 akP, 2, ackNow, none⟩,
    ⟨.port 1 fbP, 3, fb, none⟩, ⟨.port 1 tgP, 3, target, none⟩, ⟨.port 1 rsP, 3, reset, none⟩, ⟨.port 1 akP, 3, ackNow, none⟩]
  Θg := Θ
  Ωg := fun _ => none

/-- Axis 2 (fed by instance 0) reaches 10 at rest from tick 1; axis 3 (fed
    by instance 1) reports a fault at tick 1 and stays away from its
    target. -/
def IG : Input := fun d t =>
  if d = axes.declOf 0 fbP then .some (sample 10 0 false)
  else if d = axes.declOf 0 tgP then .nat 10
  else if d = axes.declOf 1 fbP then .some (sample 3 2 (t = 1))
  else if d = axes.declOf 1 tgP then .nat 10
  else if d = axes.declOf 0 rsP ∨ d = axes.declOf 1 rsP ∨ d = axes.declOf 0 akP ∨ d = axes.declOf 1 akP then .bool false
  else .nat 0

def runAxis (k : Nat) (d : DeclId) (t : Nat) : Option Value := evalF axes.flattenΔ IG 200 t [] (.declRef (axes.declOf k d))

/-- **One controller, two instances**: axis 2 completes at tick 1 (two
    settled samples) with no fault; axis 3 never completes and latches
    its fault from tick 1 — the same template, disjoint state. -/
theorem exG_two_axes :
    (runAxis 2 doneM 1).bind bool? = some true ∧ (runAxis 2 fault 3).bind bool? = some false ∧
    (runAxis 3 doneM 3).bind bool? = some false ∧ (runAxis 3 fault 1).bind bool? = some true ∧
    (runAxis 3 fault 3).bind bool? = some true ∧
    axes.declOf 2 settled ≠ axes.declOf 3 settled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by decide⟩ <;> decide

end BDL.Experiments.Provider
