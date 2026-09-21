import BDL.Surface.Assignment
import BDL.Surface.Buffer
import BDL.Surface.Stdlib
import BDL.Experiments.HardwareAlternatives

/-!
# Phase 16 — communication as state: the auto_typer stress case, executed

The hypothesis under test: the behaviour language needs *semantic state*,
not communication artifacts — no `Event`, `Message`, `Packet`, `Stream`
or `Channel` type.  A message's product-observable content is what it
does to state; its carrier stays below the physical boundary.  This
module attacks the hypothesis with a reduced motion controller of the
auto_typer kind — a host submits jobs, jobs queue and cancel, a motor
reports position / velocity / fault, completion needs fresh in-tolerance
samples, a paired axis is one output on two motors — written with the
existing kernel only: `Bool`, quantities, pairs, options, lists, `delay`,
`sync`, the Phase-9a window, the Phase-13 provision, the Phase-14
realization.

Two designs, each a handful of ordinary declarations:

* **Q — the work queue** (`queueDecls`): `submit : list Job` (the jobs
  that arrived this tick, oldest first; `Job = (JobId, delta)`),
  `cancel : opt JobId`, `done : bool`; state `queue : list Job` (FIFO,
  bounded by `cap`), `desired : Position` (advanced by a job's delta when
  it starts); `overflow` (a refusal the product observes).
* **M — the motion state** (`motionDecls`): `fb : opt (pos × vel × fault)`
  (a feedback sample or none), `target`, `reset`, `ackNow`; state `age`
  (ticks since the last sample), `fresh`, `timedOut`, `lastPos`,
  `lastVel`, `settled` (consecutive fresh in-tolerance samples),
  `doneM := settled ≥ 2`, `fault` (latched until `reset`), `acked`.

Executed (all by `decide` on `evalF` / `mevalF`):

* A — **multiplicity**: `Move(+10); Move(+10)` and `Move(+10)` differ in
  the queue and, after the first completes, in `desired` (20 vs 10).
* B — **ordering**: `A; B` and `B; A` reach the same final target through
  different intermediate desired positions (10 then 40 vs 30 then 40).
* C — **same-tick multiplicity**: `[A, B]`, `[B, A]` and `[A]` arriving in
  one tick are three different queues; nothing is lost.
* D — **cancellation** by semantic `JobId`: a queued job is removed, the
  active job is removed and the next starts, an unknown id is ignored.
* E — **bounded queue**: with `cap = 2` a third job is refused and the
  refusal is state (`overflow`).
* F — **concept identity**: a retried submission with the same `JobId`
  is one job under the dedup design and two under the plain one — the
  design decides, because the id is in the state.
* G — **freshness and timeout**: no sample for three ticks is stale, for
  six is a timeout; completion stops when freshness does.
* H — **repeated samples**: one in-tolerance sample does not complete;
  two consecutive do.
* I — **fault latching**: one faulty sample latches until `reset`.
* J — **acknowledgement state**: an ack holds until the target changes.
* K — **cross-clock delivery**: host submissions in a fast domain reach
  the controller's slow domain through the Phase-9a window, flattened —
  two jobs between two controller ticks arrive as `[A, B]`.
* L — **transport identity**: the same submission stream framed by two
  providers — `(sequence number, batch)` and per-job `(frame id, job)` —
  induces one Source trace; `two_providers_same_behavior` applies and the
  queues coincide tick by tick.
* N — **the paired axis**: `DesiredPos` realized once with a pair command
  `(p, p)` for two motors; the raw command at each tick is one pair.
* P — **builtin vs packaged**: the same profile under two origins lowers to
  one design (`assign_indistinguishable`, instantiated).
* Q — **contract vs feasibility**: the pair-command profile satisfies the
  contract for `DesiredPos` and is not feasible on a board with one pin.

Not modelled, and not needed for any case above: a message type, a queue
primitive, a transaction primitive, an event stream.
-/

namespace BDL.Experiments.Communication
open BDL BDL.Reactive BDL.Clock BDL.Output BDL.Stdlib BDL.Provision BDL.OutputRealization BDL.Adapter
open BDL.Assignment BDL.Hardware

/-! ## Types and builders -/

def Q0 : Ty := .q Dim.zero
/-- A job: `(JobId, delta)` — the identity the product cancels by, and
    the relative move.  A pair, not a record (Phase 9b). -/
def JobT : Ty := .prod Q0 Q0
def Jobs : Ty := .list JobT
def OJob : Ty := .opt JobT
/-- A feedback sample: `(position, (velocity, fault))`. -/
def Sample : Ty := .prod Q0 (.prod Q0 .bool)
def Fb : Ty := .opt Sample

def lit (n : Nat) : Expr := .prim (.lit Dim.zero n)
def headE (τ : Ty) (l : Expr) : Expr := .app (.prim (.head τ)) l
def lenE (τ : Ty) (l : Expr) : Expr := .app (.prim (.length τ)) l
def addE (a b : Expr) : Expr := app2 (.prim (.add Dim.zero)) a b
def subE (a b : Expr) : Expr := app2 (.prim (.sub Dim.zero)) a b
def getDE (τ : Ty) (o d : Expr) : Expr := app2 (.prim (.getD τ)) o d
def isSomeE (τ : Ty) (o : Expr) : Expr := .app (.prim (.isSome τ)) o
def job (i d : Nat) : Expr := pairE Q0 Q0 (lit i) (lit d)

/-- `flatten : list (opt τ) → list τ`, in order — the window's occurrences
    without the empty ticks. -/
def flattenF (τ : Ty) : Expr :=
  .lam (.list (.opt τ))
    (.fold (.lam (.opt τ) (.lam (.list τ) (app2 (appendF τ) (toListE τ (.var 1)) (.var 0)))) (nilE τ) (.var 0))

/-! ## Concepts -/

def DesiredPos : ConceptId := ⟨200⟩
def Θ : ConceptEnv := fun s => if s = DesiredPos then some Q0 else none

/-! ## Q — the work queue -/

def submit : DeclId := ⟨0⟩      -- list Job: the submissions this tick, oldest first
def cancel : DeclId := ⟨1⟩      -- opt JobId
def done : DeclId := ⟨2⟩        -- bool: the active job completed (from M)
def admitted : DeclId := ⟨3⟩    -- list Job: the queue before the bound
def queue : DeclId := ⟨4⟩       -- list Job: pending work, head active
def overflow : DeclId := ⟨5⟩    -- bool: a submission was refused this tick
def activeId : DeclId := ⟨6⟩    -- opt JobId
def starts : DeclId := ⟨7⟩      -- opt Job: the job that starts this tick
def desired : DeclId := ⟨8⟩     -- Position
def desiredC : DeclId := ⟨9⟩    -- DesiredPos — the semantic desired state, drives the output
def prevIds : DeclId := ⟨10⟩    -- list JobId: the ids queued at the previous tick

def cap : Nat := 2

/-- `λj. not (some (fst j) = cancel)`. -/
def notCancelledF : Expr :=
  .lam JobT (notE (eqE (.opt Q0) trivial (someE Q0 (fstE Q0 Q0 (.var 0))) (.declRef cancel)))
def prevQueue : Expr := .delay (nilE JobT) (.declRef queue)
/-- The queue after this tick's completion: the head is popped when `done`. -/
def afterPop : Expr := iteE Jobs (.declRef done) (dropE JobT (lit 1) prevQueue) prevQueue
def admittedBody (arrivals : Expr) : Expr :=
  app2 (filterF JobT) notCancelledF (app2 (appendF JobT) afterPop arrivals)
def queueBody : Expr := takeE JobT (lit cap) (.declRef admitted)
def overflowBody : Expr := ltE Dim.zero (lit cap) (lenE JobT (.declRef admitted))
def activeIdBody : Expr := app2 (mapOptF JobT Q0) (.prim (.fst Q0 Q0)) (headE JobT (.declRef queue))
/-- A job starts when the head's identity changes. -/
def startsBody : Expr :=
  iteE OJob (eqE (.opt Q0) trivial (.declRef activeId) (.delay (noneE Q0) (.declRef activeId)))
    (noneE JobT) (headE JobT (.declRef queue))
def desiredBody : Expr :=
  addE (.delay (lit 0) (.declRef desired))
    (getDE Q0 (app2 (mapOptF JobT Q0) (.prim (.snd Q0 Q0)) (.declRef starts)) (lit 0))
def prevIdsBody : Expr := app2 (mapF JobT Q0) (.prim (.fst Q0 Q0)) prevQueue
/-- `λj. not (contains (fst j) prevIds)` — a job already queued is not
    queued again: identity that affects behaviour, in the state. -/
def dedupF : Expr :=
  .lam JobT (notE (app2 (containsF Q0 trivial) (fstE Q0 Q0 (.var 0)) (.declRef prevIds)))

/-- The queue design over an `arrivals` term (a `list Job`); with `dedup`
    the arrivals are filtered by the ids already queued. -/
def queueDecls (arrivals : Expr) (dedup : Bool) : List DesignDecl := [
  ⟨submit, ⟨Jobs, []⟩, none⟩,
  ⟨cancel, ⟨.opt Q0, []⟩, none⟩,
  ⟨done, ⟨.bool, []⟩, none⟩,
  ⟨prevIds, ⟨.list Q0, []⟩, some prevIdsBody⟩,
  ⟨admitted, ⟨Jobs, []⟩, some (admittedBody (if dedup then app2 (filterF JobT) dedupF arrivals else arrivals))⟩,
  ⟨queue, ⟨Jobs, []⟩, some queueBody⟩,
  ⟨overflow, ⟨.bool, []⟩, some overflowBody⟩,
  ⟨activeId, ⟨.opt Q0, []⟩, some activeIdBody⟩,
  ⟨starts, ⟨OJob, []⟩, some startsBody⟩,
  ⟨desired, ⟨Q0, []⟩, some desiredBody⟩,
  ⟨desiredC, ⟨.sem DesiredPos, []⟩, some (.mk DesiredPos (.declRef desired))⟩]

def ΔQ : DeclEnv := .ofList (queueDecls (.declRef submit) false)
def ΔQd : DeclEnv := .ofList (queueDecls (.declRef submit) true)

def c0 : ClockId := ⟨0⟩
def ΚQ : ClockEnv := fun _ => some c0

theorem ΔQ_typed : GlobalWF (fun _ _ _ => True) Θ ΔQ := GlobalWF.ofList (by decide)
theorem ΔQd_typed : GlobalWF (fun _ _ _ => True) Θ ΔQd := GlobalWF.ofList (by decide)
def rankQ : DeclId → Nat := fun d =>
  if d = admitted then 1 else if d = queue ∨ d = overflow then 2 else if d = activeId then 3
  else if d = starts then 4 else if d = desired then 5 else if d = desiredC then 6 else 0
theorem ΔQ_causal : Causal ΔQ :=
  Causal.ofList rankQ 7 (by intro d; unfold rankQ; (repeat' split) <;> omega) (by decide)
theorem ΔQ_clocked : WellClocked ΚQ ΔQ := WellClocked.ofList (by decide)

/-! ### Readers -/

def nat? : Value → Option Nat
  | .nat n => some n
  | _ => none
def pair? : Value → Option (Nat × Nat)
  | .pair (.nat a) (.nat b) => some (a, b)
  | _ => none
def jobs? : Value → Option (List (Nat × Nat))
  | .list vs => go vs
  | _ => none
where
  go : List Value → Option (List (Nat × Nat))
    | [] => some []
    | v :: vs => match pair? v, go vs with
      | some p, some ps => some (p :: ps)
      | _, _ => none
def bool? : Value → Option Bool
  | .bool b => some b
  | _ => none
def optNat? : Value → Option (Option Nat)
  | .none => some none
  | .some (.nat n) => some (some n)
  | _ => none

def runQ (Δ : DeclEnv) (I : Input) (t : Nat) : Option (List (Nat × Nat)) :=
  (evalF Δ I 200 t [] (.declRef queue)).bind jobs?
def runD (Δ : DeclEnv) (I : Input) (t : Nat) : Option Nat :=
  (evalF Δ I 200 t [] (.declRef desired)).bind nat?
def runB (Δ : DeclEnv) (I : Input) (d : DeclId) (t : Nat) : Option Bool :=
  (evalF Δ I 200 t [] (.declRef d)).bind bool?

/-- Inputs from three schedules: submissions per tick, a cancellation per
    tick, completion per tick. -/
def inQ (sub : Nat → List (Nat × Nat)) (can : Nat → Option Nat) (dn : Nat → Bool) : Input := fun d t =>
  if d = submit then .list ((sub t).map fun p => .pair (.nat p.1) (.nat p.2))
  else if d = cancel then (match can t with | some i => .some (.nat i) | none => .none)
  else if d = done then .bool (dn t)
  else .nat 0

/-! ### A — multiplicity -/

/-- `Move(+10)` at tick 1 and again (a second job) at tick 2; the first
    completes at tick 4. -/
def I_A2 : Input := inQ (fun t => if t = 1 then [(1, 10)] else if t = 2 then [(2, 10)] else [])
  (fun _ => none) (fun t => t = 4)
/-- One `Move(+10)` at tick 1; completes at tick 4. -/
def I_A1 : Input := inQ (fun t => if t = 1 then [(1, 10)] else []) (fun _ => none) (fun t => t = 4)

/-- **Multiplicity is preserved**: two identical commands are two jobs, and
    after the first completes the second moves the desired position again
    — `20` against `10`. -/
theorem exA_multiplicity :
    runQ ΔQ I_A2 2 = some [(1, 10), (2, 10)] ∧ runQ ΔQ I_A1 2 = some [(1, 10)] ∧
    runD ΔQ I_A2 1 = some 10 ∧ runD ΔQ I_A1 1 = some 10 ∧
    runQ ΔQ I_A2 4 = some [(2, 10)] ∧ runQ ΔQ I_A1 4 = some [] ∧
    runD ΔQ I_A2 5 = some 20 ∧ runD ΔQ I_A1 5 = some 10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### B — ordering -/

def I_AB : Input := inQ (fun t => if t = 1 then [(1, 10)] else if t = 2 then [(2, 30)] else [])
  (fun _ => none) (fun t => t = 3)
def I_BA : Input := inQ (fun t => if t = 1 then [(2, 30)] else if t = 2 then [(1, 10)] else [])
  (fun _ => none) (fun t => t = 3)

/-- **Order is preserved where it is observable**: `A; B` moves to 10 then
    40, `B; A` to 30 then 40 — the same final target, different desired
    trajectories. -/
theorem exB_ordering :
    runQ ΔQ I_AB 2 = some [(1, 10), (2, 30)] ∧ runQ ΔQ I_BA 2 = some [(2, 30), (1, 10)] ∧
    runD ΔQ I_AB 2 = some 10 ∧ runD ΔQ I_BA 2 = some 30 ∧
    runD ΔQ I_AB 4 = some 40 ∧ runD ΔQ I_BA 4 = some 40 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### C — same-tick multiplicity -/

def I_C_AB : Input := inQ (fun t => if t = 1 then [(1, 10), (2, 30)] else []) (fun _ => none) (fun t => t = 2)
def I_C_BA : Input := inQ (fun t => if t = 1 then [(2, 30), (1, 10)] else []) (fun _ => none) (fun t => t = 2)
def I_C_A : Input := inQ (fun t => if t = 1 then [(1, 10)] else []) (fun _ => none) (fun t => t = 2)

/-- **Several occurrences in one tick lose nothing**: the batch is a list,
    with its order and multiplicity; three batches, three queues, three
    desired trajectories. -/
theorem exC_same_tick :
    runQ ΔQ I_C_AB 1 = some [(1, 10), (2, 30)] ∧ runQ ΔQ I_C_BA 1 = some [(2, 30), (1, 10)] ∧
    runQ ΔQ I_C_A 1 = some [(1, 10)] ∧
    runD ΔQ I_C_AB 1 = some 10 ∧ runD ΔQ I_C_BA 1 = some 30 ∧ runD ΔQ I_C_A 1 = some 10 ∧
    runD ΔQ I_C_AB 3 = some 40 ∧ runD ΔQ I_C_BA 3 = some 40 ∧ runD ΔQ I_C_A 3 = some 10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### D — cancellation by concept identity -/

/-- `A, B` at tick 1; cancel 2 (queued) at tick 2; cancel 1 (active) at
    tick 3; cancel 9 (unknown) at tick 4 with `C = (3, 5)` submitted. -/
def I_D : Input := inQ (fun t => if t = 1 then [(1, 10), (2, 30)] else if t = 4 then [(3, 5)] else [])
  (fun t => if t = 2 then some 2 else if t = 3 then some 1 else if t = 4 then some 9 else none) (fun _ => false)

theorem exD_cancellation :
    runQ ΔQ I_D 1 = some [(1, 10), (2, 30)] ∧
    runQ ΔQ I_D 2 = some [(1, 10)] ∧          -- the queued job is gone
    runQ ΔQ I_D 3 = some [] ∧                 -- the active job is gone; nothing starts
    runD ΔQ I_D 3 = some 10 ∧
    runQ ΔQ I_D 4 = some [(3, 5)] ∧           -- an unknown id cancels nothing; C starts
    runD ΔQ I_D 4 = some 15 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### E — the bounded queue -/

def I_E : Input := inQ (fun t => if t = 1 then [(1, 10), (2, 30), (3, 5)] else []) (fun _ => none) (fun _ => false)

/-- **A bounded queue refuses, and the refusal is state.**  With `cap = 2`
    the third job is not queued and `overflow` says so; the next tick
    nothing overflows. -/
theorem exE_bounded :
    runQ ΔQ I_E 1 = some [(1, 10), (2, 30)] ∧ runB ΔQ I_E overflow 1 = some true ∧
    runB ΔQ I_E overflow 2 = some false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ### F — concept identity: a retried submission -/

/-- The host submits job 1 and, hearing no answer, submits job 1 again. -/
def I_F : Input := inQ (fun t => if t = 1 ∨ t = 2 then [(1, 10)] else []) (fun _ => none) (fun _ => false)

/-- **Identity that affects behaviour lives in the state.**  Under the
    dedup design the retry is one job; under the plain design it is two —
    and both are designs, not transport policies.  (Whether a *transport*
    retry with a fresh sequence number is one or two submissions is the
    provider's, L below.) -/
theorem exF_identity :
    runQ ΔQd I_F 2 = some [(1, 10)] ∧ runQ ΔQ I_F 2 = some [(1, 10), (1, 10)] := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## M — the motion state -/

def fb : DeclId := ⟨20⟩            -- opt Sample: a feedback sample, or none this tick
def target : DeclId := ⟨21⟩        -- Position
def reset : DeclId := ⟨22⟩         -- bool
def ackNow : DeclId := ⟨23⟩        -- bool: the device acknowledged the current target this tick
def age : DeclId := ⟨24⟩           -- ticks since the last sample
def fresh : DeclId := ⟨25⟩
def timedOut : DeclId := ⟨26⟩
def lastPos : DeclId := ⟨27⟩
def lastVel : DeclId := ⟨28⟩
def err : DeclId := ⟨29⟩
def inTol : DeclId := ⟨30⟩
def settled : DeclId := ⟨31⟩       -- consecutive fresh in-tolerance samples
def doneM : DeclId := ⟨32⟩
def fault : DeclId := ⟨33⟩         -- latched
def targetChanged : DeclId := ⟨34⟩
def acked : DeclId := ⟨35⟩

def VF : Ty := .prod Q0 .bool
def posF : Expr := .prim (.fst Q0 VF)
def velF : Expr := .lam Sample (fstE Q0 .bool (sndE Q0 VF (.var 0)))
def faultF : Expr := .lam Sample (sndE Q0 .bool (sndE Q0 VF (.var 0)))

def ageBody : Expr :=
  iteE Q0 (isSomeE Sample (.declRef fb)) (lit 0) (addE (.delay (lit 0) (.declRef age)) (lit 1))
def freshBody : Expr := ltE Dim.zero (.declRef age) (lit 3)
def timedOutBody : Expr := notE (ltE Dim.zero (.declRef age) (lit 6))
def lastPosBody : Expr :=
  getDE Q0 (app2 (mapOptF Sample Q0) posF (.declRef fb)) (.delay (lit 0) (.declRef lastPos))
def lastVelBody : Expr :=
  getDE Q0 (app2 (mapOptF Sample Q0) velF (.declRef fb)) (.delay (lit 0) (.declRef lastVel))
/-- `|lastPos − target|` on naturals. -/
def errBody : Expr :=
  addE (subE (.declRef lastPos) (.declRef target)) (subE (.declRef target) (.declRef lastPos))
def inTolBody : Expr := andE (ltE Dim.zero (.declRef err) (lit 2)) (ltE Dim.zero (.declRef lastVel) (lit 1))
def settledBody : Expr :=
  iteE Q0 (andE (.declRef fresh) (.declRef inTol)) (addE (.delay (lit 0) (.declRef settled)) (lit 1)) (lit 0)
def doneMBody : Expr := notE (ltE Dim.zero (.declRef settled) (lit 2))
def faultBody : Expr :=
  andE (orE (.delay (.boolLit false) (.declRef fault))
      (getDE .bool (app2 (mapOptF Sample .bool) faultF (.declRef fb)) (.boolLit false)))
    (notE (.declRef reset))
def targetChangedBody : Expr :=
  notE (eqE Q0 trivial (.declRef target) (.delay (lit 0) (.declRef target)))
def ackedBody : Expr :=
  iteE .bool (.declRef targetChanged) (.declRef ackNow)
    (orE (.delay (.boolLit false) (.declRef acked)) (.declRef ackNow))

/-- The motion design; `target` is an input or, in the composed design, the
    queue's desired position. -/
def motionDecls (targetBody : Option Expr) : List DesignDecl := [
  ⟨fb, ⟨Fb, []⟩, none⟩,
  ⟨target, ⟨Q0, []⟩, targetBody⟩,
  ⟨reset, ⟨.bool, []⟩, none⟩,
  ⟨ackNow, ⟨.bool, []⟩, none⟩,
  ⟨age, ⟨Q0, []⟩, some ageBody⟩,
  ⟨fresh, ⟨.bool, []⟩, some freshBody⟩,
  ⟨timedOut, ⟨.bool, []⟩, some timedOutBody⟩,
  ⟨lastPos, ⟨Q0, []⟩, some lastPosBody⟩,
  ⟨lastVel, ⟨Q0, []⟩, some lastVelBody⟩,
  ⟨err, ⟨Q0, []⟩, some errBody⟩,
  ⟨inTol, ⟨.bool, []⟩, some inTolBody⟩,
  ⟨settled, ⟨Q0, []⟩, some settledBody⟩,
  ⟨doneM, ⟨.bool, []⟩, some doneMBody⟩,
  ⟨fault, ⟨.bool, []⟩, some faultBody⟩,
  ⟨targetChanged, ⟨.bool, []⟩, some targetChangedBody⟩,
  ⟨acked, ⟨.bool, []⟩, some ackedBody⟩]

def ΔM : DeclEnv := .ofList (motionDecls none)

theorem ΔM_typed : GlobalWF (fun _ _ _ => True) Θ ΔM := GlobalWF.ofList (by decide)
def rankM : DeclId → Nat := fun d =>
  if d = age ∨ d = lastPos ∨ d = lastVel ∨ d = fault ∨ d = targetChanged then 1
  else if d = fresh ∨ d = timedOut ∨ d = err ∨ d = acked then 2
  else if d = inTol then 3 else if d = settled then 4 else if d = doneM then 5 else 0
theorem ΔM_causal : Causal ΔM :=
  Causal.ofList rankM 6 (by intro d; unfold rankM; (repeat' split) <;> omega) (by decide)
theorem ΔM_clocked : WellClocked ΚQ ΔM := WellClocked.ofList (by decide)

def sample (p v : Nat) (f : Bool) : Value := .pair (.nat p) (.pair (.nat v) (.bool f))

/-- Inputs: a sample per tick (or none), the target, reset, ack. -/
def inM (fbs : Nat → Option (Nat × Nat × Bool)) (tg : Nat → Nat) (rs : Nat → Bool) (ak : Nat → Bool) : Input :=
  fun d t =>
    if d = fb then (match fbs t with | some (p, v, f) => .some (sample p v f) | none => .none)
    else if d = target then .nat (tg t)
    else if d = reset then .bool (rs t)
    else if d = ackNow then .bool (ak t)
    else .nat 0

def runN (Δ : DeclEnv) (I : Input) (d : DeclId) (t : Nat) : Option Nat :=
  (evalF Δ I 200 t [] (.declRef d)).bind nat?

/-! ### G — freshness and timeout -/

/-- Two good samples, then silence. -/
def I_G : Input := inM (fun t => if t ≤ 1 then some (10, 0, false) else none) (fun _ => 10)
  (fun _ => false) (fun _ => false)

/-- **Freshness is state**: the age counts ticks without a sample; `fresh`
    ends at three, `timedOut` begins at six; `settled` keeps counting on
    the held value while fresh and resets when stale — completion depends
    on freshness. -/
theorem exG_freshness :
    runN ΔM I_G age 1 = some 0 ∧ runN ΔM I_G age 4 = some 3 ∧ runN ΔM I_G age 7 = some 6 ∧
    runB ΔM I_G fresh 3 = some true ∧ runB ΔM I_G fresh 4 = some false ∧
    runB ΔM I_G timedOut 6 = some false ∧ runB ΔM I_G timedOut 7 = some true ∧
    runN ΔM I_G settled 3 = some 4 ∧ runN ΔM I_G settled 4 = some 0 ∧
    runB ΔM I_G doneM 3 = some true ∧ runB ΔM I_G doneM 4 = some false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### H — repeated samples before settling -/

/-- In tolerance, out (moving), in, in, then in position but moving. -/
def I_H : Input := inM
  (fun t => if t = 0 then some (10, 0, false) else if t = 1 then some (13, 2, false)
    else if t = 4 then some (10, 3, false) else some (10, 0, false))
  (fun _ => 10) (fun _ => false) (fun _ => false)

/-- **Two consecutive fresh in-tolerance samples complete**; one does not;
    velocity counts. -/
theorem exH_settling :
    runN ΔM I_H settled 0 = some 1 ∧ runN ΔM I_H settled 1 = some 0 ∧
    runN ΔM I_H settled 2 = some 1 ∧ runN ΔM I_H settled 3 = some 2 ∧
    runB ΔM I_H doneM 2 = some false ∧ runB ΔM I_H doneM 3 = some true ∧
    runN ΔM I_H settled 4 = some 0 ∧ runB ΔM I_H doneM 4 = some false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### I — fault latching -/

def I_I : Input := inM (fun t => some (10, 0, t = 1)) (fun _ => 10) (fun t => t = 4) (fun _ => false)

/-- **A fault latches until reset**: one faulty sample at tick 1 holds the
    fault through tick 3; reset at tick 4 clears it. -/
theorem exI_fault_latch :
    runB ΔM I_I fault 0 = some false ∧ runB ΔM I_I fault 1 = some true ∧
    runB ΔM I_I fault 3 = some true ∧ runB ΔM I_I fault 4 = some false ∧
    runB ΔM I_I fault 5 = some false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### J — acknowledgement state -/

def I_J : Input := inM (fun _ => some (10, 0, false)) (fun t => if t < 3 then 10 else 20)
  (fun _ => false) (fun t => t = 1 ∨ t = 4)

/-- **An acknowledgement is state tied to the target**: acked at tick 1,
    it holds through tick 2, lapses when the target changes at tick 3, and
    holds again after the next ack. -/
theorem exJ_ack :
    runB ΔM I_J acked 0 = some false ∧ runB ΔM I_J acked 1 = some true ∧
    runB ΔM I_J acked 2 = some true ∧ runB ΔM I_J acked 3 = some false ∧
    runB ΔM I_J acked 4 = some true ∧ runB ΔM I_J acked 5 = some true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## The composed controller: the queue drives the target, the motion
    state completes the job -/

/-- Q with `done := delay false doneM`, M with `target := desired`: one
    design, one domain, no cycle (`done` reads the previous tick). -/
def ΔQM : DeclEnv := .ofList (
  (queueDecls (.declRef submit) false).filter (fun h => h.id ≠ done) ++
  [⟨done, ⟨.bool, []⟩, some (.delay (.boolLit false) (.declRef doneM))⟩] ++
  motionDecls (some (.declRef desired)))

theorem ΔQM_typed : GlobalWF (fun _ _ _ => True) Θ ΔQM := GlobalWF.ofList (by decide)
def rankQM : DeclId → Nat := fun d =>
  if d = desired then 5 else if d = desiredC ∨ d = target then 6 else if d = err ∨ d = targetChanged then 7
  else if d = inTol ∨ d = acked then 8 else if d = settled then 9 else if d = doneM then 10 else rankQ d + rankM d
theorem ΔQM_causal : Causal ΔQM :=
  Causal.ofList rankQM 11 (by intro d; unfold rankQM rankQ rankM; (repeat' split) <;> omega) (by decide)
theorem ΔQM_clocked : WellClocked ΚQ ΔQM := WellClocked.ofList (by decide)

/-- Job 1 (+10) at tick 1 and job 2 (+5) at tick 2; the motor reports 0
    for two ticks, then 10 at rest. -/
def I_QM : Input := fun d t =>
  if d = submit ∨ d = cancel then inQ (fun t => if t = 1 then [(1, 10)] else if t = 2 then [(2, 5)] else [])
    (fun _ => none) (fun _ => false) d t
  else inM (fun t => if t ≤ 1 then some (0, 0, false) else some (10, 0, false))
    (fun _ => 0) (fun _ => false) (fun _ => false) d t

/-- The composed design is deeper per tick (the specification interpreter
    memoizes nothing), so its runners carry more fuel. -/
def runQM (d : DeclId) (t : Nat) : Option Value := evalF ΔQM I_QM 2000 t [] (.declRef d)

set_option maxRecDepth 8000 in
/-- **The composed run**: job 1 starts at tick 1 (desired 10); the motor
    is at 10 and at rest from tick 2, so `settled` reaches 2 at tick 3 and
    `doneM` holds; at tick 4 the queue pops job 1, job 2 starts and the
    desired position becomes 15, at which the motor is not yet settled. -/
theorem exQM_composed :
    (runQM desired 1).bind nat? = some 10 ∧ (runQM queue 2).bind jobs? = some [(1, 10), (2, 5)] ∧
    (runQM settled 3).bind nat? = some 2 ∧ (runQM doneM 3).bind bool? = some true ∧
    (runQM queue 4).bind jobs? = some [(2, 5)] ∧ (runQM desired 4).bind nat? = some 15 ∧
    (runQM settled 4).bind nat? = some 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## K — cross-clock delivery through the window -/

def submitH : DeclId := ⟨40⟩    -- opt Job in the host domain: one submission per host tick, or none
def logH : DeclId := ⟨41⟩
def logDH : DeclId := ⟨42⟩
def seenH : DeclId := ⟨43⟩
def cursorH : DeclId := ⟨44⟩
def windowH : DeclId := ⟨45⟩
def cH : ClockId := ⟨1⟩          -- the host's domain, every tick
def cC : ClockId := ⟨2⟩          -- the controller's domain, every third tick
def bids : BDL.Buffer.Ids := ⟨submitH, logH, logDH, seenH, cursorH, windowH⟩

/-- The queue in the controller's domain reads `flatten window` — the host
    submissions since the controller's previous activation, in order. -/
def ΔK : DeclEnv := .ofList (
  queueDecls (.app (flattenF JobT) (.declRef windowH)) false ++
  BDL.Buffer.decls OJob cH bids ++ [⟨submitH, ⟨OJob, []⟩, none⟩])
def SK : Sched := Sched.periodic fun c => if c = cC then 3 else 1
def ΚK : ClockEnv := fun d => if d = submitH ∨ d = logH then some cH else some cC

theorem ΔK_typed : GlobalWF (fun _ _ _ => True) Θ ΔK := GlobalWF.ofList (by decide)
def rankK : DeclId → Nat := fun d =>
  if d = logH ∨ d = seenH then 1 else if d = windowH then 2 else if d = admitted then 3
  else if d = queue ∨ d = overflow then 4 else if d = activeId then 5 else if d = starts then 6
  else if d = desired then 7 else if d = desiredC then 8 else 0
theorem ΔK_causal : Causal ΔK :=
  Causal.ofList rankK 9 (by intro d; unfold rankK; (repeat' split) <;> omega) (by decide)
theorem ΔK_clocked : WellClocked ΚK ΔK := WellClocked.ofList (by decide)

/-- The host submits A at tick 1, B at tick 2, C at tick 4; the controller
    completes the active job at its tick 6. -/
def I_K : Input := fun d t =>
  if d = submitH then
    (if t = 1 then .some (.pair (.nat 1) (.nat 10)) else if t = 2 then .some (.pair (.nat 2) (.nat 30))
     else if t = 4 then .some (.pair (.nat 3) (.nat 5)) else .none)
  else if d = done then .bool (t = 6) else if d = cancel then .none else .nat 0

def runKQ (t : Nat) : Option (List (Nat × Nat)) := (mevalF SK ΔK I_K 200 cC t [] (.declRef queue)).bind jobs?
def runKD (t : Nat) : Option Nat := (mevalF SK ΔK I_K 200 cC t [] (.declRef desired)).bind nat?

/-- **Occurrences cross domains without loss**: at the controller's tick 3
    the window holds the host's ticks 0–2, flattened to `[A, B]`; at tick 6
    A has completed and C has arrived — `[B, C]`, desired `40`. -/
theorem exK_cross_clock :
    runKQ 3 = some [(1, 10), (2, 30)] ∧ runKD 3 = some 10 ∧
    runKQ 6 = some [(2, 30), (3, 5)] ∧ runKD 6 = some 40 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## L — transport identity: two providers, one Source trace -/

def rSeq : DeclId := ⟨60⟩     -- raw: (sequence number, batch)
def rFrames : DeclId := ⟨61⟩  -- raw: per-job frames (frame id, job)
def FrameT : Ty := .prod Q0 JobT
def SeqRaw : Ty := .prod Q0 Jobs
def FramesRaw : Ty := .list FrameT

/-- Provider 1: a transport that numbers each batch; the channel discards
    the number. -/
def chBatch : Channel SeqRaw where
  rep := Jobs
  tr := .lam SeqRaw (sndE Q0 Jobs (.var 0))
  transfer := fun v => match v with | .pair _ b => b | v => v
  rep_semFree := by decide
  rep_data := by decide
  tr_pure := by simp [sndE, Expr.Pure]
  computes := by
    rintro v ⟨a, b, rfl, _, _⟩
    have h := Ev.appClo (Δ := DeclEnv.empty) (I := fun _ _ => Value.pair a b) (t := 0) (ρ := [])
      (f := .lam SeqRaw (sndE Q0 Jobs (.var 0))) (a := .declRef ⟨0⟩) (ρ' := []) (body := _)
      (va := .pair a b) .lam (.refInput rfl) (Ev.appPrim .prim (.var rfl))
    unfold Transduces
    simpa [applyPrim, Prim.arity, Prim.compute] using h

/-- Provider 2: a transport that frames each job with its own id; the
    channel maps the ids away. -/
def chFrames : Channel FramesRaw where
  rep := Jobs
  tr := .lam FramesRaw (app2 (mapF FrameT JobT) (.prim (.snd Q0 JobT)) (.var 0))
  transfer := fun v => match v with | .list vs => .list (vs.map fun w => applyPrim (.snd Q0 JobT) [w]) | v => v
  rep_semFree := by decide
  rep_data := by decide
  tr_pure := by simp [app2, mapF, consE, nilE, Expr.Pure]
  computes := by
    rintro v ⟨vs, rfl, _⟩
    have h := Ev.appClo (Δ := DeclEnv.empty) (I := fun _ _ => Value.list vs) (t := 0) (ρ := [])
      (f := .lam FramesRaw (app2 (mapF FrameT JobT) (.prim (.snd Q0 JobT)) (.var 0))) (a := .declRef ⟨0⟩)
      (ρ' := []) (body := _) (va := .list vs) .lam (.refInput rfl)
      (map_spec FrameT JobT (.prim) (.var rfl) (fun x _ => Or.inr ⟨_, [], rfl, rfl⟩))
    unfold Transduces
    simpa using h

def PSeq : Provision SeqRaw := .one rSeq submit (some c0) chBatch
def PFrames : Provision FramesRaw := .one rFrames submit (some c0) chFrames

theorem wfSeq : WF Θ ΔQ PSeq := WF.one rfl (by decide) (by decide) rfl rfl rfl (infer_sound (by decide))
theorem wfFrames : WF Θ ΔQ PFrames := WF.one rfl (by decide) (by decide) rfl rfl rfl (infer_sound (by decide))

/-- The submissions: A at tick 1, B at tick 2. -/
def batch : Nat → List (Nat × Nat) := fun t => if t = 1 then [(1, 10)] else if t = 2 then [(2, 30)] else []
def jobsV (l : List (Nat × Nat)) : Value := .list (l.map fun p => .pair (.nat p.1) (.nat p.2))
def framesV (t : Nat) (l : List (Nat × Nat)) : Value :=
  .list (l.map fun p => .pair (.nat (100 + 10 * t + p.1)) (.pair (.nat p.1) (.nat p.2)))
/-- What the abstract design sees: the batches, completion at tick 3. -/
def I_L : Input := inQ batch (fun _ => none) (fun t => t = 3)
/-- Provider 1's raw input: batch `t` numbered `t`. -/
def I_L1 : Input := fun d t => if d = rSeq then .pair (.nat t) (jobsV (batch t)) else I_L d t
/-- Provider 2's raw input: each job framed with `100 + 10·t + id`. -/
def I_L2 : Input := fun d t => if d = rFrames then framesV t (batch t) else I_L d t

theorem jobsV_tyVal (l : List (Nat × Nat)) : TyVal Jobs (jobsV l) := by
  refine ⟨_, rfl, ?_⟩
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨p, _, rfl⟩ := hw
  exact ⟨_, _, rfl, ⟨_, rfl⟩, ⟨_, rfl⟩⟩
theorem framesV_tyVal (t : Nat) (l : List (Nat × Nat)) : TyVal FramesRaw (framesV t l) := by
  refine ⟨_, rfl, ?_⟩
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨p, _, rfl⟩ := hw
  exact ⟨_, _, rfl, ⟨_, rfl⟩, ⟨_, _, rfl, ⟨_, rfl⟩, ⟨_, rfl⟩⟩⟩

theorem I_L_noClo (d : DeclId) (t : Nat) : (I_L d t).NoClo := by
  unfold I_L inQ
  split
  · exact TyVal.noClo (τ := Jobs) (by decide) (jobsV_tyVal _)
  · split
    · split <;> (intro h; cases h <;> (rename_i h'; cases h'))
    · split <;> (intro h; cases h)

theorem rawSeq : RawInput PSeq I_L1 := by
  refine ⟨fun t => ?_, fun d t => ?_⟩
  · exact ⟨_, _, rfl, ⟨_, rfl⟩, jobsV_tyVal _⟩
  · unfold I_L1; split
    · exact TyVal.noClo (τ := SeqRaw) (by decide) ⟨_, _, rfl, ⟨_, rfl⟩, jobsV_tyVal _⟩
    · exact I_L_noClo d t
theorem rawFrames : RawInput PFrames I_L2 := by
  refine ⟨fun t => framesV_tyVal _ _, fun d t => ?_⟩
  unfold I_L2; split
  · exact TyVal.noClo (τ := FramesRaw) (by decide) (framesV_tyVal _ _)
  · exact I_L_noClo d t

theorem frames_transfer (t : Nat) (l : List (Nat × Nat)) : chFrames.transfer (framesV t l) = jobsV l := by
  simp [chFrames, framesV, jobsV, List.map_map, applyPrim, Prim.arity, Prim.compute, Function.comp]

/-- **The same semantic trace**: off the two raw declarations the induced
    inputs agree — at `submit` both channels deliver the batch. -/
theorem sameL : SameTrace ΔQ PSeq PFrames I_L1 I_L2 := by
  intro d t h₁ h₂
  simp only [induced, PSeq, PFrames, Provision.one]
  by_cases hs : d = submit
  · subst hs
    simp [chBatch, I_L1, I_L2, frames_transfer, rSeq, rFrames, submit, DeclEnv.tyView, ΔQ, DeclEnv.ofList,
      queueDecls, Jobs, wrapAt]
  · simp only [PSeq, PFrames, Provision.one] at h₁ h₂
    simp [hs, I_L1, I_L2, h₁, h₂]

theorem nmL : NoMention ΔQ rSeq := NoMention.of_globalWF ΔQ_typed rfl
theorem nmL' : NoMention ΔQ rFrames := NoMention.of_globalWF ΔQ_typed rfl

/-- **`two_providers_same_behavior`, instantiated**: every declaration of
    the queue design evaluates alike under the two providers. -/
theorem exL_theorem (d : DeclId) (hd : ΔQ d ≠ none) (c : ClockId) (t : Nat) (v : Value) :
    MEv Sched.always (provision ΔQ PSeq) I_L1 c t [] (.declRef d) v ↔
      MEv Sched.always (provision ΔQ PFrames) I_L2 c t [] (.declRef d) v :=
  two_providers_same_behavior wfSeq wfFrames nmL nmL' rawSeq rawFrames sameL
    (by simp [Expr.refs]; intro h; exact hd (h ▸ wfSeq.fresh))
    (by simp [Expr.refs]; intro h; exact hd (h ▸ wfFrames.fresh))
    (fun _ h => by simp at h) (fun _ h => by simp at h)

/-- Executed: the queues and desired positions under the two providers
    coincide with each other and with the abstract design under the
    semantic input, tick by tick; the raw readings differ at every tick. -/
theorem exL_executed :
    (∀ t ∈ [1, 2, 3, 4], runQ (provision ΔQ PSeq) I_L1 t = runQ ΔQ I_L t ∧
      runQ (provision ΔQ PFrames) I_L2 t = runQ ΔQ I_L t ∧
      runD (provision ΔQ PSeq) I_L1 t = runD ΔQ I_L t ∧ runD (provision ΔQ PFrames) I_L2 t = runD ΔQ I_L t) ∧
    runQ ΔQ I_L 2 = some [(1, 10), (2, 30)] ∧ runD ΔQ I_L 4 = some 40 ∧
    -- the two providers' raw readings at tick 1: a numbered batch and a framed job
    Value.beq (I_L1 rSeq 1) (.pair (.nat 1) (.list [.pair (.nat 1) (.nat 10)])) = true ∧
    Value.beq (I_L2 rFrames 1) (.list [.pair (.nat 111) (.pair (.nat 1) (.nat 10))]) = true := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## N — the paired axis: one output, a pair command -/

def oY : OutputId := ⟨0⟩       -- the logical output: DesiredPos
def pY : OutputId := ⟨1⟩       -- the machine sink: the (motor 2, motor 3) pair command
def eY : DeclId := ⟨50⟩
def specY : OutputSpec := ⟨.sem DesiredPos, c0⟩
def ΩQ : OutputEnv := .ofList [(oY, specY)]
def βQ : DriveEnv := .ofList [(desiredC, oY)]
theorem βQ_wf : DriveWF ΩQ ΚQ ΔQ βQ := DriveWF.ofList (by decide)
theorem βQ_single : SingleDriver βQ := SingleDriver.ofList (by decide)

/-- The Y-pair encoder: one position, two motor commands `(p, p)`. -/
def pairEnc : Encoder where
  rep := Q0
  raw := .prod Q0 Q0
  encode := .lam Q0 (pairE Q0 Q0 (.var 0) (.var 0))
  transfer := fun v => .pair v v
  rep_semFree := trivial
  rep_data := trivial
  raw_semFree := by decide
  raw_data := by decide
  encode_pure := by simp [pairE, app2, Expr.Pure]
  computes := by rintro v ⟨n, rfl⟩; exact .appClo .lam (.refInput rfl) (Ev.prim2 rfl (.var rfl) (.var rfl))

def RY : Realization := ⟨oY, desiredC, pY, eY, pairEnc⟩
theorem wfY : WF Θ ΔQ ΩQ βQ ΚQ RY specY :=
  WF.of_driveWF βQ_wf rfl rfl rfl rfl (by decide) (infer_sound (by decide))
def ΔY : DeclEnv := lowerΔ ΔQ RY specY

theorem ΔY_causal : Causal ΔY := lower_causal wfY (NoMention.of_globalWF ΔQ_typed rfl) ΔQ_causal

/-- **The pair command at tick 2 under `I_AB`**: desired 10, so the sink
    carries `(10, 10)` — one raw command for two motors, specified by one
    value.  The frame protocol (prepare 2, prepare 3, commit) is the
    adapter's reading of this one pair. -/
theorem exN_pair :
    RawCommand Sched.always ΔQ I_AB ΩQ βQ RY 2 (.pair (.nat 10) (.nat 10)) ∧
    (mevalF Sched.always ΔY I_AB 200 c0 2 [] (.declRef eY)).bind pair? = some (10, 10) ∧
    (mevalF Sched.always ΔY I_AB 200 c0 4 [] (.declRef eY)).bind pair? = some (40, 40) := by
  refine ⟨⟨specY, .sem DesiredPos (.nat 10), rfl, ⟨desiredC, specY, rfl, rfl, ?_⟩, rfl⟩, ?_, ?_⟩
  · exact (single_domain_embedding _).mpr (Ev.of_evalF (Δ := ΔQ) (I := I_AB) (fuel := 200) rfl)
  · decide
  · decide

/-- Two realizations of the one output on two separate sinks agree with the
    pair: `paired_commands_of_one_value`, instantiated with the identity
    encoder on each motor. -/
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
def RM2 : Realization := ⟨oY, desiredC, ⟨2⟩, ⟨51⟩, idEnc⟩
def RM3 : Realization := ⟨oY, desiredC, ⟨3⟩, ⟨52⟩, idEnc⟩

theorem exN_two_motors {t : Nat} {w₂ w₃ : Value}
    (h₂ : RawCommand Sched.always ΔQ I_AB ΩQ βQ RM2 t w₂) (h₃ : RawCommand Sched.always ΔQ I_AB ΩQ βQ RM3 t w₃) :
    w₂ = w₃ := by
  obtain ⟨spec, v, _, _, rfl, rfl⟩ := paired_commands_of_one_value βQ_single rfl h₂ h₃
  rfl

/-! ## P — builtin vs packaged -/

def yProfile : DeviceOutputProfile := ⟨pairEnc, [⟨⟨0⟩, .pwm, none, none⟩, ⟨⟨1⟩, .pwm, none, none⟩]⟩
def enBuiltin : OutputEntry := ⟨.builtin, yProfile⟩
def enPackaged : OutputEntry := ⟨.package ⟨7⟩, yProfile⟩

/-- **The origin is invisible**: the builtin and the packaged entry lower
    the queue design to one design, one sink, one command relation. -/
theorem exP_origin :
    assignOutput ΔQ enBuiltin oY desiredC pY eY specY = assignOutput ΔQ enPackaged oY desiredC pY eY specY ∧
    assignOutput ΔQ enBuiltin oY desiredC pY eY specY = ΔY ∧
    enBuiltin.origin ≠ enPackaged.origin :=
  ⟨(assign_indistinguishable (Ω := ΩQ) (β := βQ) (Κ := ΚQ) rfl oY desiredC pY eY specY).1, rfl, by decide⟩

/-! ## Q — the contract is not feasibility -/

/-- A board with one digital pin and no PWM. -/
def bare : Hardware := ⟨[⟨⟨4⟩, [.digitalIn, .digitalOut], []⟩], []⟩

/-- **Semantic admissibility is separate from deployment feasibility**: the
    pair profile satisfies the contract for `DesiredPos` and allocates on
    the Nano (two PWM lines) — admissible — and satisfies the same contract
    on the bare board, where it is not feasible and hence not admissible.
    The contract judgment did not change between the boards. -/
theorem exQ_contract_not_feasible :
    OutputContract Θ (.sem DesiredPos) yProfile ∧
    Feasible HardwareCase.nano yProfile ∧ Admissible Θ (.sem DesiredPos) HardwareCase.nano yProfile ∧
    ¬ Feasible bare yProfile ∧ ¬ Admissible Θ (.sem DesiredPos) bare yProfile := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

end BDL.Experiments.Communication
