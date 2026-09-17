import BDL.Validation.Capacity
import BDL.Behavior.Preservation
import BDL.Experiments.ClockAlternatives

/-!
# Phase 9a — Buffered transport: alternatives, execution, counterexamples

§1 the models A–E of the brief, compared on observable windows;
§2 the buffered transport executed on Phase 5's multi-rate example
(`S₂`, `fast`/`slow`, the fast events `Iev₁`), against the `latest`
transport of Counterexample C;
§3 the negative examples A–F;
§4 a Phase-8a component transport: a fast sensor providing its log, a slow
consumer requiring it through a `sync` binding and computing the window.
-/

namespace BDL.Experiments.Buffer
open BDL BDL.Reactive BDL.Clock BDL.Buffer BDL.Validation.Capacity
open BDL.Experiments.Clock (fast slow S₂ evS evF fastClone)

/-! ## §1 Models A–E on observable windows -/

/-- A summary that only sees the newest `k` entries. -/
def BoundedBy (k : Nat) (f : Summary) : Prop := ∀ w, f w = f (dropOldest k w)

/-- **No bounded summary is lossless.**  Whatever fixed number of entries a
    summary keeps, two windows that agree on those entries and differ in
    length are identified.  Hence, if multiplicity and order are
    observable, unbounded sequence data is required: this is the negative
    half of the Phase-9a claim, for every summary, not only the tested
    ones. -/
theorem bounded_summary_not_lossless (k : Nat) (f : Summary) (hf : BoundedBy k f) : ¬ f.Lossless := by
  intro hl
  have h₁ := hf (List.replicate (k + 1) (Value.nat 0))
  have e₁ : dropOldest k (List.replicate (k + 1) (Value.nat 0)) = List.replicate k (Value.nat 0) := by
    simp [dropOldest, List.drop_replicate]
  rw [e₁] at h₁
  have hlen := congrArg List.length (hl _ _ h₁)
  rw [List.length_replicate, List.length_replicate] at hlen
  omega

/-- Model A — latest value only — is bounded by 1. -/
theorem latest_bounded : BoundedBy 1 latest := by
  intro w
  cases w with
  | nil => rfl
  | cons x xs =>
    have hne : dropOldest 1 (x :: xs) ≠ [] := by
      simp [dropOldest, List.drop_eq_nil_iff]
    unfold latest
    have hsplit : (x :: xs) = (x :: xs).take ((x :: xs).length - 1) ++ dropOldest 1 (x :: xs) :=
      (List.take_append_drop _ _).symm
    conv => lhs; rw [hsplit]
    rw [List.getLast?_append]
    cases hl : (dropOldest 1 (x :: xs)).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hne
    | some a => simp

/-- Model D — a fixed pair (the two newest) — is bounded by 2. -/
def pair : Summary := fun w => .list (dropOldest 2 w)
theorem pair_bounded : BoundedBy 2 pair := by
  intro w
  unfold pair dropOldest
  rw [List.drop_drop, List.length_drop]
  congr 2
  omega

theorem modelA_not_lossless : ¬ latest.Lossless := bounded_summary_not_lossless 1 latest latest_bounded
theorem modelD_not_lossless : ¬ pair.Lossless := bounded_summary_not_lossless 2 pair pair_bounded

/-- Models B (count) and C (coalesce by sum) are not bounded, and not
    lossless either: they identify windows of equal length or equal total. -/
theorem modelB_not_lossless : ¬ count.Lossless := count_not_lossless
theorem modelC_not_lossless : ¬ sumNat.Lossless := sum_not_lossless

/-- Model E — the list — is lossless. -/
theorem modelE_lossless : asList.Lossless := buffer_lossless

/-- Which histories each model identifies, on one window family. -/
theorem models_identify :
    latest [.nat 1, .nat 2] = latest [.nat 2] ∧
    count [.nat 1, .nat 2] = count [.nat 2, .nat 1] ∧
    sumNat [.nat 1, .nat 4] = sumNat [.nat 2, .nat 3] ∧
    pair [.nat 0, .nat 1, .nat 2] = pair [.nat 1, .nat 2] ∧
    asList [.nat 1, .nat 2] ≠ asList [.nat 2] := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro h
  have := congrArg List.length (Value.list.inj h)
  simp at this

/-! ## §2 The buffered transport, executed on the Phase-5 example -/

def evF' : DeclId := ⟨140⟩
def logD' : DeclId := ⟨141⟩
def logDD : DeclId := ⟨142⟩
def seenD : DeclId := ⟨143⟩
def cursorD : DeclId := ⟨144⟩
def windowD : DeclId := ⟨145⟩

def OQ : Ty := .opt Q0

def bids : Ids := ⟨evF', logD', logDD, seenD, cursorD, windowD⟩

/-- Fast events at ticks 1 and 2 (as in `Iev₁`), transported to `slow`
    through the buffer.  `latest` (Phase 5's `dEvS`) is kept beside it. -/
def Δbuf : DeclEnv := .ofList ([⟨evF', ⟨OQ, []⟩, none⟩, ⟨evS, ⟨OQ, []⟩, some (.sync fast (.prim (.none Q0)) (.declRef evF'))⟩]
  ++ BDL.Buffer.decls OQ fast bids)

def Ibuf : Input := fun d t => if d = evF' then (if t = 1 ∨ t = 2 then .some (.nat t) else .none) else .nat 0

def optNat? : Value → Option (Option Nat)
  | .none => some none
  | .some (.nat n) => some (some n)
  | _ => none

def listOptNat? : Value → Option (List (Option Nat))
  | .list vs => go vs
  | _ => none
where
  go : List Value → Option (List (Option Nat))
    | [] => some []
    | v :: vs => match optNat? v, go vs with
      | some o, some os => some (o :: os)
      | _, _ => none

def runWindow (t : Nat) : Option (List (Option Nat)) :=
  (mevalF S₂ Δbuf Ibuf 64 slow t [] (.declRef windowD)).bind listOptNat?
def runLatest (t : Nat) : Option (Option Nat) :=
  (mevalF S₂ Δbuf Ibuf 64 slow t [] (.declRef evS)).bind optNat?

/-- **Theorem M, executed.**  At the slow activation 3 the window is the
    three fast values `[none, 1, 2]`; at 6 it is `[none, none, none]`;
    `latest` sees only `2` at 3.  The buffer preserves order and
    multiplicity where the single-instant transport does not. -/
theorem buffer_trace :
    runWindow 3 = some [none, some 1, some 2] ∧ runWindow 6 = some [none, none, none] ∧
    runLatest 3 = some (some 2) := by decide

/-- The two source histories Phase 5 could not tell apart under `latest`
    are told apart by the buffer. -/
def Ibuf₂ : Input := fun d t => if d = evF' then (if t = 2 then .some (.nat t) else .none) else .nat 0
def runWindow₂ (t : Nat) : Option (List (Option Nat)) :=
  (mevalF S₂ Δbuf Ibuf₂ 64 slow t [] (.declRef windowD)).bind listOptNat?
def runLatest₂ (t : Nat) : Option (Option Nat) :=
  (mevalF S₂ Δbuf Ibuf₂ 64 slow t [] (.declRef evS)).bind optNat?

theorem buffer_distinguishes_what_latest_identifies :
    runLatest 3 = runLatest₂ 3 ∧ runWindow 3 ≠ runWindow₂ 3 := by decide

/-- The elaborated declarations are well typed and well clocked, checked
    on the finite list. -/
def Κbuf : ClockEnv := fun d =>
  if d = evF' ∨ d = logD' then some fast
  else if d = logDD ∨ d = seenD ∨ d = cursorD ∨ d = windowD ∨ d = evS then some slow else none

theorem buffer_typed : GlobalWF (fun _ _ _ => True) ConceptEnv.empty Δbuf := GlobalWF.ofList (by decide)
theorem buffer_clocked : wellClockedCheck Κbuf
    ([⟨evF', ⟨OQ, []⟩, none⟩, ⟨evS, ⟨OQ, []⟩, some (.sync fast (.prim (.none Q0)) (.declRef evF'))⟩]
      ++ BDL.Buffer.decls OQ fast bids) = true := by decide

def bufRank : DeclId → Nat := fun d =>
  if d = evF' then 0 else if d = logD' ∨ d = evS ∨ d = logDD then 1 else if d = seenD then 2
  else if d = cursorD then 3 else 4
theorem buffer_causal : causalCheck
    ([⟨evF', ⟨OQ, []⟩, none⟩, ⟨evS, ⟨OQ, []⟩, some (.sync fast (.prim (.none Q0)) (.declRef evF'))⟩]
      ++ BDL.Buffer.decls OQ fast bids) bufRank = true := by decide

/-! ## §3 Negative examples -/

/-- **A** — same latest, different histories (already `buffer_distinguishes_what_latest_identifies`). -/
theorem negA : runLatest 3 = runLatest₂ 3 ∧ runWindow 3 ≠ runWindow₂ 3 := buffer_distinguishes_what_latest_identifies

/-- **B** — same count, different values or order. -/
theorem negB : count [.nat 1, .nat 2] = count [.nat 2, .nat 1] ∧ count [.nat 1, .nat 2] = count [.nat 3, .nat 4] ∧
    asList [.nat 1, .nat 2] ≠ asList [.nat 2, .nat 1] := by
  refine ⟨rfl, rfl, fun h => ?_⟩
  have := Value.list.inj h
  simp at this

/-- **C** — coalesce by sum collides: `1 + 4 = 2 + 3`. -/
theorem negC : sumNat [.nat 1, .nat 4] = sumNat [.nat 2, .nat 3] ∧ asList [.nat 1, .nat 4] ≠ asList [.nat 2, .nat 3] := by
  refine ⟨rfl, fun h => ?_⟩
  have := Value.list.inj h
  simp at this

/-- **D** — a fixed tuple bound too small: a pair cannot hold the three-entry
    window of tick 3. -/
theorem negD : pair [.none, .some (.nat 1), .some (.nat 2)] = pair [.some (.nat 1), .some (.nat 2)] ∧
    (windowTicks S₂ fast slow 3).length = 3 := ⟨rfl, by decide⟩

/-- **E** — insufficient capacity changes the trace: capacity 2 on the
    three-entry window drops the first fast tick (drop-oldest) or the last
    (drop-newest); capacity 3 keeps it. -/
theorem negE :
    dropOldest 2 [none, some 1, some 2] ≠ [none, some 1, some 2] ∧
    dropNewest 2 [none, some 1, some 2] ≠ [none, some 1, some 2] ∧
    dropOldest 3 [none, some 1, some 2] = [none, some 1, some 2] ∧
    ¬ CapacitySufficient S₂ fast slow 2 6 ∧ CapacitySufficient S₂ fast slow 3 30 ∧
    requiredCapacity S₂ fast slow 30 = 3 := by decide

/-- The periodic bound, on the example: `slow` has period 3. -/
theorem negE_bound (t : Nat) : windowLen (Sched.periodic fun c => if c = slow then 3 else 1) fast slow t ≤ 3 :=
  periodic_window_bound _ fast slow (by decide) t

/-- **F** — a clone of `fast` with the identical schedule is a different
    domain: listing the value does not make the direct read legal. -/
theorem negF : ¬ Clocked (fun d => if d = evF' then some fastClone else none) (some fast)
    (.app (.app (.prim (.cons OQ)) (.declRef evF')) (.prim (.nil OQ))) :=
  list_direct_wire_rejected (c := fast) (c' := fastClone) _ (by decide) (d := evF') OQ (by simp)

/-! ## §4 A component transport (Phase 8a machinery) -/

/-- Local identities of the two templates. -/
def evP : DeclId := ⟨0⟩      -- sensor: event input port
def logP : DeclId := ⟨1⟩     -- sensor: provided log
def logInP : DeclId := ⟨0⟩   -- consumer: required log
def seenP : DeclId := ⟨1⟩
def cursorP : DeclId := ⟨2⟩
def windowP : DeclId := ⟨3⟩
def cP : ClockId := ⟨0⟩      -- the clock parameter of each template

/-- The sensor: `ev` open, `log := cons ev (delay nil log)`, provided. -/
def sensorDesign : Design where
  Δ := .ofList [⟨evP, ⟨OQ, []⟩, none⟩, ⟨logP, ⟨.list OQ, []⟩, some (consE OQ (.declRef evP) (.delay (nilE OQ) (.declRef logP)))⟩]
  Θ := fun _ => none
  Κ := fun d => if d = evP ∨ d = logP then some cP else none
  Ω := fun _ => none
  β := fun _ => none

def sensor : BehaviorComponent where
  iface := { required := [], provided := [⟨logP, ⟨.list OQ, []⟩, some cP⟩, ⟨evP, ⟨OQ, []⟩, some cP⟩],
             params := [], clockParams := [cP] }
  design := sensorDesign
  width := 4
  internalSem := fun _ => false
  internalOut := fun _ => false

/-- The consumer: `logIn` required; `seen`, `cursor`, `window` as elaborated. -/
def consumerDesign : Design where
  Δ := .ofList [⟨logInP, ⟨.list OQ, []⟩, none⟩,
    ⟨seenP, ⟨Q0, []⟩, some (lenE OQ (.declRef logInP))⟩,
    ⟨cursorP, ⟨Q0, []⟩, some (.delay zeroE (.declRef seenP))⟩,
    ⟨windowP, ⟨.list OQ, []⟩, some (revE OQ (takeE OQ (subE (.declRef seenP) (.declRef cursorP)) (.declRef logInP)))⟩]
  Θ := fun _ => none
  Κ := fun d => if d.n < 4 then some cP else none
  Ω := fun _ => none
  β := fun _ => none

def consumer : BehaviorComponent where
  iface := { required := [⟨logInP, ⟨.list OQ, []⟩, some cP⟩], provided := [⟨windowP, ⟨.list OQ, []⟩, some cP⟩],
             params := [], clockParams := [cP] }
  design := consumerDesign
  width := 4
  internalSem := fun _ => false
  internalOut := fun _ => false

/-- Sensor in `fast`, consumer in `slow`; the log is transported by a `sync`
    binding with initial value `nil` — the buffered transport *is* a
    Phase-8a system: a provided accumulator and a `sync` binding. -/
def transport : BehaviorSystem where
  W := 8
  insts := [⟨sensor, fun _ => fast⟩, ⟨consumer, fun _ => slow⟩]
  bindings := [⟨.port 0 logP, 1, logInP, some (nilE OQ)⟩]
  Θg := fun _ => none
  Ωg := fun _ => none

def Itr : Input := fun d t =>
  if d = transport.declOf 0 evP then (if t = 1 ∨ t = 2 then .some (.nat t) else .none) else .nat 0

def runTr (t : Nat) : Option (List (Option Nat)) :=
  (mevalF S₂ transport.flattenΔ Itr 64 slow t [] (.declRef (transport.declOf 1 windowP))).bind listOptNat?

/-- The consumer's window in the flattened system: `[none, 1, 2]` at 3,
    `[none, none, none]` at 6 — the Phase-5 window, through Phase-8a
    composition, with no new binding kind. -/
theorem transport_trace : runTr 3 = some [none, some 1, some 2] ∧ runTr 6 = some [none, none, none] := by decide

/-- The alternative binding — the event itself through `sync` (`latest`) —
    loses the tick-1 event. -/
def latestTransport : BehaviorSystem :=
  { transport with insts := [⟨sensor, fun _ => fast⟩, ⟨latestConsumer, fun _ => slow⟩],
                   bindings := [⟨.port 0 evP, 1, logInP, some (.prim (.none Q0))⟩] }
where
  latestConsumer : BehaviorComponent :=
    { consumer with
      iface := { required := [⟨logInP, ⟨OQ, []⟩, some cP⟩], provided := [], params := [], clockParams := [cP] },
      design := { consumerDesign with Δ := .ofList [⟨logInP, ⟨OQ, []⟩, none⟩] } }

def runLatestTr (t : Nat) : Option (Option Nat) :=
  (mevalF S₂ latestTransport.flattenΔ Itr 64 slow t [] (.declRef (latestTransport.declOf 1 logInP))).bind optNat?

theorem latest_transport_loses : runLatestTr 3 = some (some 2) := by decide

end BDL.Experiments.Buffer
