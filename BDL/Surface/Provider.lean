import BDL.Surface.Assignment
import BDL.Validation.Capacity

/-!
# Phase 17 — The provider's occurrence contract

Below the raw reading (Phase 13's `r : () -> raw`) sits the *provider*:
the adapter-side function that turns what a transport delivered since the
previous tick into the one raw value the Source reads.  Phase 16 rested
every state encoding on what that value means and stated no contract
(FVI-0029).  This module states the smallest one and proves what it
gives, with nothing added to the kernel:

* A **delivery** is a raw payload with a *transport identity* — a
  sequence number, a frame id, a retry token: the provider's knowledge,
  never the design's.
* **One semantic occurrence per fresh transport identity.**  The provider
  keeps the identities it has delivered (`Seen`, adapter state like
  Phase 15's `Line`) and drops a delivery whose identity it has already
  delivered (`dedup`).  A transport retry is one occurrence; two
  deliveries with distinct identities and equal payloads are two —
  `Move(+10); Move(+10)` is never merged by payload.
* **Arrival order within a raw source.**  The batch is the fresh payloads
  in arrival order (`dedup_sublist`, `dedup_of_fresh`).
* **A per-tick bound `cap`.**  The batch is the first `cap` fresh payloads
  and `overflow` says whether any was left (`provide`): the refusal is a
  value the design can read — the raw reading is `(list raw, bool)` — and
  never a silent drop.  Which bound is enough is Phase 9a's capacity
  question on the physical arrival rate, a deployment assumption.
* **Several raw sources** are several raw readings, one provision each
  (Phase 13); a provider that merges them into one batch commits to an
  explicit, deterministic policy (`mergeBySource`: source order), and a
  design that reads per source is insensitive to which policy
  (`perSource_of_interleaving`).  No canonical physical order exists, and
  none is invented.

Composition with Phase 13: the batch value is the raw reading of a
provision with two channels over one raw declaration — `chItems`, the
batch, and `chOverflow`, the flag (`batchProvision`); every Phase-13
theorem applies.  A *scalar* Source is the batch provider sampled: the
last item or the held value (`Batch.latest`).

What is proved about replacement: equal batch streams give the same
semantic trace (`sameBatches_sameTrace`), so `two_providers_same_behavior`
applies; a transport retransmission inserted anywhere in the delivery
stream changes no batch (`run_retry`) and hence no behaviour
(`retry_invisible`).
-/

namespace BDL.Provider
open BDL BDL.Reactive BDL.Clock BDL.Provision BDL.Assignment

/-! ## Deliveries and the provider's state -/

/-- A raw delivery as the provider sees it: which raw source, the
    transport identity, the payload.  The identity is below the boundary. -/
structure Delivery where
  src : Nat
  token : Nat
  payload : Value

/-- The transport identities already delivered — the provider's state. -/
abbrev Seen := List Nat

/-- Drop the deliveries whose identity was delivered, keep the rest in
    arrival order, remember the identities. -/
def dedup (seen : Seen) : List Delivery → List Delivery × Seen
  | [] => ([], seen)
  | d :: ds =>
    if d.token ∈ seen then dedup seen ds
    else
      let r := dedup (d.token :: seen) ds
      (d :: r.1, r.2)

/-- The provider's contract: the per-tick bound. -/
structure Contract where
  cap : Nat

/-- What one provider tick delivers: the batch and whether it was cut. -/
structure Batch where
  items : List Value
  overflow : Bool

/-- **`provide`**: the first `cap` fresh payloads, in arrival order; the
    flag when more were fresh. -/
def provide (C : Contract) (seen : Seen) (ds : List Delivery) : Batch × Seen :=
  let r := dedup seen ds
  (⟨(r.1.map Delivery.payload).take C.cap, decide (C.cap < r.1.length)⟩, r.2)

/-- The raw value the Source reads: `(list raw, bool)`. -/
def Batch.value (b : Batch) : Value := .pair (.list b.items) (.bool b.overflow)

/-- A scalar provider is the batch provider sampled: the last item, or the
    held value when nothing arrived. -/
def Batch.latest (b : Batch) (held : Value) : Value := (b.items.getLast?).getD held

/-- The provider over a delivery stream: the state threads through the
    ticks. -/
def run (C : Contract) (ds : Nat → List Delivery) : Nat → Batch × Seen
  | 0 => provide C [] (ds 0)
  | t + 1 => provide C (run C ds t).2 (ds (t + 1))

def batch (C : Contract) (ds : Nat → List Delivery) (t : Nat) : Batch := (run C ds t).1
def seenAfter (C : Contract) (ds : Nat → List Delivery) (t : Nat) : Seen := (run C ds t).2

/-- The raw input a provider induces at the raw declaration `r`. -/
def rawInput (C : Contract) (ds : Nat → List Delivery) (r : DeclId) (base : Input) : Input :=
  fun d t => if d = r then (batch C ds t).value else base d t

/-! ## Deduplication -/

theorem dedup_nil (seen : Seen) : dedup seen [] = ([], seen) := rfl

/-- The kept deliveries are a subsequence of the arrivals: order and
    multiplicity of what is kept are the transport's. -/
theorem dedup_sublist (seen : Seen) : ∀ ds : List Delivery, (dedup seen ds).1.Sublist ds
  | [] => List.Sublist.refl _
  | d :: ds => by
    simp only [dedup]
    split
    · exact (dedup_sublist seen ds).cons d
    · exact (dedup_sublist (d.token :: seen) ds).cons_cons d

/-- **Distinct identities are all delivered**: when no arrival's identity
    was seen and the arrivals' identities are pairwise distinct, nothing is
    dropped — two deliveries with equal payloads and distinct identities
    are two occurrences. -/
theorem dedup_of_fresh (seen : Seen) : ∀ ds : List Delivery, (∀ d ∈ ds, d.token ∉ seen) →
    (ds.map Delivery.token).Nodup → (dedup seen ds).1 = ds
  | [], _, _ => rfl
  | d :: ds, hf, hn => by
    simp only [dedup, if_neg (hf d List.mem_cons_self)]
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    congr 1
    refine dedup_of_fresh _ ds (fun d' hd' => ?_) hn.2
    simp only [List.mem_cons, not_or]
    exact ⟨fun e => hn.1 ⟨d', hd', e⟩, hf d' (List.mem_cons_of_mem d hd')⟩

/-- The identities remembered after a tick: the ones seen before and the
    ones of every arrival. -/
theorem mem_dedup_seen (seen : Seen) : ∀ (ds : List Delivery) (x : Nat),
    x ∈ (dedup seen ds).2 ↔ x ∈ seen ∨ ∃ d ∈ ds, d.token = x
  | [], x => by simp [dedup]
  | d :: ds, x => by
    simp only [dedup]
    split
    · rename_i hin
      rw [mem_dedup_seen seen ds x]
      constructor
      · rintro (h | ⟨d', hd', e⟩)
        · exact Or.inl h
        · exact Or.inr ⟨d', List.mem_cons_of_mem d hd', e⟩
      · rintro (h | ⟨d', hd', e⟩)
        · exact Or.inl h
        · rcases List.mem_cons.mp hd' with rfl | hd'
          · exact Or.inl (e ▸ hin)
          · exact Or.inr ⟨d', hd', e⟩
    · rw [mem_dedup_seen (d.token :: seen) ds x]
      simp only [List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨d', hd', e⟩)
        · exact Or.inr ⟨d, Or.inl rfl, h.symm⟩
        · exact Or.inl h
        · exact Or.inr ⟨d', Or.inr hd', e⟩
      · rintro (h | ⟨d', (rfl | hd'), e⟩)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl e.symm)
        · exact Or.inr ⟨d', hd', e⟩

/-- **A retry is erased**: a delivery whose identity was seen, or was
    delivered earlier in the same tick, changes neither the kept
    deliveries nor the remembered identities. -/
theorem dedup_retry (seen : Seen) (d : Delivery) : ∀ (l₁ l₂ : List Delivery),
    (d.token ∈ seen ∨ ∃ d' ∈ l₁, d'.token = d.token) →
    dedup seen (l₁ ++ d :: l₂) = dedup seen (l₁ ++ l₂)
  | [], l₂, h => by
    simp only [List.nil_append]
    rcases h with h | ⟨_, h, _⟩
    · simp [dedup, h]
    · exact absurd h (List.not_mem_nil)
  | d' :: l₁, l₂, h => by
    simp only [List.cons_append, dedup]
    split
    · rename_i hin
      refine dedup_retry seen d l₁ l₂ ?_
      rcases h with h | ⟨d'', hd'', e⟩
      · exact Or.inl h
      · rcases List.mem_cons.mp hd'' with rfl | hd''
        · exact Or.inl (e ▸ hin)
        · exact Or.inr ⟨d'', hd'', e⟩
    · have : dedup (d'.token :: seen) (l₁ ++ d :: l₂) = dedup (d'.token :: seen) (l₁ ++ l₂) := by
        refine dedup_retry (d'.token :: seen) d l₁ l₂ ?_
        rcases h with h | ⟨d'', hd'', e⟩
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.mp hd'' with rfl | hd''
          · exact Or.inl (e ▸ List.mem_cons_self)
          · exact Or.inr ⟨d'', hd'', e⟩
      simp only [this]

/-! ## The bound and the flag -/

theorem provide_length_le (C : Contract) (seen : Seen) (ds : List Delivery) :
    (provide C seen ds).1.items.length ≤ C.cap := by
  simp only [provide, List.length_take]; exact Nat.min_le_left _ _

theorem provide_overflow_iff (C : Contract) (seen : Seen) (ds : List Delivery) :
    (provide C seen ds).1.overflow = true ↔ C.cap < (dedup seen ds).1.length := by
  simp [provide]

/-- **Without overflow nothing is dropped**: the batch is every fresh
    payload, in arrival order. -/
theorem provide_items_of_no_overflow (C : Contract) (seen : Seen) (ds : List Delivery)
    (h : (provide C seen ds).1.overflow = false) :
    (provide C seen ds).1.items = (dedup seen ds).1.map Delivery.payload := by
  simp only [provide, decide_eq_false_iff_not, Nat.not_lt] at h ⊢
  exact List.take_of_length_le (by simpa using h)

/-- The batch is a subsequence of the arrivals' payloads. -/
theorem provide_items_sublist (C : Contract) (seen : Seen) (ds : List Delivery) :
    (provide C seen ds).1.items.Sublist (ds.map Delivery.payload) :=
  (List.take_sublist _ _).trans ((dedup_sublist seen ds).map Delivery.payload)

theorem batch_length_le (C : Contract) (ds : Nat → List Delivery) (t : Nat) : (batch C ds t).items.length ≤ C.cap := by
  cases t <;> exact provide_length_le ..

/-! ## Retries across the stream -/

/-- An identity is remembered after tick `t` iff some arrival up to `t`
    carried it. -/
theorem mem_seenAfter (C : Contract) (ds : Nat → List Delivery) :
    ∀ t x, x ∈ seenAfter C ds t ↔ ∃ t' ≤ t, ∃ d ∈ ds t', d.token = x
  | 0, x => by
    simp only [seenAfter, run, provide]
    rw [mem_dedup_seen]
    simp
  | t + 1, x => by
    simp only [seenAfter, run, provide]
    rw [mem_dedup_seen]
    constructor
    · rintro (h | ⟨d, hd, e⟩)
      · obtain ⟨t', ht', d, hd, e⟩ := (mem_seenAfter C ds t x).mp h
        exact ⟨t', Nat.le_succ_of_le ht', d, hd, e⟩
      · exact ⟨t + 1, Nat.le_refl _, d, hd, e⟩
    · rintro ⟨t', ht', d, hd, e⟩
      rcases Nat.lt_or_eq_of_le ht' with hlt | rfl
      · exact Or.inl ((mem_seenAfter C ds t x).mpr ⟨t', Nat.le_of_lt_succ hlt, d, hd, e⟩)
      · exact Or.inr ⟨d, hd, e⟩

/-- A delivery stream with a **retransmission** inserted at tick `t`: the
    same deliveries, plus one whose identity an earlier delivery carried
    (at an earlier tick, or earlier in the same tick). -/
structure Retry (ds ds' : Nat → List Delivery) (t : Nat) (d : Delivery) (l₁ l₂ : List Delivery) : Prop where
  at_t : ds t = l₁ ++ l₂
  at_t' : ds' t = l₁ ++ d :: l₂
  other : ∀ u, u ≠ t → ds' u = ds u
  earlier : (∃ t' < t, ∃ d' ∈ ds t', d'.token = d.token) ∨ ∃ d' ∈ l₁, d'.token = d.token

/-- **`run_retry`**: a retransmission changes no batch and no state, at
    any tick. -/
theorem run_retry (C : Contract) {ds ds' : Nat → List Delivery} {t : Nat} {d : Delivery} {l₁ l₂ : List Delivery}
    (h : Retry ds ds' t d l₁ l₂) : ∀ u, run C ds' u = run C ds u := by
  intro u
  induction u with
  | zero =>
    simp only [run]
    by_cases h0 : 0 = t
    · subst h0
      rw [h.at_t', h.at_t]
      simp only [provide]
      have := dedup_retry [] d l₁ l₂ (by
        rcases h.earlier with ⟨t', ht', _⟩ | h'
        · exact absurd ht' (Nat.not_lt_zero _)
        · exact Or.inr h')
      rw [this]
    · rw [h.other 0 h0]
  | succ u ih =>
    simp only [run, ih]
    by_cases hu : u + 1 = t
    · subst hu
      rw [h.at_t', h.at_t]
      simp only [provide]
      have hseen : d.token ∈ (run C ds u).2 ∨ ∃ d' ∈ l₁, d'.token = d.token := by
        rcases h.earlier with ⟨t', ht', d', hd', e⟩ | h'
        · exact Or.inl ((mem_seenAfter C ds u d.token).mpr ⟨t', Nat.le_of_lt_succ ht', d', hd', e⟩)
        · exact Or.inr h'
      rw [dedup_retry _ d l₁ l₂ hseen]
    · rw [h.other (u + 1) hu]

theorem batch_retry (C : Contract) {ds ds' : Nat → List Delivery} {t : Nat} {d : Delivery} {l₁ l₂ : List Delivery}
    (h : Retry ds ds' t d l₁ l₂) : ∀ u, batch C ds' u = batch C ds u :=
  fun u => by simp [batch, run_retry C h u]

/-! ## Several raw sources -/

/-- One explicit, deterministic merge: source order, each source's
    arrivals in their order.  A policy the provider commits to, not a
    physical fact. -/
def mergeBySource (ls : List (List Delivery)) : List Delivery := ls.flatten

/-- A merge is an *interleaving* of per-source lists when each source's
    subsequence is that source's list. -/
def Interleaving (ls : List (List Delivery)) (m : List Delivery) : Prop :=
  ∀ i (hi : i < ls.length), m.filter (fun d => d.src = i) = ls[i]

/-- **Per-source reading is merge-insensitive**: two interleavings of the
    same per-source lists agree on every source's subsequence — a design
    that reads each source separately cannot tell them apart; only a
    design that reads the merged order depends on the policy. -/
theorem perSource_of_interleaving {ls : List (List Delivery)} {m₁ m₂ : List Delivery}
    (h₁ : Interleaving ls m₁) (h₂ : Interleaving ls m₂) (i : Nat) (hi : i < ls.length) :
    m₁.filter (fun d => d.src = i) = m₂.filter (fun d => d.src = i) := by
  rw [h₁ i hi, h₂ i hi]

theorem mergeBySource_interleaving_aux (ls : List (List Delivery)) :
    ∀ (off : Nat), (∀ i (hi : i < ls.length), ∀ d ∈ ls[i], d.src = off + i) →
    ∀ i (hi : i < ls.length), (ls.flatten).filter (fun d => d.src = off + i) = ls[i] := by
  induction ls with
  | nil => intro off _ i hi; exact absurd hi (Nat.not_lt_zero _)
  | cons l ls ih =>
    intro off htag i hi
    simp only [List.flatten_cons, List.filter_append]
    cases i with
    | zero =>
      have h0 : l.filter (fun d => d.src = off + 0) = l :=
        List.filter_eq_self.mpr (fun d hd => by
          have := htag 0 (Nat.succ_pos _) d (by simpa using hd)
          simp only [decide_eq_true_eq]; omega)
      have hrest : ls.flatten.filter (fun d => d.src = off + 0) = [] := by
        apply BDL.Validation.Capacity.filter_eq_nil_of
        intro d hd
        obtain ⟨l', hl', hd'⟩ := List.mem_flatten.mp hd
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl'
        have := htag (j + 1) (by simpa using Nat.succ_lt_succ hj) d (by simpa using hd')
        simp only [decide_eq_false_iff_not]; omega
      rw [h0, hrest, List.append_nil]; rfl
    | succ i =>
      have h0 : l.filter (fun d => d.src = off + (i + 1)) = [] :=
        BDL.Validation.Capacity.filter_eq_nil_of _ _ (fun d hd => by
          have := htag 0 (Nat.succ_pos _) d (by simpa using hd)
          simp only [decide_eq_false_iff_not]; omega)
      rw [h0, List.nil_append]
      have := ih (off + 1) (fun j hj d hd => by
        have := htag (j + 1) (by simpa using Nat.succ_lt_succ hj) d (by simpa using hd); omega)
        i (Nat.lt_of_succ_lt_succ hi)
      have e : off + (i + 1) = off + 1 + i := by omega
      rw [e]; exact this

/-- Source order is an interleaving when each list is tagged with its
    index. -/
theorem mergeBySource_interleaving (ls : List (List Delivery))
    (htag : ∀ i (hi : i < ls.length), ∀ d ∈ ls[i], d.src = i) : Interleaving ls (mergeBySource ls) := by
  intro i hi
  have := mergeBySource_interleaving_aux ls 0 (fun i hi d hd => by simpa using htag i hi d hd) i hi
  unfold mergeBySource
  simp only [Nat.zero_add] at this
  exact this

/-! ## Composition with Phase 13 -/

/-- The batch's raw type. -/
def batchTy (τ : Ty) : Ty := .prod (.list τ) .bool

/-- The batch channel: the items. -/
def chItems (τ : Ty) (hs : τ.SemFree) (hd : τ.Data) : Channel (batchTy τ) where
  rep := .list τ
  tr := .lam (batchTy τ) (.app (.prim (.fst (.list τ) .bool)) (.var 0))
  transfer := fun v => match v with | .pair a _ => a | v => v
  rep_semFree := hs
  rep_data := hd
  tr_pure := by simp [Expr.Pure]
  computes := by
    rintro v ⟨a, b, rfl, _, _⟩
    have h := Ev.appClo (Δ := DeclEnv.empty) (I := fun _ _ => Value.pair a b) (t := 0) (ρ := [])
      (f := .lam (batchTy τ) (.app (.prim (.fst (.list τ) .bool)) (.var 0))) (a := .declRef ⟨0⟩) (ρ' := [])
      (body := _) (va := .pair a b) .lam (.refInput rfl) (Ev.appPrim .prim (.var rfl))
    unfold Transduces
    simpa [applyPrim, Prim.arity, Prim.compute] using h

/-- The overflow channel: the flag. -/
def chOverflow (τ : Ty) : Channel (batchTy τ) where
  rep := .bool
  tr := .lam (batchTy τ) (.app (.prim (.snd (.list τ) .bool)) (.var 0))
  transfer := fun v => match v with | .pair _ b => b | v => v
  rep_semFree := trivial
  rep_data := trivial
  tr_pure := by simp [Expr.Pure]
  computes := by
    rintro v ⟨a, b, rfl, _, _⟩
    have h := Ev.appClo (Δ := DeclEnv.empty) (I := fun _ _ => Value.pair a b) (t := 0) (ρ := [])
      (f := .lam (batchTy τ) (.app (.prim (.snd (.list τ) .bool)) (.var 0))) (a := .declRef ⟨0⟩) (ρ' := [])
      (body := _) (va := .pair a b) .lam (.refInput rfl) (Ev.appPrim .prim (.var rfl))
    unfold Transduces
    simpa [applyPrim, Prim.arity, Prim.compute] using h

/-- **The batch provision**: one raw declaration `r` read in `clock`,
    the items to the Source `s`, the flag to the Source `sOver` —
    Phase 13's shared raw reading with two targets. -/
def batchProvision (τ : Ty) (hs : τ.SemFree) (hd : τ.Data) (r s sOver : DeclId) (clock : Option ClockId) :
    Provision (batchTy τ) :=
  Provision.ofList r clock [(s, chItems τ hs hd), (sOver, chOverflow τ)]

/-- A typed delivery stream: every payload is a `τ`. -/
def Typed (τ : Ty) (ds : Nat → List Delivery) : Prop := ∀ t, ∀ d ∈ ds t, TyVal τ d.payload

theorem batch_items_typed {τ : Ty} {ds : Nat → List Delivery} (hT : Typed τ ds) (C : Contract) (t : Nat) :
    ∀ w ∈ (batch C ds t).items, TyVal τ w := by
  intro w hw
  have hsub : (batch C ds t).items.Sublist ((ds t).map Delivery.payload) := by
    cases t <;> exact provide_items_sublist ..
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (hsub.subset hw)
  exact hT t d hd

theorem batch_value_tyVal {τ : Ty} {ds : Nat → List Delivery} (hT : Typed τ ds) (C : Contract) (t : Nat) :
    TyVal (batchTy τ) (batch C ds t).value :=
  ⟨_, _, rfl, ⟨_, rfl, batch_items_typed hT C t⟩, ⟨_, rfl⟩⟩

/-- The provider's raw input is a Phase-13 raw input when the payloads are
    typed and the base input is closure-free. -/
theorem rawInput_rawInput {τ : Ty} {ds : Nat → List Delivery} (hT : Typed τ ds) (hs : τ.SemFree) (hd : τ.Data)
    (C : Contract) {r s sOver : DeclId} {clock : Option ClockId} {base : Input} (hb : ∀ d t, (base d t).NoClo) :
    RawInput (batchProvision τ hs hd r s sOver clock) (rawInput C ds r base) := by
  refine ⟨fun t => ?_, fun d t => ?_⟩
  · simp only [rawInput, batchProvision, Provision.ofList, if_true]
    exact batch_value_tyVal hT C t
  · unfold rawInput
    split
    · exact TyVal.noClo (τ := batchTy τ) ⟨hd, trivial⟩ (batch_value_tyVal hT C t)
    · exact hb d t

/-! ## Replacement -/

/-- Two providers over one design deliver **the same batches** when their
    batch streams coincide. -/
def SameBatches (C₁ : Contract) (ds₁ : Nat → List Delivery) (C₂ : Contract) (ds₂ : Nat → List Delivery) : Prop :=
  ∀ t, batch C₁ ds₁ t = batch C₂ ds₂ t

/-- **`sameBatches_sameTrace`**: equal batch streams, one base input off
    the raw declarations, give Phase 16's same semantic trace — for two
    batch provisions of one design with distinct raw declarations and the
    same targets. -/
theorem sameBatches_sameTrace {τ : Ty} (hsf : τ.SemFree) (hdt : τ.Data) {C₁ C₂ : Contract}
    {ds₁ ds₂ : Nat → List Delivery} (hsame : SameBatches C₁ ds₁ C₂ ds₂) {Δ : DeclEnv} {r₁ r₂ s sOver : DeclId}
    {clock₁ clock₂ : Option ClockId} {base : Input} (hs : s ≠ r₁ ∧ s ≠ r₂) (hso : sOver ≠ r₁ ∧ sOver ≠ r₂) :
    SameTrace Δ (batchProvision τ hsf hdt r₁ s sOver clock₁) (batchProvision τ hsf hdt r₂ s sOver clock₂)
      (rawInput C₁ ds₁ r₁ base) (rawInput C₂ ds₂ r₂ base) := by
  intro d t h₁ h₂
  simp only [batchProvision, Provision.ofList] at h₁ h₂ ⊢
  simp only [induced, rawInput]
  by_cases hd : d = s
  · subst hd
    simp [hs.1, hs.2, hsame t]
  · by_cases hd' : d = sOver
    · subst hd'
      simp [hso.1, hso.2, hsame t]
    · simp [h₁, h₂, Ne.symm hd, Ne.symm hd']

/-- **`retry_invisible`**: a transport retransmission inserted anywhere in
    the delivery stream leaves every batch — hence, by
    `two_providers_same_behavior`, every behaviour observation — unchanged. -/
theorem retry_invisible {τ : Ty} (hsf : τ.SemFree) (hdt : τ.Data) (C : Contract) {ds ds' : Nat → List Delivery}
    {t : Nat} {d : Delivery} {l₁ l₂ : List Delivery} (h : Retry ds ds' t d l₁ l₂) {Δ : DeclEnv} {r s sOver : DeclId}
    {clock : Option ClockId} {base : Input} (hs : s ≠ r) (hso : sOver ≠ r) :
    SameTrace Δ (batchProvision τ hsf hdt r s sOver clock) (batchProvision τ hsf hdt r s sOver clock)
      (rawInput C ds' r base) (rawInput C ds r base) :=
  sameBatches_sameTrace hsf hdt (batch_retry C h) ⟨hs, hs⟩ ⟨hso, hso⟩

end BDL.Provider
