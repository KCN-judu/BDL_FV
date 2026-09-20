---
kind: report
phase: 17
area: surface
date: 2026-09-20
status: current
---

# Phase 17 — The provider's occurrence contract and the occurrence-preserving output window

Question (the two boundaries Phase 16 left below its state encodings — FVI-0029
and FVI-0024): what must a provider promise about the raw reading it delivers —
which deliveries are one semantic occurrence, in what order, deduplicated how,
bounded how — and how does a logical output whose every value matters reach a
device that activates more slowly than the output's clock, without a message
primitive? Answer: **both are constructions over the existing kernel, proved.**
The provider keeps the transport identities it has delivered and delivers, per
tick, the first `cap` fresh payloads in arrival order with an observable
overflow flag; a retransmission is erased and a repeated command with a fresh
identity is not (`run_retry`, `dedup_of_fresh`); the raw reading is
`(list raw, bool)` — Phase 13's provision with two channels; a scalar Source is
the batch sampled. The occurrence-preserving realization is Phase 9a's window
with Phase 14's encoder declaration as its source, transported into the device
domain, driving a `list raw` sink: the sink carries exactly the raw commands
specified at the output-clock activations since the device's previous
activation, in order and with multiplicity (`lowerWindow_correspondence`), the
behaviour is unchanged (`lowerWindow_transparent`), the batch is bounded by the
Phase-9a capacity obligation (`lowerWindow_bounded`), and the lowered design is
well formed, causal, well clocked, drive-well-formed and single-driver. Nothing
entered `Core`; no `Event`, `Message`, `Stream`, queue, batch or transaction
primitive was needed. Files: `BDL/Surface/Provider.lean`,
`BDL/Surface/OutputWindow.lean`, `BDL/Surface/Buffer.lean` (generalised),
`BDL/Experiments/ProviderExamples.lean`,
`BDL/Experiments/OutputWindowExamples.lean`; note:
[the-provider-contract-and-the-output-window](../notes/the-provider-contract-and-the-output-window.md).

## 17.1 Part A — the provider's occurrence contract

The provider sits below Phase 13's raw reading `r : () -> raw`: what the
transport delivered since the previous tick becomes the one raw value the Source
reads. `BDL/Surface/Provider.lean`:

- **`Delivery ⟨src, token, payload⟩`** — a raw source index, a transport
  identity (a sequence number, a frame id, a retry token — the provider's
  knowledge, never the design's), the payload.
- **`dedup seen ds`** — drop the deliveries whose identity was already
  delivered, keep the rest in arrival order, remember the identities; `Seen` is
  adapter state (as Phase 15's `Line` is).
- **`Contract ⟨cap⟩`**, **`provide C seen ds`** — the first `cap` fresh payloads
  and `overflow := cap < #fresh`; **`Batch.value`** is the raw reading
  `(list raw, bool)`; **`run`/`batch`/`seenAfter`** thread the state over a
  delivery stream; **`rawInput C ds r base`** is the induced raw input.
- **`Batch.latest`** — a scalar Source is the batch sampled: the last item or
  the held value.
- **`mergeBySource`**, **`Interleaving`** — an explicit, deterministic merge of
  several raw sources, and the class of merges that keep each source's order.
- **`batchTy τ`, `chItems`, `chOverflow`, `batchProvision`** — the batch as
  Phase 13's shared raw reading with two channels; **`Typed`**,
  **`SameBatches`**.

| Claim                                                                                                                                     | Theorem                                                                                        | Hypotheses                                  |
| ----------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------- | ------------------------------------------- |
| the kept deliveries are a subsequence of the arrivals: order and multiplicity of what is kept are the transport's                         | `dedup_sublist`, `provide_items_sublist`                                                       | —                                           |
| **distinct identities are all delivered** — two equal payloads with distinct identities are two occurrences; nothing is merged by payload | `dedup_of_fresh`                                                                               | identities fresh and pairwise distinct      |
| the identities remembered are exactly those of every arrival so far                                                                       | `mem_dedup_seen`, `mem_seenAfter`                                                              | —                                           |
| **a retry is erased**: a delivery whose identity was delivered (earlier, or earlier in the tick) changes nothing                          | `dedup_retry`                                                                                  | the identity seen or earlier in the tick    |
| the batch has at most `cap` items; the flag is exact; without overflow nothing is dropped                                                 | `provide_length_le`, `batch_length_le`, `provide_overflow_iff`, `provide_items_of_no_overflow` | —                                           |
| **a retransmission inserted anywhere in the stream changes no batch and no state, at any tick**                                           | `run_retry`, `batch_retry`                                                                     | `Retry ds ds' t d l₁ l₂`                    |
| source order is an interleaving; two interleavings agree per source — a per-source reading is merge-insensitive                           | `mergeBySource_interleaving`, `perSource_of_interleaving`                                      | sources tagged by index                     |
| the provider's raw input is a Phase-13 raw input                                                                                          | `batch_value_tyVal`, `rawInput_rawInput`                                                       | typed payloads, closure-free base           |
| equal batch streams are Phase 16's same semantic trace, hence the same behaviour                                                          | `sameBatches_sameTrace` (+ `two_providers_same_behavior`)                                      | distinct raw declarations, the same targets |
| **a retransmission is invisible to the behaviour**                                                                                        | `retry_invisible`                                                                              | `Retry`                                     |

**The contract, stated.** (1) One semantic occurrence per _fresh transport
identity_ — never per payload; `Move(+10); Move(+10)` with two identities is
two. (2) Arrival order within a raw source. (3) Retransmissions are erased by
identity, below the boundary, with adapter state. (4) At most `cap` per tick,
and the cut is a value the design reads (`overflow`), never a silent drop; which
`cap` suffices is a deployment assumption on the physical arrival rate, the
Phase-9a capacity question. (5) Several raw sources are several raw readings —
one provision each — unless the provider commits to an explicit deterministic
merge; no physical total order is assumed, and a design that reads per source is
insensitive to the merge.

## 17.2 Part B — the occurrence-preserving realization

`BDL/Surface/OutputWindow.lean`. Phase 15's `lowerSync` samples the last
command; for an output whose every value is an occurrence a device must not
miss, the crossing is the Phase-9a window:

```text
e      @c  := encode (rep d)                       -- Phase 14
log    @c  := cons e (delay nil log)
logD   @dc := sync c nil log
seen   @dc := length logD
cursor @dc := delay 0 seen
window @dc := reverse (take (seen − cursor) logD)  →  p : list raw @dc
```

`lowerWindowΔ Δ R spec ids` (six updates over `lowerΔ`), `lowerWindowΩ` (the
sink at `list raw` in `dc`), `lowerWindowβ` (the window drives the sink),
`lowerWindowΚ`; `Fresh Δ R ids` (six distinct fresh identities); `RepTrace` (the
typed representation trace of the logical output — unique under `SingleDriver`,
existing by totality). `Surface/Buffer.lean` was generalised so that the
window's source may be any declaration with a known value function
(`RealizedFrom`, `log_at_from` … `buffer_window_correspondence_from`); the
input-source theorems are the instances.

| Claim                                                                                                                                                                                                       | Theorem                                                                                   | Hypotheses                                               |
| ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------- | -------------------------------------------------------- |
| updating an environment at an unmentioned identity changes no term avoiding it — the generic step of every lowering's transparency                                                                          | `update_transparent`, `NoMention.update`                                                  | `NoMention`, inputs avoiding                             |
| **the behaviour is literally unchanged** off the six fresh identities; every abstract declaration evaluates alike                                                                                           | `lowerWindow_transparent`, `lowerWindow_decl_transparent`                                 | `Fresh`, `WF`, `NoMention` ×6, inputs avoiding ×6        |
| the encoder carries the transfer of the trace at every output tick                                                                                                                                          | `lowerWindow_encoder_at`, `encoder_value_in`                                              | + `SingleDriver`, `RepTrace`                             |
| **correspondence**: at every tick, in the device domain, the sink carries the raw commands specified at the output-clock activations since the device's previous activation, in order and with multiplicity | `lowerWindow_correspondence`, `lowerWindow_batch_rawCommands`, `lowerWindow_batch_unique` | + `DriveWF` for uniqueness                               |
| order and multiplicity (Phase 9a's, at the sink)                                                                                                                                                            | `lowerWindow_order_multiplicity`                                                          | —                                                        |
| **bounded** by Phase 9a's capacity obligation on the crossing `spec.clock → dc`                                                                                                                             | `lowerWindow_bounded`                                                                     | `CapacitySufficient S c dc cap T`, `t ≤ T`               |
| refinement; the window's binding is Phase 6's first binding; the new edge and every old one well formed                                                                                                     | `lowerWindow_envRefines`, `lowerWindow_singleDriver`, `lowerWindow_driveWF`               | `Fresh`, `WF`, `DriveWF`, `SingleDriver`                 |
| well clocked (encoder and log in the output's clock, the four others in the device domain); causal (edges `e→d`, `log→e`, `seen→logD`, `window→…`; none for the transports); globally well formed           | `lowerWindow_wellClocked`, `lowerWindow_causal`, `lowerWindow_wf`                         | + `WellClocked`, `Causal`, `GlobalWF`, monotone evidence |
| the adapter's batch is a list of Phase 15's operations; the line after a batch is its last accepted item                                                                                                    | `batchOps_length`, `lineAfterBatch_accepted`, `lineAfterBatch_refused`                    | —                                                        |
| **two window realizations of one output** carry batches that are pointwise the two transfers of one value list                                                                                              | `paired_batches_of_one_window`                                                            | `SingleDriver`, `R₁.o = R₂.o`, two traces                |

**State vs occurrence.** The distinction is the sink's type — the device's
consumption contract: a device that consumes `raw` is lowered by `lowerSync`
(latest value), one that consumes `list raw` by `lowerWindow` (every value). The
logical output is one value stream in both; no flag is added to it. A
batch-valued output (each value itself a list of occurrences) is the same
construction with `flattenF` at the device. **Capacity** stays Phase 9a's:
decided on the schedules (`CapacitySufficient`), a deployment infeasibility when
it fails, never a type. **The device clock** is a BDL `ClockId` the deployment
chooses (FVD-0141); carriers stay configuration. **The transaction case** under
batching: one output, one pair command per item, or two window realizations
whose batches agree pointwise; the prepare/prepare/commit order of each item is
the backend's order within one batch (FVD-0148 stands).

## 17.3 Executed

`ProviderExamples.lean` — `exA_occurrences` (one; two equal payloads, two
identities; a retransmission at a later tick: none), `exB_order` (`[A, B]`,
`[B, A]`; a retried `A` between `A` and `B` does not appear),
`exB_retry_is_Retry` / `exB_all_ticks` (the stream-level theorem instantiated),
`exC_merge` (source order; the other interleaving; equal per-source
subsequences), `exD_bound` (`cap = 2` cuts and flags, `cap = 3` delivers),
`exE_ingress` (host deliveries into Phase 16's queue design through
`batchProvision`: `A` then `B`, desired 10 then 40; the retry stream gives the
same queue and desired at every tick shown; `submitOver` false), `exE_theorem`
(`two_providers_same_behavior` through `retry_invisible` on the queue design),
`exE_overflow` (three jobs in one tick under `cap = 2`: two queued, the flag
raised in the design), `exF_feedback` (two motors' feedback from two raw
readings sampled by `chLatest` into `fb2`, `fb3 : opt Sample`: two samples in
one tick give the last, a retransmitted sample is `none`, silence is `none` —
what `age` counts), `exG_two_axes` (the Phase-16 motion state as a behaviour
component instantiated on two axes in one system: axis 2 completes, axis 3
latches its fault; disjoint state).

`OutputWindowExamples.lean` — `exA_window_vs_sample` (device on even ticks: the
sampled lowering carries `104` at tick 2, the window `[102, 104]`; `[107, 109]`
at tick 4), `exB_multiplicity_order` (a repeated dial value twice, in order),
`exC_capacity` (period 2 needs `cap = 2`; period 3 with `cap = 2` refused;
decided), `exC_bounded`, `exD_batch` (`[102, 306]` under `duty8` is
`[set 102, refused]`, the line ends at 102; under `clamp8` at 255),
`exE_paired`/`exE_paired_theorem`, `exF_correspondence` and `exF_structure` (the
theorems instantiated on the PWM realization), `exF_transparent`.

116 theorem-like declarations added (22 + 53 + 6 + 19 + 16); every one on
`propext`/`Quot.sound` (`List.filter_eq_nil_iff`, which is classical, was
replaced by Phase 9a's constructive `filter_eq_nil_of`); no `sorry`. The whole
development: 1 479 across 66 files; `lake build` 69 jobs, clean, no warnings.

## 17.4 Models tried

| Model                                                                             | Verdict                                                                                                                                                                                                     |
| --------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| deduplication by payload                                                          | rejected: `Move(+10); Move(+10)` is two commands (`dedup_of_fresh`, `exA`); identity is the transport's, and only the transport can say                                                                     |
| the transport identity in the Source's type                                       | rejected (FVD-0144 stands): the batch carries payloads only; `retry_invisible`                                                                                                                              |
| a silent drop at the bound                                                        | rejected: the flag is a raw value the design reads (`exE_overflow`); a bound the world exceeds is a deployment assumption that failed, and the design can say so                                            |
| an implicit total order across raw sources                                        | rejected: no physical fact supplies one; `mergeBySource` is one explicit policy, per-source reading is insensitive (`perSource_of_interleaving`), and the recommended shape is one provision per raw source |
| a second input semantics for batches                                              | rejected: the batch is Phase 13's shared raw reading with two channels (`batchProvision`); the scalar Source is `Batch.latest` (`chLatest`, `exF`)                                                          |
| a weaker "same trace" for batches                                                 | not needed: `SameBatches` implies `SameTrace` (`sameBatches_sameTrace`); nothing was weakened                                                                                                               |
| an `Event`/`Stream` type or a queue primitive for the output crossing             | rejected: the window is Phase 9a's five declarations over the encoder (`lowerWindow_correspondence`)                                                                                                        |
| an "event mode" flag on the logical output                                        | rejected: the sink's type says which lowering the device takes; the output is one value stream (`exA_window_vs_sample` shows both lowerings of one output)                                                  |
| a batch adapter primitive                                                         | rejected: `batchOps` is `List Op`, `lineAfterBatch` a fold (`exD_batch`)                                                                                                                                    |
| a transaction object for the paired axis under batching                           | rejected: `paired_batches_of_one_window` (`exE_paired`)                                                                                                                                                     |
| the window's source generalised in `Buffer.lean` by a second copy of the theorems | rejected: the lemmas were generalised in place over any value function (`_from`) and the input case kept as an instance — no duplicate                                                                      |

## 17.5 Claim audit

- _proved_: §17.1 and §17.2.
- _executed_: §17.3, including the reusable `MotionController` witness on two
  axes.
- _definitional_: the contract's clauses (1)–(3) are `provide`'s definition; the
  state/occurrence distinction is the sink's type.
- _design decision_: source order as the explicit merge (FVD-0151); the batch as
  `(list raw, bool)` (FVD-0149).
- _not established_: which `cap` a physical arrival rate needs (a deployment
  assumption, decided like Phase 9a's capacity on schedules); a Source-side
  device clock and a stateful transducer (FVI-0020); a device that acknowledges
  and the initial representation of a slower device (FVI-0024, narrowed);
  anything below the raw reading or the adapter operation. The production slice
  that consumes this (Part C) was found **in flight and uncommitted** in the
  production working tree at audit time — a `bdl-catalogue` crate,
  `DeviceKind::DigitalInput`, `DeviceBinding.source` / `provider`,
  `InputProfileId` — and is not cited as a fact of any commit.

## 17.6 Verdicts

| Construct                                                              | Verdict                                                                   | Decision           |
| ---------------------------------------------------------------------- | ------------------------------------------------------------------------- | ------------------ |
| the provider's occurrence contract (`dedup`, `provide`, `Batch.value`) | KEEP IN DEPLOYMENT (the adapter's); the raw reading is `(list raw, bool)` | FVD-0149           |
| deduplication by transport identity; a retransmission erased           | KEEP IN DEPLOYMENT — below the boundary, with adapter state               | FVD-0150           |
| deduplication by payload; an implicit cross-source order               | REMOVE                                                                    | FVD-0150, FVD-0151 |
| several raw sources                                                    | KEEP AS SEVERAL PROVISIONS; a merge is an explicit policy                 | FVD-0151           |
| the occurrence-preserving realization (`lowerWindow`)                  | KEEP IN DEPLOYMENT CONSTRUCTION — the sink's type selects it              | FVD-0152           |
| an "event mode" on the logical output; an `Event`/`Stream` type        | REMOVE                                                                    | FVD-0152           |
| the adapter's batch (`batchOps`, `lineAfterBatch`)                     | KEEP IN MACHINE/BACKEND — `List Op`, a fold                               | FVD-0153           |
| a batch or transaction primitive                                       | REMOVE                                                                    | FVD-0153           |
