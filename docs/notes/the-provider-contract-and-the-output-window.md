---
kind: note
phase: 17
area: surface
date: 2026-09-20
status: current
---

# The provider's occurrence contract and the occurrence-preserving output window

For production and for a reader who will not open the Lean: what a Source device
must promise about the reading it delivers, and how an output whose every value
matters reaches a slower device — both without a message primitive. It
summarises the
[Phase 17 report](../reports/phase-17-the-provider-occurrence-contract-and-the-output-window.md),
`BDL/Surface/Provider.lean`, `BDL/Surface/OutputWindow.lean` and the decisions
FVD-0149 … FVD-0153.

## 1. The two gaps

Phase 16 encoded every tested communication case as state and rested the
encodings on two things it did not state: what the raw reading of a Source
_means_ when several things arrived since the previous tick (FVI-0029), and how
a device that activates more slowly than an output's clock receives every
command rather than the last one (FVI-0024). Both are now constructions over the
existing kernel, proved; neither needed a primitive.

## 2. The provider's occurrence contract

Below the raw reading `r : () -> raw` sits the provider: the adapter's function
from what the transport delivered to the one value the Source reads. Its
contract, in five clauses:

1. **One semantic occurrence per fresh transport identity.** A delivery is a
   payload with an identity the transport owns — a sequence number, a frame id,
   a retry token. The provider remembers the identities it delivered and drops a
   delivery whose identity it has seen. A retransmission is nothing; two
   deliveries with distinct identities and equal payloads are two —
   `Move(+10); Move(+10)` is never merged by payload (`dedup_of_fresh`).
2. **Arrival order** within a raw source (`dedup_sublist`).
3. **Retransmissions are erased by identity**, below the boundary, with adapter
   state; a retransmission inserted anywhere in the delivery stream changes no
   batch at any tick (`run_retry`) and no behaviour (`retry_invisible`).
4. **A per-tick bound `cap`**, with the cut visible: the reading is
   `(list raw, bool)` — the first `cap` fresh payloads and an overflow flag the
   design can read (`provide`, `exE_overflow`). Never a silent drop. Which `cap`
   suffices is a deployment assumption on the physical arrival rate — Phase 9a's
   capacity question, not the language's.
5. **Several raw sources are several raw readings**, one provision each (Phase
   13). A provider that merges them commits to an explicit, deterministic policy
   (source order, `mergeBySource`); no physical total order is assumed, and a
   design that reads per source is insensitive to the policy
   (`perSource_of_interleaving`).

The contract composes with Phase 13 as it stands: the batch is a shared raw
reading with two channels, the items and the flag (`batchProvision`), so
`provision_transparent` and `two_providers_same_behavior` apply; equal batch
streams are the same semantic trace (`sameBatches_sameTrace`). A **scalar**
Source — a level, a sample — is the batch sampled: the last item or the held
value (`Batch.latest`, `chLatest`). The Phase-16 queue design fed by a host
through this provider, under a delivery stream with a retransmission, has the
same queue and desired position at every tick as without it (`exE_ingress`,
`exE_theorem`); two motors' feedback from two raw readings, sampled, gives the
motion state its `fb : opt Sample` — two samples in a tick give the last, a
retransmitted sample is `none`, silence is `none` (`exF_feedback`).

## 3. The occurrence-preserving output window

Phase 15's device-clock lowering samples: at a device activation the sink
carries the command specified at the last output-clock activation before it. For
a state-like output that is the meaning. For an output whose every value is an
occurrence, the crossing is Phase 9a's window over Phase 14's encoder:

```text
e      @c  := encode (rep d)
log    @c  := cons e (delay nil log)
logD   @dc := sync c nil log
seen   @dc := length logD
cursor @dc := delay 0 seen
window @dc := reverse (take (seen − cursor) logD)  →  p : list raw @dc
```

Proved (`OutputWindow.lean`): the behaviour is literally unchanged
(`lowerWindow_transparent`); at every device tick the sink carries exactly the
raw commands specified at the output-clock activations since the device's
previous activation, in order and with multiplicity
(`lowerWindow_correspondence`); the batch is bounded by the Phase-9a capacity
obligation on the crossing (`lowerWindow_bounded`); the lowered design refines
the abstract one and is well formed, causal, well clocked, drive-well-formed and
single-driver. Executed: with the device on even ticks, the sampled lowering
carries `104` at tick 2 where the window carries `[102, 104]`
(`exA_window_vs_sample`); a repeated value appears twice (`exB`); a period-3
device with `cap = 2` is refused (`exC_capacity`).

**State vs occurrence is the sink's type** — the device's consumption contract:
a device that consumes `raw` is lowered by `lowerSync`, one that consumes
`list raw` by `lowerWindow`. The logical output is one value stream in both
cases; no flag is added to it. **The adapter's batch** is a list of Phase 15's
operations (`batchOps`) and the line after it the last accepted item
(`lineAfterBatch`). **The paired axis** under batching: two window realizations
of one output carry batches that are pointwise the two transfers of one value
(`paired_batches_of_one_window`); prepare/prepare/commit is the backend's order
within one batch.

## 4. What is not established

Which `cap` a physical arrival rate needs (a deployment assumption); a
Source-side device clock and a stateful transducer (FVI-0020); a device that
acknowledges, and the initial representation of a slower device (FVI-0024,
narrowed); anything below the raw reading or the adapter operation (FVI-0023).

## 5. Production guidance

What exists at `aa6e7f4` (the last commit): no input profile; the adapters
refuse a design with a Source (`adapter.inputs_unbound`). What was found **in
flight and uncommitted** in the production working tree while this phase was
written: a `bdl-catalogue` crate, `DeviceKind::DigitalInput`,
`DeviceBinding.source` and `provider`, `InputProfileId` — the Source realization
slice, not yet a fact of any commit. What that slice should consume from this
phase (_design recommendation_):

1. **An input profile carries its delivery contract**: `sampled` (a scalar
   reading per tick — a level, an ADC count; the first slice) or `batch { cap }`
   (a `(list raw, bool)` reading). The transducer is typed `raw -> rep` under no
   grant, exactly as an encoder is.
2. **The adapter owns identities**: deduplication of transport retries by token,
   never by payload; for a sampled profile there is nothing to deduplicate — the
   level is read once per tick.
3. **The overflow flag is a value**, delivered beside the items, so the design
   can refuse or count; a bound the world exceeds is not a silent drop.
4. **Per-source provisions**: a design that must see several raw sources
   declares one Source per raw reading; a merged reading is a provider policy
   the profile states.
5. **Occurrence-preserving sinks**: a profile that consumes `list raw` selects
   the window lowering; its capacity is checked like a cross-domain window
   (ADR-0027's machinery on the output clock → device clock crossing).

Nothing here is implemented; the correspondence page records Phase 17 as _not
consumed_.
