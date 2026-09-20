---
id: FVD-0149
legacy-id:
status: accepted
date: 2026-09-20
phase: 17
area: surface
supersedes: []
superseded-by: []
related: [FVD-0121, FVD-0125, FVD-0143, FVD-0086]
production: [ISS-0016/bears-on, ISS-0001/bears-on]
---

# FVD-0149: The provider's occurrence contract: one occurrence per fresh transport identity, arrival order, a bounded batch with an observable overflow flag; the raw reading is `(list raw, bool)` and a scalar Source is the batch sampled

## Status

Accepted in Phase 17.

## Decision

Below Phase 13's raw reading, the provider delivers per tick the batch
`provide C seen ds`: the first `C.cap` payloads of the deliveries whose
transport identity was not delivered before, in arrival order, and the flag
`cap < #fresh`. The Source reads `(list raw, bool)` through Phase 13's shared
raw reading with two channels (`batchProvision`: the items and the flag). A
scalar Source is the batch sampled — the last item or the held value
(`Batch.latest`, `chLatest`). Which `cap` suffices is a deployment assumption on
the physical arrival rate, decided as Phase 9a decides capacity.

## Alternatives rejected

A silent drop at the bound (only refusal preserves semantics, FVD-0086, and a
provider cannot refuse the world — it can say so); a second input semantics for
batches; an unbounded batch.

## Reason

`provide_length_le`, `provide_overflow_iff`, `provide_items_of_no_overflow`,
`provide_items_sublist`, `rawInput_rawInput`, `sameBatches_sameTrace`
(`BDL/Surface/Provider.lean`); executed `exD_bound`, `exE_ingress`,
`exE_overflow`, `exF_feedback`.
