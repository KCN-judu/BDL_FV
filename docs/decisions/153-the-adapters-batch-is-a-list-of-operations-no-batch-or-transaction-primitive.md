---
id: FVD-0153
legacy-id:
status: accepted
date: 2026-09-20
phase: 17
area: surface
supersedes: []
superseded-by: []
related: [FVD-0140, FVD-0148, FVD-0152]
production: [ISS-0017/bears-on, ADR-0037/supports]
---

# FVD-0153: The adapter's batch is a list of Phase 15's operations and the line after it a fold; no batch or transaction primitive

## Status

Accepted in Phase 17.

## Decision

A device that receives a `list raw` in one activation performs `batchOps P ws` —
each item read by the policy, in the batch's order, a `List Op` — and the line
after the batch is `lineAfterBatch P start ws`, the last accepted item or the
line before. Two window realizations of one output carry batches that are
pointwise the two transfers of one value (`paired_batches_of_one_window`); the
prepare/prepare/commit of a paired axis is the backend's order within one batch.

## Alternatives rejected

An `ApplyBatch` primitive; a transaction object for the paired axis under
batching.

## Reason

`batchOps_length`, `lineAfterBatch_accepted`, `lineAfterBatch_refused`,
`paired_batches_of_one_window` (`BDL/Surface/OutputWindow.lean`); executed
`exD_batch`, `exE_paired`, `exE_paired_theorem`.
