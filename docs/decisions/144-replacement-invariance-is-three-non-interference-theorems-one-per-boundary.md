---
id: FVD-0144
legacy-id:
status: accepted
date: 2026-09-20
phase: 16
area: surface
supersedes: []
superseded-by: []
related: [FVD-0129, FVD-0131, FVD-0140, FVD-0143]
production: [ADR-0032/supports, ADR-0036/supports, ADR-0037/supports]
---

# FVD-0144: Replacement invariance is three non-interference theorems, one per boundary; the input side is `two_providers_same_behavior`

## Status

Accepted in Phase 16.

## Decision

The architectural test _if a carrier is replaced while the product-observable
semantic trace stays the same, behaviour stays the same_ is stated as three
theorems: Source side `two_providers_same_behavior` /
`two_providers_same_outputs` (`BDL/Surface/Assignment.lean`, new), output side
`two_realizations_same_behavior` (Phase 14), adapter side
`two_policies_same_commands` (Phase 15). "Same semantic trace" on the input side
is `SameTrace Δ P₁ P₂ I₁ I₂`: the induced inputs agree at every declaration
other than the two raw ones, at every global tick; the raw readings themselves
may carry any transport identity and need not share a type.

## Alternatives rejected

A single generic non-interference predicate over "deployment steps" (there is no
one type of step); agreement only at the reading domain's activations (a
refinement no case needed).

## Reason

`two_providers_same_behavior` is `provision_transparent` on each side and
`induced_congr`, which moves between the two induced inputs by two `input_congr`
steps, one per raw identity, using `induced_avoids` (the induced input is
closure-free off the raw declarations because a channel's transfer of a
closure-free raw value is pure). Executed: `exL_theorem`, `exL_executed` —
`(sequence number, batch)` framing and per-job `(frame id, job)` framing give
one queue.
