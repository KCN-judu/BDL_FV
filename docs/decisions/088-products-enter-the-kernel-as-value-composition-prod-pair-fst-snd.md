---
id: FVD-0088
legacy-id: D-88
status: accepted
date: 2026-09-17
phase: 9b
area: surface
supersedes: []
superseded-by: []
related: []
production: [ADR-0025/supports]
---

# FVD-0088: Products enter the kernel as value composition: `prod`, `pair`, `fst`, `snd`

## Status

Accepted in Phase 9b.

## Alternatives rejected

Church/function encodings (arrows are not data — `arrow_not_delayable`;
first-class use needs rank 2 — `church_fst_rank`); tuples as component
interfaces or output bundles (Phases 6, 8 unchanged).

## Reason

Paired state must be delayable (`pair_state_delayable`).
