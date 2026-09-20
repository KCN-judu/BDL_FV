---
id: FVD-0037
legacy-id: D-37
status: accepted
date: 2026-09-15
phase: 4
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0004/supports, ADR-0016/supports]
---

# FVD-0037: Causality replaces blanket acyclicity: `Causal` on `InstDependsOn`

## Status

Accepted in Phase 4.

## Alternatives rejected

Deleting `Unfolds.not_of_cyclic`; keeping structural acyclicity as the execution
criterion.

## Reason

`Unfolds` stays correct wherever it exists (`unfolds_preserves_eval` on wiring
designs) and is the delay-free special case (`Causal_iff_acyclic_of_delayFree`);
execution exists exactly on causal designs (`reactive_total`,
`Ev.not_of_strictCyclic`).

## Known gap

Lambda-guarded cycles are rejected conservatively.
