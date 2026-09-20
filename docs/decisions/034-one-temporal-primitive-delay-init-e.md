---
id: FVD-0034
legacy-id: D-34
status: accepted
date: 2026-09-15
phase: 4
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0004/supports, ADR-0016/supports]
---

# FVD-0034: One temporal primitive: `delay init e`

## Status

Accepted in Phase 4.

## Alternatives rejected

_Rejected as primitives:_ `previous`, `hold`, `count`, `since`, `once`, `every`,
`rise`, `Event`, `Signal`. Each was reduced to `delay` plus `Prim` and executed
(`*_trace`).

## Reason

No candidate adds observable behaviour, changes causality beyond one delayed
self-edge, or needs its own storage.

## Claim strength

Expressibility by execution; there is no kernel definition for them to be
equivalent to.
