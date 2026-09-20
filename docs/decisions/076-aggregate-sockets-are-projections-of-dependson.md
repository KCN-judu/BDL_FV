---
id: FVD-0076
legacy-id: D-76
status: accepted
date: 2026-09-16
phase: 8b
area: behavior
supersedes: []
superseded-by: []
related: []
production: [ADR-0019/supports]
---

# FVD-0076: Aggregate sockets are projections of `DependsOn`

## Status

Accepted in Phase 8b.

## Alternatives rejected

Socket declarations; fan-out edges; "union of input concepts".

## Reason

Counterexample 6 (`fanout_false_dependency`); `socket_no_fanout`. The dependency
model is declaration-based, so the socket is `crossIn`/`crossOut` over it.
