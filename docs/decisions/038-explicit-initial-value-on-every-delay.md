---
id: FVD-0038
legacy-id: D-38
status: accepted
date: 2026-09-15
phase: 4
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0004/supports, ADR-0016/supports]
---

# FVD-0038: Explicit initial value on every delay

## Status

Accepted in Phase 4.

## Alternatives rejected

`previous : τ → opt τ` as the primitive (derivable); no init (undefined or
nondeterministic first tick, `first_tick_*`); init as a validation obligation
(nothing to validate without a unique first step).
