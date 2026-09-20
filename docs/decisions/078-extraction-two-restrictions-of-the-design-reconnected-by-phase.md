---
id: FVD-0078
legacy-id: D-78
status: accepted
date: 2026-09-16
phase: 8b
area: behavior
supersedes: []
superseded-by: []
related: []
production: [ADR-0019/supports]
---

# FVD-0078: Extraction = two restrictions of the design reconnected by Phase-8a bindings

## Status

Accepted in Phase 8b.

## Alternatives rejected

Translating members into a new calculus; a tuple-returning declaration
(Counterexample 5); body substitution across the boundary.

## Reason

The component body _is_ the members' declarations; the reconnection is Phase-1
realization; `flat_WF` reuses Phase 8a.
