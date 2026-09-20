---
id: FVD-0007
legacy-id: D-07
status: accepted
date: 2026-09-14
phase: 1
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0009/supports]
---

# FVD-0007: Realization is write-once; "detach" is not a refinement step

## Status

Accepted in Phase 1.

## Alternatives rejected

Allowing `some e ↝ none` in `DeclLeq`.

## Reason

Detaching preserves typing of clients (tyView unchanged) but is not monotone for
evidence — any client evidence that consulted `B`'s realization is invalidated.
Detaching is therefore an _edit_ that re-opens validation of all transitive
dependents, not a refinement. The paper's "definitions may coexist, one active"
is carried as a pending surface question (`docs/kernel/minimality.md`).
