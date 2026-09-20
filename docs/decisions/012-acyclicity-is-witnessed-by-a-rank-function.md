---
id: FVD-0012
legacy-id: D-12
status: accepted
date: 2026-09-14
phase: 1
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0010/supports]
---

# FVD-0012: Acyclicity is witnessed by a rank function

## Status

Accepted in Phase 1.

## Alternatives rejected

`WellFounded` on the dependency relation; a finite-graph DFS.

## Reason

Rank is the simplest witness that makes `Unfolds.exists_of_acyclic` a direct
strong induction; it is sufficient and for finite graphs equivalent.
`Acyclic.not_cyclic` connects it to the cycle predicate.
