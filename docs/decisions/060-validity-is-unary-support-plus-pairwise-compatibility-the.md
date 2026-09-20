---
id: FVD-0060
legacy-id: D-60
status: accepted
date: 2026-09-15
phase: 7
area: validation
supersedes: []
superseded-by: []
related: []
production: [ADR-0006/supports, ADR-0015/supports]
---

# FVD-0060: Validity is unary support plus pairwise compatibility; the solver is exhaustive DFS, proved sound and complete

## Status

Accepted in Phase 7.

## Alternatives rejected

_Rejected for now:_ SMT integration; minimal unsat cores.

## Reason

All tested constraints are unary/binary, so pruning on prefixes is complete
(`solve_complete`); `decide` runs the instances in seconds; `diagnose` gives a
first dead end.

## Claim strength

For the tested pin/peripheral scope.
