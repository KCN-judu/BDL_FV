---
id: FVD-0069
legacy-id: D-69
status: accepted
date: 2026-09-15
phase: 8a
area: behavior
supersedes: []
superseded-by: []
related: []
production: [ADR-0021/supports, ADR-0022/supports]
---

# FVD-0069: Causality across instances is a validation condition on the inter-instance direct-binding graph

## Status

Accepted in Phase 8a.

## Alternatives rejected

"causal components compose causally" (Counterexample 1); port-level graphs
(finer; deferred).

## Reason

`flatten_causal`; self-edges are treated conservatively.
