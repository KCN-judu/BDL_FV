---
id: FVD-0091
legacy-id: D-91
status: accepted
date: 2026-09-17
phase: 9b
area: surface
supersedes: []
superseded-by: []
related: []
production: [ADR-0025/supports]
---

# FVD-0091: `toList : opt τ → list τ` and `drop` are registered operators

## Status

Accepted in Phase 9b.

## Reason

Without `toList` an option has no eliminator that does not need a default value;
with it `fold` eliminates options (`optElimF`, `mapOptF`). `drop` is the dual of
`take`, needed by `zip`.
