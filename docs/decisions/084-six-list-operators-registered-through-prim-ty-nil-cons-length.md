---
id: FVD-0084
legacy-id: D-84
status: accepted
date: 2026-09-17
phase: 9a
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0024/supports]
---

# FVD-0084: Six list operators, registered through `Prim.ty`: `nil`, `cons`, `length`, `take`, `reverse`, `head`

## Status

Accepted in Phase 9a.

## Alternatives rejected

List typing/evaluation/domain rules; a general folding combinator in the kernel.

## Reason

The buffer and every tested policy need only these; typing is primitive
application, evaluation is `applyPrim`, `Clocked` has no list clause
(`list_clock_conservative`). Every earlier theorem is generic in primitives and
held unchanged.
