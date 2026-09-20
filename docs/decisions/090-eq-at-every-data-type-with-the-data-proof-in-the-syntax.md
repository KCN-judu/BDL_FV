---
id: FVD-0090
legacy-id: D-90
status: accepted
date: 2026-09-17
phase: 9b
area: surface
supersedes: []
superseded-by: []
related: [FVD-0098]
production: [ADR-0025/supports]
---

# FVD-0090: `eq` at every data type, with the data proof in the syntax

## Status

Accepted in Phase 9b.

## Alternatives rejected

Equality on quantities only (boolean equality had to be encoded); a typing side
condition (would change the `prim` rule).

## Reason

Structural equality is defined on all data values (`Value.beq`); typing already
forbids comparing two concepts. The proof field makes `eq (arr ..)` unwritable.
_(9b also generalized `lt` to every data type through a structural order;
FVD-0098 reverts that.)_
