---
id: FVD-0095
legacy-id: D-95
status: accepted
date: 2026-09-17
phase: 9b
area: surface
supersedes: []
superseded-by: []
related: []
production: [ADR-0025/supports]
---

# FVD-0095: Sets, intervals, records, predicates, finite quantifiers are surface

## Status

Accepted in Phase 9b.

## Decision

`x ∈ {…}` is `contains` over a list literal (`oneOf_mem`; duplicates
irrelevant); an interval is a pair with a convention (`inIntervalF`); a record
is a right-nested pair with positional projections (`recTy`, `projE_typed`); a
predicate is `α → bool`; `forall/exists x in xs` are `all`/`any`
(`forall_in_list`, `exists_in_list`).

## Alternatives rejected

A `Set` type, a record type, row polymorphism, quantifiers in expressions.
