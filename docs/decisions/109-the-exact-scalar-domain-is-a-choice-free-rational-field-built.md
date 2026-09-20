---
id: FVD-0109
legacy-id: D-109
status: accepted
date: 2026-09-18
phase: 10b
area: surface
supersedes: []
superseded-by: []
related: []
production: [ISS-0004/bears-on]
---

# FVD-0109: The exact scalar domain is a choice-free rational field built in the development

## Status

Accepted in Phase 10b.

## Decision

`Rational.lean`: `Q` as a quotient of `Int` fractions; laws by `Int` ring
identities; concrete equalities decided by cross-multiplication.

## Alternatives rejected

Core `Rat` (its lemmas depend on `Classical.choice`); `Nat` (no negatives, no
fractions); floating point in the formal model. Production `f64` gets a
toleranced property-test contract, not an exactness claim.
