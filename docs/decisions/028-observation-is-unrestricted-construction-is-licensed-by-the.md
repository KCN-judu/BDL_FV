---
id: FVD-0028
legacy-id: D-28
status: accepted
date: 2026-09-15
phase: 3
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0013/supports]
---

# FVD-0028: Observation is unrestricted; construction is licensed by the realized declaration's signature

## Status

Accepted in Phase 3.

## Alternatives rejected

(B) observation only — safe (`provenance`) but _formally unable_ to realize any
mapping by a formula (`modelB_cannot_realize_mapping`); (D-alone) a witness with
no policy — it is a component, not a model.

## Decision

`rep` everywhere; `mk s` iff the grant permits `s`; client code at `Grant.none`;
a realization at `Grant.of` its own signature.

## Reason

`constructs_granted` (a `sem s` value is built only inside a declaration
announcing `sem s`), `grant_provenance`, `hidden_crossing_rejected_under_grant`,
and the positive `explicit_semantic_mapping_can_use_representation_formula`. The
signature is the smallest authority that makes every crossing visible at the
design level and needs no new annotation.

## Claim strength

Smallest among tested designs.
