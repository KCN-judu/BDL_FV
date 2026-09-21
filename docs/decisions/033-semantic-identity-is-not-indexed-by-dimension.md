---
id: FVD-0033
legacy-id: D-33
status: accepted
date: 2026-09-15
phase: 3
area: core
supersedes: []
superseded-by: []
related: [FVD-0029]
production: [ADR-0013/supports]
---

# FVD-0033: Semantic identity is not indexed by dimension

## Status

Accepted in Phase 3.

## Alternatives rejected

`ConceptId d`, `Ty.sem s d`.

## Reason

`same_dimension_does_not_imply_same_semantic_identity` — Tilt and MotorAngle
share `q Angle` and stay distinct with the direct wire rejected; the association
lives in `Θ` (FVD-0029). This is what Phase 2 + Phase 3 yield _instead of_ the
paper's `Sem[name, dimension]`.
