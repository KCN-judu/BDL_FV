---
id: FVD-0026
legacy-id: D-26
status: accepted
date: 2026-09-15
phase: 3
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0013/supports]
---

# FVD-0026: Unrestricted symmetric `mk`/`rep` rejected

## Status

Accepted in Phase 3.

## Alternatives rejected

Global `rep_s : sem s → R` and `mk_s : R → sem s` (Model A).

## Reason

_formally rejected by counterexample_ —
`unrestricted_representation_binding_bypasses_semantic_identity` gives a closed
`Tilt → MotorAngle` in the empty environment;
`hidden_crossing_inside_unrelated_body` hides it inside an unrelated signature;
Phase-2 provenance becomes false.
