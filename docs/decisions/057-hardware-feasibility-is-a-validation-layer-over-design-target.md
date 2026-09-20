---
id: FVD-0057
legacy-id: D-57
status: accepted
date: 2026-09-15
phase: 7
area: validation
supersedes: []
superseded-by: []
related: []
production: [ADR-0006/supports, ADR-0015/supports]
---

# FVD-0057: Hardware feasibility is a validation layer over `Design × Target`, not typing

## Status

Accepted in Phase 7.

## Alternatives rejected

`Ty.pwm`/`Ty.pin`/…; feasibility as a semantic commitment.

## Reason

`seven_pwm_design_semantically_valid ∧ seven_pwm_unsat_on_nano`; the same
requirements are SAT on a larger board; the solver's type never mentions `Δ`.
