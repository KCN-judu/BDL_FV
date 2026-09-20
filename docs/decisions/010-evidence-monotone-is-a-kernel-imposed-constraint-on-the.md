---
id: FVD-0010
legacy-id: D-10
status: accepted
date: 2026-09-14
phase: 1
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0010/supports]
---

# FVD-0010: `Evidence.Monotone` is a kernel-imposed constraint on the validation layer

## Status

Accepted in Phase 1.

## Alternatives rejected

Leaving discharge mechanisms unconstrained.

## Reason

`local_refinement_preserves_global_wf` is false otherwise (probe 6,
`badEv_not_mono`). Positivity in the environment is the minimal condition found;
whether some weaker condition suffices was not investigated because the
counterexample is already a one-declaration, one-step case.
