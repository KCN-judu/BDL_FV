---
id: FVD-0001
legacy-id: D-01
status: accepted
date: 2026-09-14
phase: 0
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0010/supports]
---

# FVD-0001: Commitments are atomic labels; evidence is abstract

## Status

Accepted in Phase 0.

## Alternatives rejected

Modelling semantic properties (monotonicity etc.) in Lean.

## Reason

The experiment is about refinement structure; `InterfaceRefines_iff_semantic`
shows the syntactic order is complete for abstract evidence, so nothing is lost
at this level.
