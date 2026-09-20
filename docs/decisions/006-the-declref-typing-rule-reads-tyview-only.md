---
id: FVD-0006
legacy-id: D-06
status: accepted
date: 2026-09-14
phase: 1
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0010/supports]
---

# FVD-0006: The `declRef` typing rule reads `Δ.tyView` only

## Status

Accepted in Phase 1.

## Alternatives rejected

A rule that also inspects the referenced declaration's realization or
commitments.

## Reason

This is the formal content of "signature-first". It makes
`local_refinement_preserves_global_typing` immediate and is _necessary_ (probe
4). Reported as a definitional theorem.
