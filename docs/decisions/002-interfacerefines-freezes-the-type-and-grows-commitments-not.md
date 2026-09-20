---
id: FVD-0002
legacy-id: D-02
status: accepted
date: 2026-09-14
phase: 0
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0010/supports]
---

# FVD-0002: `InterfaceRefines` freezes the type and grows commitments; not logical implication

## Status

Accepted in Phase 0.

## Alternatives rejected

`InterfaceRefines := ∀ realizations, Satisfies new → Satisfies old`.

## Reason

Equivalent (`InterfaceRefines_iff_semantic`) and the syntactic form is
decidable.
