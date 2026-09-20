---
id: FVD-0024
legacy-id: D-24
status: accepted
date: 2026-09-15
phase: 2
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0013/supports]
---

# FVD-0024: Canonical closed inhabitants replaced by unresolved declarations

## Status

Accepted in Phase 2.

## Decision

`Ty.canon` removed; `InterfaceRefines_iff_semantic` now inhabits a type by
`declRef` in a one-declaration environment (`DeclEnv.single_hasType`).

## Reason

Opaque semantic types have no closed inhabitants, and signature-first typing
never needed them.
