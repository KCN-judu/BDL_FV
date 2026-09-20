---
id: FVD-0102
legacy-id: D-102
status: accepted
date: 2026-09-18
phase: 10
area: surface
supersedes: []
superseded-by: []
related: []
production: [ADR-0028/supports]
---

# FVD-0102: Unit semantics are stated exactly over an abstract scalar domain; the kernel's `Nat` and production's floats are models

## Status

Accepted in Phase 10.

## Decision

`Scalars K` with `Sym` (free abelian group on `2,3,5,127,π`): π is a generator,
`deg = π/180` exact. The `Nat` registry uses canonical sub-units and has no
radian; round trip 2 holds under divisibility only.

## Alternatives rejected

Pretending π is rational; hiding float approximation.
