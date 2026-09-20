---
id: FVD-0115
legacy-id: D-115
status: accepted
date: 2026-09-18
phase: 12
area: surface
supersedes: []
superseded-by: []
related: []
production: [ADR-0029/supports]
---

# FVD-0115: The canonical type `domain(inputs) -> B` with `domain([]) = ()` lives above the kernel; the kernel interface type is its normalization

## Status

Accepted in Phase 12.

## Decision

`UnitDomain.lean`: `CTy` (production's `Ty` with `Unit`), `canonical`, `encode`,
`elim`; `elim_canonical`, `decode_encode`, `canonicalOfKernel_encode`,
`canonical_injective`.

## Alternatives rejected

`Ty.unit`, `Value.unit`, `Expr.unit` in the kernel.

## Reason

The encoding is an exact bijection over concept signatures and a computed
normalization, so a kernel unit would add a type that no term has
(`elim unit = none`).
