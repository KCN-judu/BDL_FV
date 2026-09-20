---
id: FVD-0004
legacy-id: D-04
status: accepted
date: 2026-09-14
phase: 0
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0010/supports]
---

# FVD-0004: `DeclInterface.commitments` is a `List`, not a `Finset`

## Status

Accepted in Phase 0.

## Alternatives rejected

Mathlib `Finset`.

## Reason

Avoids the dependency; cost is that `InterfaceEquiv` is not antisymmetric.
Cosmetic.
