---
id: FVD-0092
legacy-id: D-92
status: accepted
date: 2026-09-17
phase: 9b
area: surface
supersedes: []
superseded-by: []
related: []
production: [ADR-0025/supports]
---

# FVD-0092: Rank-1 polymorphism is definitional: families instantiated by matching; no type variable in the kernel

## Status

Accepted in Phase 9b.

## Alternatives rejected

Kernel type variables (open declaration types would be meaningless); System F
terms (`Λ`, `[τ]`) — their prenex fragment is family instantiation
(`PolyAlternatives`); higher rank — every candidate is rank ≥ 2 with a rank-1
replacement (`applyBoth_rank`, `applyBoth_replacement`); let-generalization and
principal-type search — use sites have closed argument types, so instantiation
is one-way matching (`matchTy_sound`, `matchTy_complete`).
