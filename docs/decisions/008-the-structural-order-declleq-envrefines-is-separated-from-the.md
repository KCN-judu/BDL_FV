---
id: FVD-0008
legacy-id: D-08
status: accepted
date: 2026-09-14
phase: 1
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0010/supports]
---

# FVD-0008: The structural order (`DeclLeq`, `EnvRefines`) is separated from the invariant (`GlobalWF`)

## Status

Accepted in Phase 1.

## Alternatives rejected

Phase 0's `DeclLeq` which bundled well-formedness of the target.

## Reason

The typing theorem holds under the structural order alone; bundling would have
hidden that its hypotheses are weaker than the commitment theorem's. The Phase-0
characterization survives as
`DeclRefinesStar_iff : … ↔ DeclLeq h₁ h₂ ∧ WellFormedDecl ev Δ Γ h₂`.
