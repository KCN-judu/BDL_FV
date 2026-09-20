---
id: FVD-0050
legacy-id: D-50
status: accepted
date: 2026-09-15
phase: 6
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0005/supports]
---

# FVD-0050: Physical sinks have nominal identity (`OutputId`), separate from `SemanticId` and `DeclId`

## Status

Accepted in Phase 6.

## Alternatives rejected

Type-keyed sinks (`type_keyed_binding_collides`); `SemanticId` as sink (one
concept, many devices); `DeclId` as sink (Counterexample A becomes unstatable);
deployment-only binding (completeness is a design-time acceptance condition).

## Amendment (2026-09-20, Phase 14)

The choice stands; the wording is refined. `OutputId` names a **logical output**
— the behaviour's intent that the product carry a value at the output's clock —
which deployment _physically realizes_ by a machine sink and a device encoder
(FVD-0131, FVD-0132). "Physical sink" in Phase 6 meant _terminal, outside the
behaviour_ (no feedback edge), not _a device_; the mechanism is never in
`OutputSpec`.
