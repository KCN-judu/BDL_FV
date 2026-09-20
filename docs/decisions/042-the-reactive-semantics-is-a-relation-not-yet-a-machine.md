---
id: FVD-0042
legacy-id: D-42
status: accepted
date: 2026-09-15
phase: 4
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0004/supports, ADR-0016/supports]
---

# FVD-0042: The reactive semantics is a relation, not yet a machine

## Status

Accepted in Phase 4.

## Alternatives rejected

_Rejected for now:_ An explicit `MachineState`/`Step` with stored cells.

## Reason

The tick-indexed relation is the specification and suffices for determinism,
totality, causality, provenance, and the Event comparison; the stored-state
machine is an implementation to be proven equivalent in Phase 8.
