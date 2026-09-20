---
id: FVD-0052
legacy-id: D-52
status: accepted
date: 2026-09-15
phase: 6
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0005/supports]
---

# FVD-0052: Single-driver is a global invariant; completeness is the executable condition

## Status

Accepted in Phase 6.

## Decision

`SingleDriver β` (at most one) for partial designs, `CompleteOutputs β req`
(exactly one required) for executable ones. Local typing is insufficient
(`two_direct_drivers_locally_fine`). Joins commitments, causality, clock
consistency as global structure beyond STLC typing.
