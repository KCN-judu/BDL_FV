---
id: FVD-0119
legacy-id: D-119
status: accepted
date: 2026-09-18
phase: 12
area: surface
supersedes: []
superseded-by: []
related: []
production: [ADR-0029/supports, ADR-0032/supports]
---

# FVD-0119: `A -> ()` is not a physical sink; the drive edge is

## Status

Accepted in Phase 12.

## Decision

`homUnit`, `unit_codomain_collapse`, `consumers_indistinguishable`,
`eval_independent_of_drives`; Phase 6's `OutputId`, `DriveWF`, `SingleDriver`,
`CompleteOutputs` retained (`driver_is_unit_domain` ties "may drive" to the
drive rule).

## Alternatives rejected

Unit-returning consumer functions.

## Reason

All pure total functions into the unit are equal, so the type cannot name a
receiver; consumption needs an effect/output semantics, which the drive edge
already is.
