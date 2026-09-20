---
id: FVD-0118
legacy-id: D-118
status: accepted
date: 2026-09-18
phase: 12
area: surface
supersedes: []
superseded-by: []
related: []
production: [ADR-0032/supports]
---

# FVD-0118: The source role is a realization state, not a type shape and not a kind

## Status

Accepted in Phase 12.

## Decision

`Source := realizationOf d = none`; `UnitDomain := tyView d` not an arrow;
`SimulationInput := Source ∧ UnitDomain` (production's narrowing).
`source_value`, `resolved_not_source`, `SimulationInput.value`.

## Alternatives rejected

A `source` semantic kind; equating every `() -> A` with a sensor.

## Reason

A resolved `() -> A` never consults `I`; an unresolved one is environment
provision at `(d, t)`, whatever its type.
