---
id: FVI-0013
legacy-id: OI-13
state: resolved
area: core
opened: 2026-09-15
resolved-by: [FVD-0046]
related: []
production: []
---

# FVI-0013: Folding `ClockEnv` into the `DeclInterface` record (churn only)

## Problem

Folding `ClockEnv` into the `DeclInterface` record (churn only).

## Resolution

Resolved (2026-09-20) — rejected as representation churn. FVD-0046 already
decides that the clock is interface data held in a projection, not a record
field; every later construction keeps the projections independent (`DeclEnv`,
`ClockEnv`, `OutputEnv`, `DriveEnv`; Phase 13's `provision`/`provisionΚ`; Phase
14's `lowerΔ`/`lowerΩ`/`lowerβ`/`lowerΚ`; Phase 15's `lowerSyncΚ`), and each
theorem states exactly which projection it touches. Folding would change no
judgment and every proof.
