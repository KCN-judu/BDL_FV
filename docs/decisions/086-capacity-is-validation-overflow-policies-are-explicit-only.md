---
id: FVD-0086
legacy-id: D-86
status: accepted
date: 2026-09-17
phase: 9a
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0027/supports]
---

# FVD-0086: Capacity is validation; overflow policies are explicit; only rejecting the deployment preserves semantics

## Status

Accepted in Phase 9a.

## Decision

`CapacitySufficient` (decidable for a finite horizon), `requiredCapacity` (least
sufficient, proved), `periodic_capacity_sufficient` (one destination period
suffices for periodic schedules at every horizon). `dropOldest`/`dropNewest` are
functions of the unbounded window: identity under sufficient capacity
(`sufficient_capacity_preserves`), trace-changing under insufficient capacity
(`negE`).

## Alternatives rejected

Implicit overflow in the kernel.
