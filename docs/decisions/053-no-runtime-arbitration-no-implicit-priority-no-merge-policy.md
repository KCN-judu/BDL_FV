---
id: FVD-0053
legacy-id: D-53
status: accepted
date: 2026-09-15
phase: 6
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0005/supports]
---

# FVD-0053: No runtime arbitration, no implicit priority, no merge policy

## Status

Accepted in Phase 6.

## Alternatives rejected

First/last/numeric-priority policies; effect-handler arbitration.

## Reason

Hidden policies are observable (`hidden_arbitration_observable`); priority, max,
blend, clamp are ordinary declarations of the target type
(`explicit_priority_single_driver`).

## Claim strength

Unnecessary in the tested architecture; not a universal impossibility.
