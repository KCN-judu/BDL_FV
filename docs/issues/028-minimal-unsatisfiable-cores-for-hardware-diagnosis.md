---
id: FVI-0028
legacy-id:
state: deferred
area: validation
opened: 2026-09-20
resolved-by: []
related: [FVI-0011]
production: []
---

# FVI-0028: Minimal unsatisfiable cores for hardware diagnosis

## Problem

`diagnose` reports a first dead end under one placement order, not a minimal
unsatisfiable core. Split from FVI-0011 (2026-09-20): explanation quality, not
correctness of feasibility.

## Current evidence

Phase 7 report; `Validation/Hardware.lean` `diagnose`.

## Dependencies

A decision that a minimal core is worth its cost over the first dead end
(production DI-21 chose the dead end).

## Resolution

Deferred (2026-09-20): optional; the semantic model of FVI-0011 comes first.
