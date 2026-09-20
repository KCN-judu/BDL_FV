---
id: FVD-0058
legacy-id: D-58
status: accepted
date: 2026-09-15
phase: 7
area: validation
supersedes: []
superseded-by: []
related: []
production: [ADR-0006/supports, ADR-0015/supports]
---

# FVD-0058: Resources carry capabilities and per-capability units; sharing is a per-capability policy

## Status

Accepted in Phase 7.

## Alternatives rejected

`allDifferent` (Counterexample E); capability counts (C); pin capability without
units (`timers_matter`); protocol-specific solver logic (board tables carry pin
sets and units; grouping is generic `UnitRel.same`).
