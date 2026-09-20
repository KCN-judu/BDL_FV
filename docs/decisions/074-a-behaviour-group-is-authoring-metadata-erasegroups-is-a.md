---
id: FVD-0074
legacy-id: D-74
status: accepted
date: 2026-09-16
phase: 8b
area: behavior
supersedes: []
superseded-by: []
related: []
production: [ADR-0019/supports]
---

# FVD-0074: A behaviour group is authoring metadata; `eraseGroups` is a projection

## Status

Accepted in Phase 8b.

## Alternatives rejected

A group as a kernel term; a group as a declaration; groups carrying types,
clocks, outputs or formulas.

## Reason

Theorems A–G of `Group.lean` are `rfl`/`Iff.rfl` — the group never enters the
design, so nothing it could carry would be semantic.
