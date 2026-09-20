---
id: FVD-0081
legacy-id: D-81
status: accepted
date: 2026-09-16
phase: 8b
area: behavior
supersedes: []
superseded-by: []
related: [FVD-0074]
production: [ADR-0019/supports]
---

# FVD-0081: Identity: templates keep original identities; instances are fresh; the group id is never a component id

## Status

Accepted in Phase 8b.

## Decision

Before packaging nothing is renamed (FVD-0074). After packaging the flattened
system uses `W + n` and `2W + n`; further instances `3W + n`, ….
