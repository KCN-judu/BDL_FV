---
id: FVD-0114
legacy-id: D-114
status: accepted
date: 2026-09-18
phase: 11
area: surface
supersedes: []
superseded-by: []
related: []
production: [ADR-0028/supports]
---

# FVD-0114: `x ?? d` desugars to `getD`

## Status

Accepted in Phase 11.

## Decision

Trivially conservative (`coalesce_typed`, `exI`).
