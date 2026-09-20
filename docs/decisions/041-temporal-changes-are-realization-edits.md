---
id: FVD-0041
legacy-id: D-41
status: accepted
date: 2026-09-15
phase: 4
area: core
supersedes: []
superseded-by: []
related: [FVD-0016]
production: [ADR-0004/supports, ADR-0016/supports]
---

# FVD-0041: Temporal changes are realization edits

## Status

Accepted in Phase 4.

## Decision

Adding/removing a delay or changing an initial value is not `DeclLeq`
(`temporal_change_is_edit`); FVD-0016 applies unchanged.
