---
id: FVD-0039
legacy-id: D-39
status: accepted
date: 2026-09-15
phase: 4
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0004/supports, ADR-0016/supports]
---

# FVD-0039: State has no identity; state is structural

## Status

Accepted in Phase 4.

## Alternatives rejected

`StateId`, reuse of `DeclId`/`SemanticId` for cells.

## Reason

A delay node is referred to by nobody; consumers reference the declaration.
"Multiple writers" does not arise until actions (Phase 6).
