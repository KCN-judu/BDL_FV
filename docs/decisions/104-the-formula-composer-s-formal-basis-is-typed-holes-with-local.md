---
id: FVD-0104
legacy-id: D-104
status: accepted
date: 2026-09-18
phase: 10
area: surface
supersedes: []
superseded-by: []
related: []
production: [ADR-0028/supports]
---

# FVD-0104: The Formula Composer's formal basis is typed holes with local bidirectional dimension inference — no unification

## Status

Accepted in Phase 10.

## Decision

`PExpr`, `check`, `solve` (add/sub propagate; mul `r−d`; div `r+d`, `d−r`);
`solve_sound`, `solve_complete`; candidates from the solved dimension
(`candidates_sound/_complete`). Two-hole operands are unsolved, not searched.

## Alternatives rejected

A general constraint solver; executing partial terms.
