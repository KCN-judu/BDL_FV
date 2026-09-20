---
id: FVD-0005
legacy-id: D-05
status: accepted
date: 2026-09-14
phase: 1
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0010/supports]
---

# FVD-0005: References are by `DeclId` inside `Expr` (`declRef`), not a separate `DesignExpr`

## Status

Accepted in Phase 1.

## Alternatives rejected

A two-level syntax.

## Reason

Nothing distinguishes a realization from any other term except that it may
mention declarations; one syntax with `refs` is smaller.
