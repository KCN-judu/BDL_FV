---
id: FVD-0009
legacy-id: D-09
status: accepted
date: 2026-09-14
phase: 1
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0010/supports]
---

# FVD-0009: `Evidence` takes the environment as an argument

## Status

Accepted in Phase 1.

## Alternatives rejected

Phase 0's `Expr → PropertyId → Prop`.

## Reason

Compositional discharge ("A monotone because B committed monotone", `compEv`) is
otherwise inexpressible, and it is exactly the case that makes probe 5 fail.
Constant evidence is a special case (`Evidence.Monotone.of_const`).
