---
id: FVD-0003
legacy-id: D-03
status: accepted
date: 2026-09-14
phase: 0
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0010/supports]
---

# FVD-0003: `strengthen` on a realized declaration carries a re-verification premise

## Status

Accepted in Phase 0.

## Alternatives rejected

`strengthen` with only `InterfaceRefines S S'`.

## Reason

Theorem 4 fails (`naive_breaks_wellformedness`).
