---
id: FVD-0111
legacy-id: D-111
status: accepted
date: 2026-09-18
phase: 11
area: surface
supersedes: []
superseded-by: []
related: []
production: [ADR-0028/supports]
---

# FVD-0111: Binder syntax desugars to the Phase-9 library applied to a lambda; a binder local is the lambda parameter

## Status

Accepted in Phase 11.

## Decision

`all x in xs: p ↦ allF τ (λx. p) xs` (any, map, filter alike); `desugar`
resolves names to de Bruijn indices, nearest binder first.

## Alternatives rejected

A binder construct in the kernel; a second variable calculus; binder clocks.

## Reason

`binder_*_typed`, `binder_*_eval`, `binder_clock` are instances of Phase-9
theorems; `desugar_rename` makes names invisible.
