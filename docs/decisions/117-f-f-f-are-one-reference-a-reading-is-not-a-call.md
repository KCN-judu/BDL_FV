---
id: FVD-0117
legacy-id: D-117
status: accepted
date: 2026-09-18
phase: 12
area: surface
supersedes: []
superseded-by: []
related: []
production: [ADR-0029/supports]
---

# FVD-0117: `f`, `f()`, `f(())` are one reference; a reading is not a call

## Status

Accepted in Phase 12.

## Decision

`RefForm.desugar`, `refForms_agree`, `Ev/MEv.declRef_env_irrelevant`,
`same_tick_same_value`, `Clocked.refForms`.

## Alternatives rejected

A per-reference application evaluated in the reader's environment.

## Reason

The value is indexed by `(d, t)` and independent of `ρ`; nothing the unique
argument could carry reaches the semantics.
