---
id: FVD-0123
legacy-id: D-123
status: accepted
date: 2026-09-20
phase: 13
area: surface
supersedes: []
superseded-by: []
related: []
production: [PRP-0001/audits]
---

# FVD-0123: A channel carries the transfer function and the term that computes it

## Status

Accepted in Phase 13.

## Decision

`Channel.transfer : Value → Value` with
`computes : ∀ v, TyVal raw v → Transduces tr v (transfer v)`.

## Alternatives rejected

The term alone.

## Reason

The induced input must be a function; extracting it from per-tick existence is a
choice principle, outside the development's axiom base.
