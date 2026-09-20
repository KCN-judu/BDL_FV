---
id: FVD-0094
legacy-id: D-94
status: accepted
date: 2026-09-17
phase: 9b
area: surface
supersedes: []
superseded-by: []
related: []
production: [ADR-0025/supports]
---

# FVD-0094: The equation library is a set of combinators, inlined at use sites

## Status

Accepted in Phase 9b.

## Decision

`Comb`: no reference, state, transport, `rep` or `mk`.

## Proved once

Typing independent of Δ, Θ, G (`HasType.comb_irrelevant`), evaluation
context-free (`lib_eval_context_free` from `Ev.pure`), clocked everywhere
(`lib_clocked`), no construction (`Comb.noConstruct`), and the combined
expansion statement (`lib_expansion`).

## Alternatives rejected

Library functions as declarations (would be monomorphic and would enter the
dependency graph).
