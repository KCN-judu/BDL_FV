---
id: FVD-0035
legacy-id: D-35
status: accepted
date: 2026-09-15
phase: 4
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0004/supports, ADR-0016/supports]
---

# FVD-0035: `delay` is data-typed and top-level (empty context)

## Status

Accepted in Phase 4.

## Alternatives rejected

Delay at function types; delay under lambdas.

## Reason

Forced by the totality proof — closures cannot be transported across ticks
(`Red_data` needs `τ.Data`), and a delay under a lambda would evaluate its
operand at the previous tick under a current-tick environment.

## Consequences

Temporal state belongs to declarations; mappings are pointwise; reusable
stateful components need instantiation (Phase 8). Also scopes
`HasType.weaken_append` / `Unfolds.preserves_typing` to the delay-free fragment
— the domain of validity of the Phase-1 inlining results.
