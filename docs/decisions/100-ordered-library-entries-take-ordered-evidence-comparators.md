---
id: FVD-0100
legacy-id: D-100
status: accepted
date: 2026-09-18
phase: 9c
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0025/supports, ADR-0026/supports]
---

# FVD-0100: Ordered library entries take `Ordered` evidence; comparators recover them

## Status

Accepted in Phase 9c.

## Decision

`min`/`max`/`clamp`/`inRange`/`inInterval` are indexed by `Ordered τ` (`q d` |
`sem s d`, well formed against Θ); `contains`/`oneOf` keep the `Data` proof;
`map`/`fold`/`any`/`all`/`filter` need neither. `minBy_recovers_min`: the
comparator escape hatch loses nothing. Combinators admit `rep` (needed by
ordered concepts); their typing is independent of Δ and G and reads Θ only
through write-once bindings.
