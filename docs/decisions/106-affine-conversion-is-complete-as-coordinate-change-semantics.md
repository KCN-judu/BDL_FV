---
id: FVD-0106
legacy-id: D-106
status: accepted
date: 2026-09-18
phase: 10
area: surface
supersedes: []
superseded-by: []
related: []
production: [ISS-0004/bears-on]
---

# FVD-0106: Affine conversion is complete as coordinate-change semantics; point/delta is optional physical-arithmetic validation

## Status

Accepted in Phase 10; revised in Phase 10b.

## Decision

`celsius_not_linear`; `affLitE`/`affInUnitE` exact (`K/180` basis);
`delta_is_linear`; `sum_of_points_is_not_a_point` while `sum_well_typed`. Phase
10b: the chart laws, the groupoid laws and the difference law are proved without
any sort (`Charts.lean`); `AffSort` is orthogonal to conversion
(`sort_orthogonal_to_conversion`).

## Alternatives rejected

A kernel temperature type; faking °C with a scale; deferring conversion;
`Ty.q d sort`.

## Retained as optional

A validation annotation over operand sorts.
