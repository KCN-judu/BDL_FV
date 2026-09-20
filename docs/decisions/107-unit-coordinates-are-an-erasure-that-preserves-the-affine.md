---
id: FVD-0107
legacy-id: D-107
status: accepted
date: 2026-09-18
phase: 10b
area: surface
supersedes: []
superseded-by: []
related: []
production: [ISS-0004/bears-on]
---

# FVD-0107: Unit coordinates are an erasure that preserves the affine coordinate change

## Status

Accepted in Phase 10b.

## Decision

A chart is `⟨scale, offset⟩` over a field; `coord`/`reconstruct` are inverse
(`chart_left_inverse`, `chart_right_inverse`); the coordinate is a bare scalar
with no chart in it (`coordinate_is_chartless`, `coordinate_needs_chart`) and
the other coordinates are recovered from it and the charts
(`unit_erasure_preserves_conversion_structure`).

## Alternatives rejected

A runtime unit tag on scalars; units as data.
