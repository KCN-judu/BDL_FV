---
id: FVD-0105
legacy-id: D-105
status: accepted
date: 2026-09-18
phase: 10
area: surface
supersedes: []
superseded-by: []
related: []
production: []
---

# FVD-0105: Preferred display units are presentation, not design

## Status

Accepted in Phase 10.

## Decision

`Presentation` beside `Design`; every kernel judgment is unchanged by
construction (`presentation_irrelevant_*`); ordering compares canonical
magnitudes (`ordering_ignores_presentation`).

## Design guidance

Literal unit = semantic source (in the formula text); concept preferred unit =
authoring metadata; simulation unit = UI state.
