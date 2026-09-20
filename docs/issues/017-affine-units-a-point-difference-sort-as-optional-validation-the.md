---
id: FVI-0017
legacy-id: OI-17
state: deferred
area: surface
opened: 2026-09-18
resolved-by: []
related: []
production: [ISS-0004]
---

# FVI-0017: Affine units: a point/difference sort as optional arithmetic validation

## Problem

Affine _coordinate_ semantics is solved: Phase 10b proves conversion complete as
coordinate change, a groupoid of affine maps, with the point/difference
decomposition and no sort required (`sort_orthogonal_to_conversion`, FVD-0106 …
FVD-0110). What remains optional is an _arithmetic validation_ — refusing
`20 °C + 30 °C` as a sum of two points — which is not required for affine-unit
correctness and would only matter once production exposes °C/°F (ISS-0004). The
display-name clause this item once carried is FVI-0019's and was never a theorem
obligation.

## Resolution

Deferred (2026-09-20): optional validation, not correctness; wait for
production's decision on exposing affine units (ISS-0004).
