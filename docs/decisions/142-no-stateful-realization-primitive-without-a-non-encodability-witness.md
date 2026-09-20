---
id: FVD-0142
legacy-id:
status: accepted
date: 2026-09-20
phase: 15
area: surface
supersedes: []
superseded-by: []
related: [FVD-0133, FVD-0136]
production: [ISS-0017/bears-on]
---

# FVD-0142: No stateful realization primitive without a non-encodability witness; the representative cases are behaviour, Source-side or backend

## Status

Accepted in Phase 15.

## Decision

No `StatefulEncoder` is added. Slew-rate limiting, servo smoothing and
hysteresis are product-observable and are ordinary behaviour state upstream of
the logical output (`delay` declarations the designer reads and simulates);
debouncing is Source-side (FVI-0020); PWM dithering is below the tick and
therefore backend implementation; protocol batching is the backend's per-tick
commit. A stateful primitive between the logical output and the raw command
requires a case none of these can represent; none is known (FVI-0025).

## Alternatives rejected

A `StatefulEncoder`; `delay` inside `Encoder`; adapter state promoted into the
realization.

## Reason

`exE_slew`: the slew-limited brightness as a `delay` declaration
(`10, 20, 30, 40`) and the same pure encoder producing the ramped raw trace
(`25, 51, 76, 102`); the line's hold state is already a fold below the boundary
(FVD-0140).
