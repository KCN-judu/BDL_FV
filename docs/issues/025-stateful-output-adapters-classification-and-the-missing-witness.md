---
id: FVI-0025
legacy-id:
state: open
area: surface
opened: 2026-09-20
resolved-by: []
related: [FVI-0022]
production: [ISS-0017]
---

# FVI-0025: Stateful output adapters: the classification and the missing non-encodability witness

## Problem

Phase 15 classifies the representative cases before generalizing: **slew-rate limiting, servo smoothing, hysteresis** are product-observable and are ordinary behaviour state upstream of the logical output (executed: `exE_slew` — a `delay` declaration ramps the brightness and the same pure encoder produces the ramped raw trace); **debouncing** is Source-side (FVI-0020); **PWM dithering** modulates below the tick — the model has no finer time than a tick, so it is backend implementation; **protocol batching** is the backend's per-tick commit. No case produced a value that needs state *between* the logical output and the raw command that the design could not hold itself; no stateful realization primitive is added. Open: a witness that cannot be represented by behaviour state upstream plus a pure encoder plus backend state — none is known.

## Current evidence

`AdapterExamples.lean` `exE_slew`; Phase 15 report §15.2.

## Dependencies

A concrete device protocol whose state is neither product-observable nor below the tick.

## Resolution

Open.
