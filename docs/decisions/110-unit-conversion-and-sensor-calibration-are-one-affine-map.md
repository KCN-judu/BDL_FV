---
id: FVD-0110
legacy-id: D-110
status: accepted
date: 2026-09-18
phase: 10b
area: surface
supersedes: []
superseded-by: []
related: []
production: [ISS-0004/bears-on]
---

# FVD-0110: Unit conversion and sensor calibration are one affine-map abstraction

## Status

Accepted in Phase 10b.

## Decision

`exH` (ADC → mV → calibrated reading), `exI` (encoder count → angle with home
offset) instantiate the same theorems.
