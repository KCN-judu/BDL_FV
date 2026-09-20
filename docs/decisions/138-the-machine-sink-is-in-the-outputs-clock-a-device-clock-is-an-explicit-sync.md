---
id: FVD-0138
legacy-id:
status: accepted
date: 2026-09-20
phase: 14
area: surface
supersedes: []
superseded-by: []
related: [FVD-0045, FVD-0055]
production: [ADR-0037/supports, ISS-0017/bears-on]
---

# FVD-0138: The machine sink is in the output's clock; a device clock is an explicit `sync`; a carrier frequency is not a `ClockId`

## Status

Accepted in Phase 14.

## Decision

`lowerΩ` places the machine sink in `spec.clock` and `lowerΚ` places the encoder
there: the command is produced exactly when the logical output is. A device that
consumes commands at another rate needs an explicit `sync` declaration in the
lowered design (Phase 5's transport), never an implicit resampling in the
binding. A peripheral's carrier frequency (the PWM period, the bus clock) is
device configuration checked by validation, not a BDL `ClockId`.

## Alternatives rejected

An implicit same-tick bridge or resampling in the drive edge (`exI`: an encoder
in another domain fails `DriveWF` and `WellClocked`); a `ClockId` per carrier.

## Reason

`lower_wellClocked`, `lower_driveWF`; Phase 6 Counterexample G
(`output_binding_respects_clock_domain`) already forbids a crossing in the
binding. The `sync` variant is not built (FVI-0022).
