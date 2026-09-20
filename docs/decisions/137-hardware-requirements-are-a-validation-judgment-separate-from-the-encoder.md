---
id: FVD-0137
legacy-id:
status: accepted
date: 2026-09-20
phase: 14
area: surface
supersedes: []
superseded-by: []
related: [FVD-0057, FVD-0062]
production: [ADR-0015/supports]
---

# FVD-0137: Hardware requirements are a validation judgment separate from the encoder

## Status

Accepted in Phase 14.

## Decision

`DeviceOutputProfile = ⟨E, requirements⟩`. `Admissible Θ accepts H P := EFits Θ accepts P.E ∧ (solve H P.requirements).isSome`: the encoder is behaviour-to-command semantics, the requirements are what the board must carry; each is checked by its own judgment and neither knows the other. Nothing electrical is claimed.

## Alternatives rejected

Requirements inside the encoder; the encoder inside the hardware model; a solver that sees the design.

## Reason

`admissible_satisfiable` (Phase 7's `satisfiable_iff_solve`); `exH_admissible`: the PWM profile and the I²C profile are both admissible for the light on the Nano, and the PWM profile is not admissible for the relay — the fit fails, the pins do not.
