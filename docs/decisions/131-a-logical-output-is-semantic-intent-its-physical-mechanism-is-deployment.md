---
id: FVD-0131
legacy-id:
status: accepted
date: 2026-09-20
phase: 14
area: surface
supersedes: []
superseded-by: []
related: [FVD-0050, FVD-0132]
production: [ADR-0015/supports]
---

# FVD-0131: A logical output is semantic intent; its physical mechanism is deployment data, never part of `OutputSpec`

## Status

Accepted in Phase 14.

## Decision

`OutputId`, `OutputSpec = ⟨accepts, clock⟩`, `DriveEnv`, `DriveWF` and `SingleDriver` stay exactly as Phase 6 left them and are read as the **logical output**: the behaviour's intent that the product carry `C` at the output's clock. Which mechanism moves the value to the world — PWM, GPIO level, I²C frame, UART packet — is chosen at deployment (`Realization`, `Encoder`) and appears nowhere in the design: no `deviceKind` in `OutputSpec`, no concept that implies a protocol (`Brightness` does not mean PWM; `SwitchState` does not mean GPIO).

## Alternatives rejected

`OutputSpec = ⟨accepts, clock, deviceKind⟩`; a concept whose identity fixes a protocol; a per-mechanism output kind.

## Reason

`exH` (`OutputRealizationExamples.lean`): one `oLight` accepting `Brightness` is realized by PWM (`pwm8`) and by an I²C register (`i2cReg`); the behaviour trace is identical (`two_realizations_same_behavior`), only the command types and traces differ. A kind in the spec would make that two designs. `lower_physicalOutput_unchanged`: realization changes no logical output.

## Consequences

Phase 6's wording "physical sink" is read as "logical output, physically realized by a machine sink" (amendment on FVD-0050). The Lean names are unchanged.
