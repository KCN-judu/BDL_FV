---
id: FVD-0141
legacy-id:
status: accepted
date: 2026-09-20
phase: 15
area: surface
supersedes: []
superseded-by: []
related: [FVD-0138, FVD-0132, FVD-0045]
production: [ADR-0037/supports]
---

# FVD-0141: A device clock is an explicit `sync` lowering into the device domain; the carrier stays configuration

## Status

Accepted in Phase 15.

## Decision

A realization whose device consumes at another rate is lowered as
`e := encode (sync c initRep (rep d))` with `e` and the machine sink `p` in the
device domain `dc`, `c` the output's clock and `initRep` a pure closed
representation value (`lowerSyncΔ`/`lowerSyncΩ`/`lowerSyncΚ`). What is explicit
in the lowering: `dc` and `initRep`; what belongs to deployment: the choice of
both; nothing in the design. The carrier frequency remains configuration
(FVD-0138).

## Alternatives rejected

An implicit crossing (Phase 14 `exI`); a second transport primitive for devices;
the carrier as a `ClockId`; a device domain chosen by the design.

## Reason

`lowerSync_transparent`, `lowerSync_envRefines`, `lowerSync_singleDriver`,
`lowerSync_driveWF`, `syncBody_typed`, `lowerSync_wf`, `lowerSync_causal` (no
new instantaneous edge: `syncBody_instRefs = []`), `lowerSync_wellClocked`,
`lowerSync_correspondence` (the sink carries the command sampled strictly
before, or the initial representation's transfer); executed `exD_*`.
