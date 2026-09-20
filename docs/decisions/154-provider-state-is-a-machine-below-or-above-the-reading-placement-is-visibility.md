---
id: FVD-0154
legacy-id:
status: accepted
date: 2026-09-20
phase: 18
area: surface
supersedes: []
superseded-by: []
related: [FVD-0123, FVD-0143, FVD-0149]
production: [ISS-0016/bears-on, PRP-0001/audits]
---

# FVD-0154: Provider state is a Mealy machine below the raw reading, movable upstream with the same Source trace; placement is decided by visibility, and a state that reads a design value is the design's

## Status

Accepted in Phase 18.

## Decision

A stateful transducer is a `Machine`: a pure BDL step term over data with an
explicit initial state. Run below the raw reading it is provider state; placed
above it as one declaration with `delay` (`machineBody`) it is behaviour state;
the Source's trace is the same (`provider_state_movable`). Placement is decided
by visibility: state whose parameter the product fixes, whose reset it commands
or whose reading it shows is upstream; state that only interprets a device's
signal may be the provider's. A state that reads a design value cannot be a
provider's (a channel term mentions no declaration; a machine's run is a
function of the raw stream alone).

## Alternatives rejected

Memory in the channel term (FVD-0123 stands); classification by implementation
convenience; a stateful primitive.

## Reason

`machine_upstream`, `below_source_trace`, `upstream_source_trace`,
`provider_state_movable`, `stateful_providers_same_trace`, `Machine.run_congr`
(`BDL/Surface/SourceBoundary.lean`, examples); executed `exA_filter`,
`exA_debounce_param`, `exA_quadrature`, `exA_hysteresis_param`,
`exA_latch_reads_design`.
