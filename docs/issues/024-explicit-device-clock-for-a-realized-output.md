---
id: FVI-0024
legacy-id:
state: open
area: surface
opened: 2026-09-20
resolved-by: []
related: [FVI-0022, FVI-0020]
production: [ISS-0017]
---

# FVI-0024: Explicit device clock for a realized output: what remains after the `sync` lowering

## Problem

Phase 15 lowers a realization into a device domain through Phase 5's transport
(`lowerSyncΔ`: `e := encode (sync c initRep (rep d))`, `e` and `p` in `dc`) and
proves behaviour preservation, well-formedness, causality (no new instantaneous
edge), clocks, single-driver and the sampled correspondence
(`lowerSync_correspondence`). What remains: a device that acknowledges (a bus
transaction with a reply) is not a `sync`; the choice of `initRep` is
deployment's and no theorem says which value a device should hold before the
first activation; production has no spelling for a device domain at all (the
adapter's carrier is configuration, FVD-0138).

## Current evidence

`BDL/Surface/DeviceClock.lean`; `AdapterExamples.lean` `exD_device_clock`,
`exD_initial`, `exD_structure`.

## Dependencies

A production device that consumes at its own rate (ISS-0017); then a deployment
spelling for the device domain and the initial representation.

## Amendment (2026-09-20, Phase 16)

One more remainder, found by attacking the state-only thesis (Phase 16 §16.2):
`lowerSync` samples the last command, so two commands specified between two
device activations reach a slower device as one. An occurrence-preserving
crossing is a construction over existing primitives — the Phase-9a window
mirrored into the lowering: a log in the output's clock, transported by `sync`,
a cursor in the device domain, a `list raw` sink whose batch the backend commits
in order — and it is not built. Not a primitive gap; a lowering to write and
prove when a device that must not miss a command exists.

## Amendment (2026-09-20, Phase 17)

The occurrence-preserving crossing is built: `lowerWindow` in
`BDL/Surface/OutputWindow.lean` — Phase 9a's window over the encoder declaration
into the device domain, a `list raw` sink — with `lowerWindow_transparent`,
`lowerWindow_correspondence`, `lowerWindow_bounded` and the structural theorems
(FVD-0152); the adapter's batch is `List Op` (FVD-0153). What remains here is
narrower: a device that acknowledges (a bus transaction with a reply is not a
`sync` and not a window) and which initial representation a device should hold
before the first activation.

## Amendment (2026-09-20, Phase 18)

The Source side's initialization (FVD-0155) shares one principle with the
"initial representation" left here: every crossing carries an explicit `InitRep`
— `lowerSync`'s and `syncBody`'s on the output side, `provisionSync`'s on the
input side — and the input side names its two policies (`InitPolicy.supplied`,
`InitPolicy.unavailable`). The output side's choice of that value is a device
profile's field, not a theorem's subject; what remains open here is only whether
the sink should carry an _unavailable_ form before the first command (the dual
of the optional Source), which no device yet asks for. A device that
acknowledges is an interaction of two boundaries — the acknowledgement is a
Source (Phase 16's `acked`) — and not a new crossing; it stays here only as the
codegen half FVI-0023 owns.

## Resolution

Open.
