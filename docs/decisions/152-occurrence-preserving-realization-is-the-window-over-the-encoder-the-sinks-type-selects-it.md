---
id: FVD-0152
legacy-id:
status: accepted
date: 2026-09-20
phase: 17
area: surface
supersedes: []
superseded-by: []
related: [FVD-0085, FVD-0132, FVD-0141, FVD-0143]
production: [ISS-0017/bears-on]
---

# FVD-0152: Occurrence-preserving realization is Phase 9a's window over the encoder declaration into the device domain with a `list raw` sink; the sink's type selects it; capacity stays Phase 9a's

## Status

Accepted in Phase 17.

## Decision

For a device that must receive every command of an output whose clock is faster
than the device's, the lowering is `lowerWindowΔ/Ω/β/Κ`: Phase 14's encoder
declaration `e` in the output's clock is the source of Phase 9a's five
declarations, transported by `sync` into the device domain `dc`, and the machine
sink accepts `list raw` in `dc` and is driven by `window`. Which lowering a
device takes — `lowerSync` (latest value) or `lowerWindow` (every value) — is
the sink's type, the device's consumption contract; the logical output is one
value stream in both and carries no flag. The batch's bound is
`CapacitySufficient` on the crossing `spec.clock → dc`, a deployment judgment.

## Alternatives rejected

An `Event`/`Stream` type or queue primitive for the crossing; an "event mode"
flag on the logical output; `lowerSync` for occurrence outputs (it collapses
`[A], [B]` to `[B]`: `exA_window_vs_sample`); capacity in typing.

## Reason

`lowerWindow_transparent`, `lowerWindow_correspondence`,
`lowerWindow_batch_rawCommands`, `lowerWindow_batch_unique`,
`lowerWindow_order_multiplicity`, `lowerWindow_bounded`,
`lowerWindow_envRefines`, `lowerWindow_singleDriver`, `lowerWindow_driveWF`,
`lowerWindow_wellClocked`, `lowerWindow_causal`, `lowerWindow_wf`
(`BDL/Surface/OutputWindow.lean`), over `buffer_window_correspondence_from`
(`Surface/Buffer.lean`, generalised). Executed `exA_window_vs_sample`, `exB`,
`exC_capacity`, `exF_correspondence`, `exF_structure`.

## Consequences

FVI-0024's occurrence-preserving crossing is built; what remains there is a
device that acknowledges and the initial representation. The kernel is
unchanged.
