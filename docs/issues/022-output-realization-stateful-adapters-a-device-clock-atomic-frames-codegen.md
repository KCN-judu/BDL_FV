---
id: FVI-0022
legacy-id:
state: open
area: surface
opened: 2026-09-20
resolved-by: []
related: [FVI-0020]
production: [ISS-0016, ISS-0017]
---

# FVI-0022: Output realization: stateful adapters, a device clock, atomic multi-value frames, codegen correspondence, output commitments

## Problem

Phase 14 realizes a logical output by a pure encoder in the output's clock and
stops at the raw command relation. Not modelled or not proved:

- **stateful output adapters** — slew-rate limiting, PWM dithering, protocol
  batching, servo smoothing, hysteresis: not pure encoders; whether each belongs
  to the behaviour (an ordinary declaration with `delay`), to deployment
  adaptation (a stateful lowering, with a stream-level correspondence theorem)
  or to the backend;
- **a device clock different from the output clock** — the explicit `sync`
  variant of the lowering (FVD-0138), and the distinction between a behaviour
  activation clock and a peripheral carrier frequency, which is configuration;
- **atomic multi-value frames** — whether a device that must receive several
  logical outputs in one indivisible frame ever forces a many-to-one
  construction beyond per-tick batching or upstream combination (FVD-0136). The
  counter-pressure case: a display controller whose one write frame carries a
  `Mode` and a `Level` that the behaviour drives as two independently meaningful
  logical outputs (`oMode accepts Mode`, `oLevel accepts Level`), and whose
  protocol rejects a frame with only one of them. Per-tick batching gives the
  backend both values at every activation of the common clock, and upstream
  combination gives one `Display accepts (Mode × Level)`; whether either is
  always acceptable, or whether a `lowerMany` with one encoder over two drivers
  and one machine sink is needed for atomicity, is undecided and is not settled
  by FVD-0136;
- **codegen correspondence** — the generated core's `Outputs` struct and the
  future platform adapter call against `RawCommand`: abstract trace → raw
  command trace is proved; raw command trace → backend call trace is not;
- **commitments on outputs** — production authors none; if a logical output ever
  carries a range or monotonicity commitment, whether the encoder's declared
  transfer must discharge it (the output analogue of FVD-0128).

## Current evidence

`BDL/Surface/OutputRealization.lean`: `lower_correspondence` (same clock, pure
encoder), `lower_wellClocked`, `lower_comm`; `exI` (an encoder in another domain
fails); `exD_hbridge` (a joint command from one upstream concept).
[Phase 14 report §14.2, §14.4](../reports/phase-14-output-realization-by-device-encoders.md).

## Dependencies

A production decision on the device catalogue for outputs (the `provides` half
of ISS-0016's device model); the first platform adapter.

## Resolution

Open.
