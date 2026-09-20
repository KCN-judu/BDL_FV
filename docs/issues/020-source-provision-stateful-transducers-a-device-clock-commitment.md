---
id: FVI-0020
legacy-id: OI-20
state: open
area: surface
opened: 2026-09-20
resolved-by: []
related: []
production: [PRP-0001, ISS-0016]
---

# FVI-0020: Source provision: stateful transducers, a device clock, commitment discharge

## Problem

Source provision (Phase 13): stateful transducers (memory in `tr`) and a
transparency theorem over streams; a device clock with a deployment `sync`;
commitment discharge by profile ranges (`hcomm`); whether `computes` is checked
or trusted; out-of-type raw readings as a validation question. ~~Output
provision (the dual)~~ — answered by Phase 14: output realization is a lowering,
not a provision.

## Audit (2026-09-20)

Production's first adapter refuses a design with a Source
(`adapter.inputs_unbound`, ADR-0037) and ISS-0016 (a device binding for a
Source) is still open, so the Source-side questions are blocked on the same
production evidence Phase 13 was: no device provides a Source yet. Phase 15's
explicit device clock for outputs (`lowerSync`) is the shape the Source-side
device clock would take in reverse.

## Amendment (2026-09-20, Phase 16)

Freshness is not a Source-side question: it is behaviour state — the design
counts ticks without a sample and says what stale means (`age`, `fresh`,
`timedOut`; `exG_freshness`), and no transducer could. Bounded buffered input is
narrowed to the provider's occurrence contract, FVI-0029 (a `list raw` reading
per tick, bounded, in arrival order). What remains here: stateful transducers, a
device clock on the Source side (the reverse of `lowerSync`), commitment
discharge, `computes` checked or trusted, out-of-type readings.

## Amendment (2026-09-20, Phase 17)

Bounded buffered input is answered: the provider's occurrence contract
(FVI-0029, resolved) delivers `(list raw, bool)` through Phase 13's shared raw
reading (`batchProvision`), and a scalar Source is the batch sampled
(`chLatest`). What remains here: stateful transducers, a Source-side device
clock (the input dual of `lowerSync` / `lowerWindow`), commitment discharge,
`computes` checked or trusted, out-of-type readings.

## Resolution

Open. The **output provision** part is answered by Phase 14
([report](../reports/phase-14-output-realization-by-device-encoders.md)): output
realization is a lowering, not a provision, and its own open questions are
FVI-0022. The Source-side questions (stateful transducers, a device clock,
commitment discharge, `computes` checked or trusted, out-of-type readings)
remain open here.
