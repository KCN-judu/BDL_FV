---
id: FVI-0020
legacy-id: OI-20
state: resolved
area: surface
opened: 2026-09-20
resolved-by:
  [
    docs/reports/phase-18-the-source-side-boundary-provider-state-device-clock-commitments-and-readings.md,
  ]
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

Resolved by
[Phase 18](../reports/phase-18-the-source-side-boundary-provider-state-device-clock-commitments-and-readings.md)
(2026-09-20), each remainder on its own:

- **stateful transducers** — resolved: a Mealy machine below the raw reading or
  above it gives the same Source trace (`provider_state_movable`); placement is
  visibility, and a state that reads a design value is the design's (FVD-0154);
- **a Source-side device clock** — resolved: `provisionSync` (sampled, an
  explicit `sync` with an explicit initial value) and `provisionWindow`
  (occurrences, Phase 9a's window) (FVD-0155);
- **commitment discharge by profile ranges** — resolved: three evidence levels,
  static / checked / trusted, the trusted assumption a visible hypothesis
  (FVD-0156);
- **`computes` checked or trusted** — resolved: proof-carrying, derived from the
  term (`Channel.ofTerm`), decided at a finite raw type (`computes_of_bool`); a
  separately supplied function at an infinite raw type is a claim to test, not a
  formal question (FVD-0157);
- **out-of-type readings** — resolved: refused by the checking provider,
  crossing as `none` or a flag (FVD-0158).

Earlier remainders: the output-provision half was answered by Phase 14;
freshness is behaviour state (Phase 16); bounded buffered input is the
provider's occurrence contract (Phase 17, FVI-0029). What stays outside the
formal development: which bound or range a physical device needs (a deployment
assumption), and the production slice itself (ISS-0016).
