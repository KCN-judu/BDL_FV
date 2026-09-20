---
id: FVD-0135
legacy-id:
status: accepted
date: 2026-09-20
phase: 14
area: surface
supersedes: []
superseded-by: []
related: [FVD-0126]
production: []
---

# FVD-0135: Output correspondence is directional; no injectivity, exactness or round-trip is required

## Status

Accepted in Phase 14.

## Decision

Correctness of a realization is `raw trace = transfer ∘ abstract trace` (`lower_correspondence`). The profile-declared transfer is the intended realization; two abstract values may encode to one command (quantization, saturation, calibration) and a round-trip `decode (encode x) = x` is neither assumed nor needed.

## Alternatives rejected

An exactness requirement or a joint-section condition on the output side by analogy with Phase 13 (`JointSection`); an injective-encoder condition; a decode.

## Reason

`exB_quantized`: 4-bit PWM sends duty 6 for 40 % and for 41 %, and the lowered design passes `driveWFCheck`; the correspondence theorem has no hypothesis on `transfer` beyond `computes`. The Source side needed a section because abstract inputs had to be *reached* from raw ones; the output side only has to *deliver* what the behaviour produced.
