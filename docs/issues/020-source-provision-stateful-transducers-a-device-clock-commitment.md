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

# FVI-0020: Source provision: stateful transducers, a device clock, commitment discharge, output provision

## Problem

Source provision (Phase 13): stateful transducers (memory in `tr`) and a
transparency theorem over streams; a device clock with a deployment `sync`;
commitment discharge by profile ranges (`hcomm`); output provision (the dual);
whether `computes` is checked or trusted; out-of-type raw readings as a
validation question.

## Resolution

Open. The **output provision** part is answered by Phase 14
([report](../reports/phase-14-output-realization-by-device-encoders.md)): output
realization is a lowering, not a provision, and its own open questions are
FVI-0022. The Source-side questions (stateful transducers, a device clock,
commitment discharge, `computes` checked or trusted, out-of-type readings)
remain open here.
