---
id: FVI-0018
legacy-id: OI-18
state: resolved
area: core
opened: 2026-09-15
resolved-by:
  [FVD-0094, docs/reports/phase-14-output-realization-by-device-encoders.md]
related: []
production: []
---

# FVI-0018: Grant delegation to higher-order mappings

## Problem

Grants are per-signature; whether a realization may _delegate_ its grant
(higher-order mappings taking a constructor as argument) is untested.

## Resolution

Resolved (2026-09-20) — delegation is unnecessary. A realization's body is typed
under its own signature's grant, and every `mk` inside it — including inside a
rule passed to a library equation — is licensed by that grant
(`HasType.constructs_granted`); a closure crosses to another declaration only as
a value whose body was checked where it was written, and a library combinator
adds no privilege (`lib_expansion`, FVD-0094). Phase 13's channels and Phase
14's encoders are typed under `Grant.none` and construct nothing
(`channel_constructs_nothing`, `encoder_constructs_nothing`). No current surface
program needs a constructor as an argument that its own declaration could not
write; without such a witness no delegation calculus is added.
