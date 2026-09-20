---
id: FVI-0021
legacy-id: OI-21
state: open
area: surface
opened: 2026-09-18
resolved-by: []
related: []
production: [ADR-0029]
---

# FVI-0021: Unit-domain normalization: `elim` beyond canonical types; the `Input` narrowing

## Problem

Unit-domain normalization (Phase 12): `elim` is proved on canonical types only;
a general `CTy` with nested interface products in _output_ position has no
kernel meaning by design (production refuses `()` as an output). Whether
production should narrow `Input` to unit-domain declarations at the model level
(rather than as Studio policy) is a presentation choice, not a semantic one.

## Resolution

Open.
