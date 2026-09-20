---
id: FVI-0021
legacy-id: OI-21
state: resolved
area: surface
opened: 2026-09-18
resolved-by:
  [
    docs/reports/phase-12-unit-domain-normalization-and-the-source-boundary.md,
    FVD-0115,
    FVD-0118,
  ]
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

Resolved (2026-09-20) — no formal question remains. A general `elim` on `CTy`
with an interface product in output position has no kernel meaning by design:
the canonical interface is `domain(inputs) -> B` with `B` a kernel type
(FVD-0115), production refuses `()` as an output, and `elim_canonical` covers
every canonical type. The narrowing of `Input` to unit-domain declarations is
production's simulation-input policy (FVD-0118, `SimulationInput`), a
presentation choice, not a semantic one.
