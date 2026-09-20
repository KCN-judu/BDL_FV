---
id: FVI-0004
legacy-id: OI-04
state: deferred
area: core
opened: 2026-09-15
resolved-by: []
related: []
production: []
---

# FVI-0004: Higher-order `unfolds_preserves_eval` (closure equivalence)

## Problem

Higher-order `unfolds_preserves_eval` (closure equivalence).

## Audit (2026-09-20)

`Unfolds` is the Phase-1 alternative semantics for the timeless fragment; the
executable definition is the tick evaluator (`Ev`/`MEv`), which production
transcribes (ADR-0016). A higher-order agreement theorem between the two would
change no judgment and no production artefact.

## Resolution

Deferred (2026-09-20): proof churn with no semantic consequence; the unfolding
semantics is not the executable definition.
