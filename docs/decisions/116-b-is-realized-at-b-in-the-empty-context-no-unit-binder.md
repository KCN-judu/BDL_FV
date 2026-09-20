---
id: FVD-0116
legacy-id: D-116
status: accepted
date: 2026-09-18
phase: 12
area: surface
supersedes: []
superseded-by: []
related: []
production: [ADR-0029/supports]
---

# FVD-0116: `() -> B` is realized at `B` in the empty context; no unit binder

## Status

Accepted in Phase 12.

## Decision

`zero_input_obligation` (`Iff.rfl`), `lams_typed`.

## Alternatives rejected

Literal `λ(). body` realizations and `app (declRef f) ()` references.

## Reason

`delay_not_under_binder`/`sync_not_under_binder` — a binder of any domain around
memory is untypable, so the literal encoding would forbid memory in every
zero-input declaration; `zero_input_memory` shows the kernel encoding permits
it. The unit must be eliminated before Core.
