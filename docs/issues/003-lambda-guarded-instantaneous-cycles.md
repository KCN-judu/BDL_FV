---
id: FVI-0003
legacy-id: OI-03
state: deferred
area: core
opened: 2026-09-15
resolved-by: []
related: []
production: []
---

# FVI-0003: Lambda-guarded instantaneous cycles

## Problem

Lambda-guarded instantaneous cycles: rejected conservatively by `Causal`; the
negative theorem does not cover them.

## Audit (2026-09-20, surface reachability)

A lambda-guarded reference is instantaneous whenever the closure is applied at
the tick it is built, and in the current kernel a closure cannot survive a tick:
arrows are not data, so `delay`/`sync` refuse them (Phase 4,
`delay_not_under_binder`), and no declaration stores one. The only case
`Causal`'s conservative count loses is a closure that is built and _never_
applied at that tick (a rule passed to `fold` over an empty list) — a
data-dependent causality the language does not want; production's `bdl-ir`
`inst_refs` counts references under a rule exactly as the kernel does. The
negative theorem's gap is therefore a design choice, not a missing proof.

## Resolution

Deferred (2026-09-20): conservative rejection is the intended policy;
data-dependent causality is not wanted. Reopen only if a surface form needs a
closure that outlives its tick.
