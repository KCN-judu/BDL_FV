---
id: FVD-0045
legacy-id: D-45
status: accepted
date: 2026-09-15
phase: 5
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0004/supports]
---

# FVD-0045: One transport primitive `sync src init e`, reading strictly before

## Status

Accepted in Phase 5.

## Alternatives rejected

Same-tick-visible transport (makes scheduler order semantic,
`scheduling_order_observable`); separate `hold`/`latest`/`sample` primitives
(all are `sync`); a buffering primitive (derivable:
`buffer_from_log_and_cursor`).

## Reason

`delay_is_sync_own` — the Phase-4 state primitive is this primitive at the own
domain, so the kernel has _one_ temporal read; `MEv.det`, `multi_domain_total`.
