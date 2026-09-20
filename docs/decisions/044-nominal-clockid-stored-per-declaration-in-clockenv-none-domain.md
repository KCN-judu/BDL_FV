---
id: FVD-0044
legacy-id: D-44
status: accepted
date: 2026-09-15
phase: 5
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0004/supports]
---

# FVD-0044: Nominal `ClockId`, stored per declaration in `ClockEnv Κ`; `none` = domain-agnostic pure mapping

## Status

Accepted in Phase 5.

## Alternatives rejected

Inferred domains (would make an unresolved declaration's domain depend on future
realizations — the Phase-1 signature-first property); domains by rate
(`equal_rate_not_same_domain`).

## Reason

Clients' validity depends on the producer's domain
(`clock_change_invalidates_clients`), so the domain is interface data and must
be declarable before realization.
