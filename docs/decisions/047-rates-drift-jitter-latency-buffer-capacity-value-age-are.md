---
id: FVD-0047
legacy-id: D-47
status: accepted
date: 2026-09-15
phase: 5
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0004/supports]
---

# FVD-0047: Rates, drift, jitter, latency, buffer capacity, value age are validation

## Status

Accepted in Phase 5.

## Decision

None affects `Clocked`, `MEv.det`, or `multi_domain_total`; a rate change alters
the induced schedule (observed values) but no client's well-formedness.
