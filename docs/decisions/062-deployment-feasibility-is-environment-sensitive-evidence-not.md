---
id: FVD-0062
legacy-id: D-62
status: accepted
date: 2026-09-15
phase: 7
area: validation
supersedes: []
superseded-by: []
related: []
production: [ADR-0006/supports, ADR-0015/supports]
---

# FVD-0062: Deployment feasibility is environment-sensitive evidence, not `Evidence.Monotone`

## Status

Accepted in Phase 7.

## Decision

`feasibility_not_monotone_under_extension`: a monotone design extension can
falsify it. Phase 1's stable/sensitive distinction is realized as two layers
that are never merged.
