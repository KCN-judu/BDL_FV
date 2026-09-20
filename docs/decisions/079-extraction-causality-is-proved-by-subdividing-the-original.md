---
id: FVD-0079
legacy-id: D-79
status: accepted
date: 2026-09-16
phase: 8b
area: behavior
supersedes: []
superseded-by: []
related: []
production: [ADR-0019/supports]
---

# FVD-0079: Extraction causality is proved by subdividing the original graph, not by `InstAcyclic`

## Status

Accepted in Phase 8b.

## Reason

A group with both inputs and outputs has instance edges both ways; `flat_causal`
uses the rank `2·rank` / `2·rank + 1`. Phase 8a's condition is recorded as too
coarse for extraction.
