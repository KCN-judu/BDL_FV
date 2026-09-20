---
id: FVD-0077
legacy-id: D-77
status: accepted
date: 2026-09-16
phase: 8b
area: behavior
supersedes: []
superseded-by: []
related: []
production: [ADR-0019/supports]
---

# FVD-0077: Boundary inference: required = crossing-in, provided = crossing-out, private = the rest without a sink, clocks = all clocks

## Status

Accepted in Phase 8b.

## Alternatives rejected

Required = all member references (Counterexample 1); required = own open
declarations only (Counterexample 2); no clock parameters (Counterexample 3).
Physical sinks are never semantic ports (Counterexample 4); the drive edge stays
with the member.
