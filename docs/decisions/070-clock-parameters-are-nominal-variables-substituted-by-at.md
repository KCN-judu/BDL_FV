---
id: FVD-0070
legacy-id: D-70
status: accepted
date: 2026-09-15
phase: 8a
area: behavior
supersedes: []
superseded-by: []
related: []
production: [ADR-0021/supports, ADR-0022/supports]
---

# FVD-0070: Clock parameters are nominal variables substituted by κ at instantiation; rates never enter

## Status

Accepted in Phase 8a.

## Alternatives rejected

Clock-indexed component types; frequency matching.

## Reason

`Clocked.rename` holds for any κ, including one that merges two parameters into
one system domain; mismatch without `sync` is rejected (Counterexample 2).
