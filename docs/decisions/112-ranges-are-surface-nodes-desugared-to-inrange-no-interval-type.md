---
id: FVD-0112
legacy-id: D-112
status: accepted
date: 2026-09-18
phase: 11
area: surface
supersedes: []
superseded-by: []
related: []
production: [ADR-0028/supports]
---

# FVD-0112: Ranges are surface nodes desugared to `inRange`; no interval type or value

## Status

Accepted in Phase 11.

## Decision

`x in lo .. hi ↦ inRangeF o x lo hi` under the 9c order policy; bounds must have
the value's (nominal) type (`range_bounds_forced`); a concept value against
representation bounds goes through `rep`.

## Alternatives rejected

An `Interval` type; ranges as data.

## Reason

No case stores, passes, lists or compares a range.
