---
id: FVD-0093
legacy-id: D-93
status: accepted
date: 2026-09-17
phase: 9b
area: surface
supersedes: []
superseded-by: []
related: []
production: [ADR-0025/supports]
---

# FVD-0093: Constraints: the closed vocabulary {Data}; no user-defined classes

## Status

Accepted in Phase 9b.

## Alternatives rejected

Hardcoded per-operator admissibility (subsumed), an open class system,
dictionary passing.

## Reason

`eq`, `lt`, `delay`, `sync` are the only constrained operations and all need
exactly `Data`; a designer's custom order is a comparator argument (`minByF`).
Dimension genericity is a pattern variable over `Dim` (`PDim.dvar`); no kind
system.
