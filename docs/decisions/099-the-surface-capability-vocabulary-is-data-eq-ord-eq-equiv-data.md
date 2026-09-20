---
id: FVD-0099
legacy-id: D-99
status: accepted
date: 2026-09-18
phase: 9c
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0025/supports, ADR-0026/supports]
---

# FVD-0099: The surface capability vocabulary is {Data, Eq, Ord}; Eq ≡ Data today; Ord is by declaration

## Status

Accepted in Phase 9c.

## Decision

`Poly.Cap`, `Scheme.caps`, `Ty.ordB O Θ`: quantities, and concepts the designer
declared ordered (`OrdDecl`) with a quantity representation. `Cap.eq_iff_data`
records the coincidence; `Cap.ord_data` that Ord ⇒ Data and not conversely.

## Alternatives rejected

User-defined classes, instance search, superclasses (no case); deriving order
from declaration/constructor order (enums included). Diagnostics name the
capability and the concept.
