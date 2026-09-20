---
id: FVI-0027
legacy-id:
state: deferred
area: surface
opened: 2026-09-20
resolved-by: []
related: [FVI-0022, FVI-0001]
production: [ISS-0017]
---

# FVI-0027: Output commitments and what an encoder must discharge

## Problem

If a logical output ever carries a commitment (a range, monotonicity), whether
the realization's declared transfer must discharge it — the output analogue of
FVD-0128.

## Current evidence

Production authors no commitments at all (production-correspondence.md); the
kernel's commitment machinery would make the theorem small once one exists.

## Dependencies

Production authoring a commitment on an output (blocked with FVI-0001).

## Resolution

Deferred (2026-09-20): no commitment exists to discharge; reopen with the first.
