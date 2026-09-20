---
id: FVI-0019
legacy-id: OI-19
state: resolved
area: surface
opened: 2026-09-15
resolved-by: [FVD-0014]
related: []
production: []
---

# FVI-0019: Display-name table for concepts

## Problem

Display-name table for concepts — surface; not modelled in core.

## Resolution

Resolved (2026-09-20) — duplicate of the display-name clause of FVI-0017 and
already decided: FVD-0014 keeps display names out of the kernel; they are
surface metadata separate from `SemanticId`, `DeclId` and type identity, and
production stores them as mutable documentation (`Concept.name`). No theorem
obligation exists; nothing to model.
