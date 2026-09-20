---
id: FVI-0005
legacy-id: OI-05
state: resolved
area: behavior
opened: 2026-09-15
resolved-by:
  [docs/reports/phase-08a-behaviour-as-a-first-class-design-object.md]
related: []
production: []
---

# FVI-0005: Reusable stateful components

## Problem

Reusable stateful components (function abstraction over `delay`)

## Resolution

Resolved in Phase 8a by instantiation: a component is a template instantiated
into fresh declarations, never a function over `delay`.
