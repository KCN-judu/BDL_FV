---
id: FVI-0001
legacy-id: OI-01
state: deferred
area: core
opened: 2026-09-14
resolved-by: []
related: [FVI-0015]
production: [ISS-0003]
---

# FVI-0001: Interface-level references

## Problem

Interface-level references (commitments that mention other declarations) —
needed before a full dependency graph is meaningful.

## Audit (2026-09-20, after Phase 14)

Production authors no commitments: every declaration's commitments are `[]` and
no commitment solver exists (production-correspondence.md, _Production facts_).
A commitment that mentions another declaration therefore has no production
instance to model. The question is genuine — the dependency graph is over
realizations only (`DependsOn`), and an interface-level reference would need its
own edge kind — but it is blocked on evidence: what such a commitment would say.
FVI-0015 (evidence invalidation under edits) is the same boundary — commitments
mention declarations, so evidence has dependencies and edits invalidate it
selectively — and is merged here.

## Resolution

Deferred (2026-09-20): blocked on production authoring a commitment that
mentions a declaration (ISS-0003). Merged with FVI-0015; one future phase, when
the first such commitment exists.
