---
id: FVD-0059
legacy-id: D-59
status: accepted
date: 2026-09-15
phase: 7
area: validation
supersedes: []
superseded-by: []
related: []
production: [ADR-0006/supports, ADR-0015/supports]
---

# FVD-0059: Requirements are independent variables with nominal `RequirementId`, optional fixed resource, optional unit relation

## Status

Accepted in Phase 7.

## Alternatives rejected

Reusing `DeclId`/`OutputId` (one sink ⇒ several requirements); composite
peripheral requirements (independent + `same` unit suffices); pins as `OutputId`
(swapping boards must not change the design).
