---
id: FVD-0017
legacy-id: D-17
status: accepted
date: 2026-09-14
phase: M
area: core
supersedes: []
superseded-by: []
related: []
production: [ISS-0003/bears-on]
---

# FVD-0017: Commitments and validation obligations share `PropertyId` for now

## Status

Accepted in Phase 1 (post-phase migration).

## Decision

The field is named `commitments` because, from a dependent's perspective, these
are public promises; the validation layer turns each into a proof obligation to
discharge.

## Alternatives rejected

A separate obligation datatype.

## Reason

No phase yet distinguishes them operationally; introducing the split before
Phase 11 would be speculative.
