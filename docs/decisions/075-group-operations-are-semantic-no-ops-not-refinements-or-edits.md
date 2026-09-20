---
id: FVD-0075
legacy-id: D-75
status: accepted
date: 2026-09-16
phase: 8b
area: behavior
supersedes: []
superseded-by: []
related: []
production: [ADR-0019/supports]
---

# FVD-0075: Group operations are semantic no-ops, not refinements or edits

## Status

Accepted in Phase 8b.

## Decision

Every operation (`group`, `ungroup`, `addMember`, `removeMember`, `move`,
`merge`, `split`) is the identity on `design` (`group_is_identity_on_design`).
They are a fourth invalidation class below "validation-only": nothing is
rechecked.
