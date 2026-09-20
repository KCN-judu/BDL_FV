---
id: FVD-0021
legacy-id: D-21
status: accepted
date: 2026-09-15
phase: 2
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0013/supports]
---

# FVD-0021: No introduction/elimination forms for semantic types in Phase 2

## Status

Accepted in Phase 2.

## Alternatives rejected

Adding `mk`/`rep` now.

## Reason

Distinctness needs only the nominal constructor. Without `mk`/`rep`,
`no_semantic_value_without_declaration` shows semantic values flow only through
declarations — the intended discipline. `mk`/`rep` are a representation binding,
needed to realize mappings by formulas, and belong with Phase 3 where the
representation is `Q[d]`.
