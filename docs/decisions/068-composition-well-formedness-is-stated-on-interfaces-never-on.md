---
id: FVD-0068
legacy-id: D-68
status: accepted
date: 2026-09-15
phase: 8a
area: behavior
supersedes: []
superseded-by: []
related: []
production: [ADR-0021/supports, ADR-0022/supports]
---

# FVD-0068: Composition well-formedness is stated on interfaces, never on bodies

## Status

Accepted in Phase 8a.

## Reason

Substitutability (`substitute_composeWF`) is then a consequence of
`IfaceRefines`. The two conditions beyond existing judgments are `dstNodup` and
`ExternalSingleDriver` (Counterexample 5).
