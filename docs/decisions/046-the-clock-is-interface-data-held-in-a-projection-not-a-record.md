---
id: FVD-0046
legacy-id: D-46
status: accepted
date: 2026-09-15
phase: 5
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0004/supports]
---

# FVD-0046: The clock is interface data held in a projection, not a record field

## Status

Accepted in Phase 5.

## Decision

The public interface is semantically `expectedType × commitments × clock`
(Counterexample E; frozen under refinement; edit to change). It is stored in
`Κ`, as the representation is stored in `Θ`, rather than in `DeclInterface`.

## Alternatives rejected

`Ty`-indexed clocks (`clocked_type_forces_polymorphism`). Folding `Κ` into the
record is churn, not semantics; deferred.
