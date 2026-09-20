---
id: FVD-0029
legacy-id: D-29
status: accepted
date: 2026-09-15
phase: 3
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0013/supports]
---

# FVD-0029: Representation binding is a separate, write-once concept environment `Θ`

## Status

Accepted in Phase 3.

## Alternatives rejected

Storing the binding in `DeclInterface`; indexing `Ty.sem` by the representation
(`Sem[n,d]`).

## Reason

A concept is a type, not a declaration (Phase 2, Model C); the binding is
deferred like a realization (`unbound_concept_still_wires`), monotone to bind
(`HasType.mono_concept`, `GlobalWF.of_conceptRefines`), and an edit to change
(`representation_change_is_edit_not_refinement`, both forms). Typing reads `Θ`
only through `Θ s = some R`. **Consequence (major):** typing now consults two
environments — `Δ.tyView` and `Θ` — plus a grant. `tyView` itself is unchanged.
The brief's `HasType` / `Realizes` split is realized as one judgment family
indexed by the grant.
