---
id: FVD-0020
legacy-id: D-20
status: accepted
date: 2026-09-15
phase: 2
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0013/supports]
---

# FVD-0020: `ConceptId` is independent of `DeclId` and of display names

## Status

Accepted in Phase 2.

## Alternatives rejected

Deriving concept identity from a declaration id (Model C) or from the surface
name (Counterexample C, `rename_under_name_identity_breaks_client`).

## Reason

A concept is a type, a declaration is a value; names are renameable.

## Consequences

Three distinct things — internal identity (`ConceptId`), display name (surface
`Concept.name`), representation (`ρ : ConceptId → Ty`, used only by erasure in
Phase 2).
