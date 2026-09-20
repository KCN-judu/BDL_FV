---
id: FVD-0015
legacy-id: D-15
status: accepted
date: 2026-09-14
phase: M
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0010/supports]
---

# FVD-0015: Kernel ontology migrated from holes to declarations

## Status

Accepted in Phase 1 (post-phase migration).

## Alternatives rejected

Treating an unresolved declaration as a syntactic hole (`HoleId`, `DesignHole`,
`holeRef`, `Spec.obligations`, …).

## Reason

Phase 1 showed (a) identity is used only as an environment key — ordinary
declaration identity, not a new abstraction (`EnvRefines_update`, REPORT §1.5);
(b) clients reference the _interface_ (`tyView` for typing, commitments for
validation), never a syntactic position — nothing in the kernel object records
where a reference occurs; (c) unresolvedness is exactly `realization = none`.
The hole vocabulary therefore described a concept the model never contained.

## Consequences

Kernel names are `DeclId`, `DesignDecl`, `DeclEnv`, `declRef`, `DeclInterface`
(with `commitments`), `DeclLeq`/`DeclRefines`, `WellFormedDecl`. "Hole" remains
available only as a surface/HCI metaphor for a declaration whose realization is
absent. No aliases retained.

## Verification

Mechanical rename compiled with zero proof edits; declaration inventory
identical modulo the rename map (REPORT §M).
