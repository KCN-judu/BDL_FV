---
id: FVD-0022
legacy-id: D-22
status: accepted
date: 2026-09-15
phase: 2
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0013/supports]
---

# FVD-0022: Explicit semantic mappings are ordinary declarations

## Status

Accepted in Phase 2.

## Alternatives rejected

A kernel conversion relation, coercion, cast, or subtyping.

## Reason

`tiltToMotor : sem tilt → sem motor` is a _design relationship_ between
concepts, not a representation conversion. As a declaration it is already
signature-first, may remain unresolved, and makes the mapping visible in every
term that uses it (`explicit_semantic_mapping_accepted`).

## Terminology

"explicit semantic mapping"; the words conversion / coercion / cast are reserved
for representation-level mechanisms, none of which exist in the Phase-2 kernel.
