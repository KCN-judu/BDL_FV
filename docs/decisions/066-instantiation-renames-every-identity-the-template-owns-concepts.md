---
id: FVD-0066
legacy-id: D-66
status: accepted
date: 2026-09-15
phase: 8a
area: behavior
supersedes: []
superseded-by: []
related: []
production: [ADR-0021/supports, ADR-0022/supports]
---

# FVD-0066: Instantiation renames every identity the template owns; concepts and sinks are partitioned into internal (fresh) and global (shared)

## Status

Accepted in Phase 8a.

## Alternatives rejected

Identity by name; a global concept table per component; renaming globals.

## Reason

Counterexample 3 (`identity_renaming_aliases`, `internal_concept_not_shared`);
`Tilt` must be the same concept in every instance, a private accumulator concept
must not be. The encoding `W·(k+1)+n` is a device; only injectivity,
decodability, and disjointness from globals `< W` are used.
