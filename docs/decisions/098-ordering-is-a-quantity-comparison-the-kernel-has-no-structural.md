---
id: FVD-0098
legacy-id: D-98
status: accepted
date: 2026-09-18
phase: 9c
area: core
supersedes: []
superseded-by: []
related: [FVD-0090]
production: [ADR-0025/supports, ADR-0026/supports]
---

# FVD-0098: Ordering is a quantity comparison; the kernel has no structural order

## Status

Accepted in Phase 9c.

## Decision

`lt` is `lt (d : Dim)` again (Phase-4 form); `Value.blt` is removed.

## Alternatives rejected

`lt` at every data type (9b) — `mode1 < mode2`, `None < Some x` and
lexicographic pairs/lists have no behaviour-design meaning and their order would
come from codes, constructor tags or `SemanticId`s (`lt_rejected`,
`min_mode_rejected`); a kernel `Ord` predicate on types (unnecessary: an ordered
concept compares as `lt d` on `rep`). An implementation's canonical order for
maps/serialization is not a language capability.
