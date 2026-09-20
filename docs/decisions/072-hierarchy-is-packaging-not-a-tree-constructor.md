---
id: FVD-0072
legacy-id: D-72
status: accepted
date: 2026-09-15
phase: 8a
area: behavior
supersedes: []
superseded-by: []
related: []
production: [ADR-0021/supports, ADR-0022/supports]
---

# FVD-0072: Hierarchy is packaging, not a tree constructor

## Status

Accepted in Phase 8a.

## Alternatives rejected

An inductive `BehaviorSystem` tree with offset threading.

## Reason

A flattened system is a design over identities `< flatWidth`, hence a template
(`toComponent`); nesting is instantiating packages. The `Realizes` proof for a
package is a decidable side condition, not yet discharged.
