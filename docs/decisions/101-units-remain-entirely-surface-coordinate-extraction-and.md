---
id: FVD-0101
legacy-id: D-101
status: accepted
date: 2026-09-18
phase: 10
area: surface
supersedes: []
superseded-by: []
related: []
production: [ADR-0028/supports]
---

# FVD-0101: Units remain entirely surface; coordinate extraction and quantity construction are elaborated quantity arithmetic

## Status

Accepted in Phase 10.

## Decision

`inUnit q u := div q (lit d scale(u))`,
`withUnit x u := mul x (lit d scale(u))`, `n u := withUnit n u`.

## Alternatives rejected

Runtime unit values (no case delays, syncs, stores or compares a unit), units in
`Ty` (`1 m` and `100 cm` would differ in type), a kernel conversion primitive
(`convert` is the composition: `convert_eq`, `convert_trans`).

## Reason

`inUnitE_typed`, `inUnitE_safe`, `withUnitE_typed`, `withUnitE_is_quantity`,
`unitOps_no_construction`.
