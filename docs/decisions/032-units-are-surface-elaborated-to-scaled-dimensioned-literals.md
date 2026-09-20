---
id: FVD-0032
legacy-id: D-32
status: accepted
date: 2026-09-15
phase: 3
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0028/supports]
---

# FVD-0032: Units are surface: elaborated to scaled dimensioned literals

## Status

Accepted in Phase 3.

## Alternatives rejected

Units in `Ty`.

## Reason

`unit_scaling_preserves_dimension`, `unit_change_is_value_not_type`; mixed-unit
addition works after elaboration. Affine units not modelled.
