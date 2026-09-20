---
id: FVD-0054
legacy-id: D-54
status: accepted
date: 2026-09-15
phase: 6
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0005/supports]
---

# FVD-0054: Effect rows and action values rejected for this kernel

## Status

Accepted in Phase 6.

## Decision

Direct effect rows are `β` (`single_driver_iff_direct_rows_disjoint`);
propagated rows produce false positives
(`propagated_effect_rows_false_positive`); action values relocate the conflict
into a collector that must be a policy (`action_values_relocate_conflict`).

## Claim strength

The tested formulations add no rejection or expressive capability.
