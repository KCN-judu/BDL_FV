---
id: FVD-0055
legacy-id: D-55
status: accepted
date: 2026-09-15
phase: 6
area: core
supersedes: []
superseded-by: []
related: [FVD-0007]
production: [ADR-0005/supports]
---

# FVD-0055: First binding is a refinement; rebinding is an edit; a second driver is invalid

## Status

Accepted in Phase 6.

## Decision

`first_output_binding_is_monotone` (side condition: the sink is undriven),
`second_binding_invalid`, `rebinding_invalidates_design`. Same write-once
philosophy as realizations (FVD-0007) with one global side condition.
