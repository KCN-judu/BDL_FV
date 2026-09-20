---
id: FVD-0018
legacy-id: D-18
status: accepted
date: 2026-09-14
phase: M
area: core
supersedes: []
superseded-by: []
related: []
production: [ISS-0003/bears-on]
---

# FVD-0018: `Evidence.Monotone` is a stability condition, not a definition of validity

## Status

Accepted in Phase 1 (post-phase migration).

## Decision

Documentation correction. Monotonicity is required of evidence intended to
_survive_ monotone environment refinement. Environment-sensitive evidence that
is rechecked on every change is a legitimate future category and is not excluded
by the kernel; it is simply not covered by
`local_refinement_preserves_global_wf`.
