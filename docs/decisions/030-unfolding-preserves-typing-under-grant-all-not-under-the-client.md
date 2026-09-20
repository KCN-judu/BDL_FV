---
id: FVD-0030
legacy-id: D-30
status: accepted
date: 2026-09-15
phase: 3
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0013/supports]
---

# FVD-0030: Unfolding preserves typing under `Grant.all`, not under the client grant

## Status

Accepted in Phase 3.

## Alternatives rejected

Pretending the flattened executable is semantically isolated.

## Reason

Each inlined `mk` was authorized at its own declaration (`constructs_granted`
per body); the executable is where isolation has been discharged. Recorded
honestly in `Unfolds.preserves_typing`.
