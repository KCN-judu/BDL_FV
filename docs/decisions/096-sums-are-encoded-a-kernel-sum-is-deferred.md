---
id: FVD-0096
legacy-id: D-96
status: accepted
date: 2026-09-17
phase: 9b
area: surface
supersedes: []
superseded-by: []
related: []
production: [ISS-0005/bears-on]
---

# FVD-0096: Sums are encoded; a kernel `sum` is deferred

## Status

Accepted in Phase 9b.

## Decision

`enum LampMode { Off, Automatic, Manual(Brightness) }` is a tag paired with an
optional payload; `match` is conditionals on the tag (`exM`). A kernel `sum`
would need one more eliminator term former; deferred until a case needs
exhaustiveness beyond the encoding.
