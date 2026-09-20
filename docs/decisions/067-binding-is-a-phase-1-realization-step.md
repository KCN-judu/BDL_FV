---
id: FVD-0067
legacy-id: D-67
status: accepted
date: 2026-09-15
phase: 8a
area: behavior
supersedes: []
superseded-by: []
related: []
production: [ADR-0021/supports, ADR-0022/supports]
---

# FVD-0067: Binding is a Phase-1 realization step

## Status

Accepted in Phase 8a.

## Alternatives rejected

A binding relation in the kernel; substitution of the source body into the
destination.

## Reason

`binding_satisfies` + `local_refinement_preserves_global_wf` give Theorem C/D
for free; write-once realization means a port is bound at most once
(`dstNodup`). Transport bindings elaborate to `sync` with an explicit initial
value (Phase 5); the source must be clocked.
