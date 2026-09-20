---
id: FVD-0080
legacy-id: D-80
status: accepted
date: 2026-09-16
phase: 8b
area: behavior
supersedes: []
superseded-by: []
related: []
production: [ADR-0019/supports]
---

# FVD-0080: Template realization needs interface-local evidence

## Status

Accepted in Phase 8b.

## Decision

`Evidence.InterfaceLocal`: a discharged commitment depends only on the
interfaces of the referenced declarations. Without it a member's commitment
discharged in the whole design could not be carried into the template, where its
dependencies are unresolved port copies.
