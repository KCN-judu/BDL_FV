---
id: FVD-0121
legacy-id: D-121
status: accepted
date: 2026-09-20
phase: 13
area: surface
supersedes: []
superseded-by: []
related: []
production: [PRP-0001/audits]
---

# FVD-0121: Provision is a construction over designs, not a kernel construct

## Status

Accepted in Phase 13.

## Decision

`provision Δ P` writes a fresh unresolved `r : raw` and realizes each target by
`mk c (app tr (declRef r))` (or `app tr (declRef r)`); nothing enters `Core`.

## Alternatives rejected

A Source kind, an effect, a `Ty` constructor, a provision expression form.

## Reason

Every theorem (`provision_envRefines`, `provision_wf`, `provision_causal`,
`provision_wellClocked`, `provision_transparent`) is about the function on
`DeclEnv`.
