---
id: FVD-0011
legacy-id: D-11
status: accepted
date: 2026-09-14
phase: 1
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0010/supports]
---

# FVD-0011: Semantics at Phase 1 is unfolding to a reference-free term

## Status

Accepted in Phase 1.

## Alternatives rejected

A denotational semantics with fixpoints.

## Reason

The paper's pure fragment has no general recursion (§4.5); unfolding is the
smallest semantics that distinguishes "well-typed partial" from "executable".

## Consequences

Every reference cycle is meaningless (`Unfolds.not_of_cyclic`). Revisit when
delay exists.
