---
id: FVD-0157
legacy-id:
status: accepted
date: 2026-09-20
phase: 18
area: surface
supersedes: []
superseded-by: []
related: [FVD-0122, FVD-0124]
production: [PRP-0001/audits]
---

# FVD-0157: `computes` is proof-carrying: derived when the transfer function is the term's evaluation, decided at a finite raw type; a separately supplied transfer function is a claim about the term

## Status

Accepted in Phase 18.

## Decision

The Phase-13 obligation stays a proof. `Channel.ofTerm` defines the transfer
function as the term's evaluation and derives `computes` from the
interpreter's totality on typed inputs; `computesBool` decides the coherence
of a supplied function at `bool` (`computes_of_bool`, over
`Value.beq_sound`). At an infinite raw type a supplied function is a claim
to test; production compiles the term, so nothing beyond the compiler is
trusted.

## Alternatives rejected

A boolean "trusted" field; a proof language for transfer functions.

## Reason

`Channel.ofTerm`, `Machine.ofTerm`, `computesBool`, `computes_of_bool`;
executed `exD_ofTerm`, `exD_bool`.
