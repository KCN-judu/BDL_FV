---
id: FVD-0089
legacy-id: D-89
status: accepted
date: 2026-09-17
phase: 9b
area: surface
supersedes: []
superseded-by: []
related: []
production: [ADR-0025/supports]
---

# FVD-0089: The list recursor `fold` is a term former, not a registered operator

## Status

Accepted in Phase 9b.

## Alternatives rejected

A `fold` primitive (operators never apply closures; a closure-applying operator
would need the evaluation relation inside `Prim.compute`); per-operation
primitives `map`/`any`/`all`/…; bounded unrolling.

## Reason

One eliminator derives every collection operation (`Stdlib`); evaluation is
syntactic unrolling through the environment (`Ev.foldCons`), so `Ev` stays an
ordinary inductive and every earlier proof extends by one case. Totality by
`fold_total`.
