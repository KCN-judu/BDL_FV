---
id: FVD-0019
legacy-id: D-19
status: accepted
date: 2026-09-15
phase: 2
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0013/supports]
---

# FVD-0019: Semantic identity lives in the type: `Ty.sem : SemanticId → Ty`

## Status

Accepted in Phase 2.

## Alternatives rejected

_Rejected (with claim strength):_ (B-weak) a `semanticRole` field in
`DeclInterface` with a direct-wire checker — _tested design failure_: evaded by
η-expansion (`bweak_evaded_by_eta`), and a role change flips verdicts on
unchanged clients (`role_change_flips_unchanged_clients`), so the field would
have to be frozen exactly like the type. (B-strong) a compositional role
judgment — _engineering preference_: any sound checker must be compositional
over terms, i.e. of type-system strength; the tested role-per-subterm
formulation duplicates nominal typing with no observed benefit; the broader
family of compositional semantic analyses is not universally ruled out. (C)
concepts as _ordinary_ `DesignDecl`s with identity = `DeclId` — _tested design
failure_: category errors (`conceptC_usable_as_value`,
`conceptC_realizable_by_a_number`). A stratified concept sort is not rejected
but reintroduces an independent `SemanticId`.

## Consequences

`Ty` gains one constructor; `DeclInterface` and `tyView` are unchanged; all
Phase 0/1 theorems hold verbatim. This is the smallest mechanism among the
tested designs, not a proof that nominal typing is the only possible one.
