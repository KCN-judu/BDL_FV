---
id: FVD-0031
legacy-id: D-31
status: accepted
date: 2026-09-15
phase: 3
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0011/supports, ADR-0013/supports]
---

# FVD-0031: Dimensions in `Ty` as `q d`; algebra in `Prim.ty`; no dimension rule

## Status

Accepted in Phase 3.

## Alternatives rejected

Dimensions as metadata or validation obligations (not formalized; engineering
preference — `mul`/`div` _produce_ dimensions, so any checker recomputes
inference); a dimension-specific typing rule (unnecessary — registered operators
carry their types).

## Reason

`dimension_mismatch_rejected`; the numeric baseline is erased dimensional typing
(`HasType.eraseDim`, `counterexampleB_baseline_accepts_length_plus_time`). `Dim`
is an exponent vector over three bases, chosen to keep proofs decidable.
