---
id: FVD-0133
legacy-id:
status: accepted
date: 2026-09-20
phase: 14
area: surface
supersedes: []
superseded-by: []
related: [FVD-0122, FVD-0124]
production: [ADR-0005/supports]
---

# FVD-0133: An encoder is pure, consumes the representation, and constructs nothing

## Status

Accepted in Phase 14.

## Decision

`Encoder.encode : rep -> raw` is `Expr.Pure` and typed in the empty design under `Grant.none` (`Encoder.WF`); at a semantic output the lowering applies it to `rep (declRef d)` — the driver's representation, observed without a grant — and the encoder declaration is typed at `raw`, a sem-free data type that grants nothing. `Encoder` carries `transfer` beside `encode` with `computes`, as Phase 13's `Channel` does, so that the command trace can be named without a choice principle.

## Alternatives rejected

"Closed and well-typed" as the condition (`exEFG`: `(λk. λn. k) (delay 0 1)` is typed at `q₀ -> q₀` and tick-dependent); an encoder granted the target concept or any other (`λx. mk Other x` refused under `Grant.none`, accepted only under `Grant.of (sem Other)`, which no encoder has); an encoder consuming the concept value directly (it would need to be a mapping on `sem c`, which is the behaviour's business, not the device's).

## Reason

`encoder_constructs_nothing` (from `constructs_granted`), `encoder_decl_no_grant` / `grant_of_semFree_data`, `Encoder.WF_refFree`, `encoderBody_typed`; purity is what makes `Transduces.mev` transport the encoder's evaluation (`encoder_value`) and keeps the causality edge set to `e -> d` (`lower_causal`).
