---
id: FVD-0134
legacy-id:
status: accepted
date: 2026-09-20
phase: 14
area: surface
supersedes: []
superseded-by: []
related: [FVD-0119, FVD-0132]
production: [ADR-0016/supports]
---

# FVD-0134: The machine boundary is the `RawCommand` relation; no effectful `R -> ()` term exists

## Status

Accepted in Phase 14.

## Decision

The behaviour semantics ends at `RawCommand S Δ I Ω β R t w`: the command sink `p` receives at tick `t`. The backend — a PWM write, a GPIO write, an I²C transaction, a UART send — consumes it outside the formal semantics. No `Expr.write`, `Expr.effect`, `Ty.effect`, `Action`, `IO`, effect row or unit-returning consumer is added.

## Alternatives rejected

A pure `R -> ()` as the physical sink (Phase 12 `consumers_indistinguishable`: it cannot name a receiver); an effect type; "validation performs the side effect".

## Reason

`RawCommand.det` (a function of the tick under `SingleDriver`); `lower_correspondence` (the lowered design's machine sink carries exactly it). Nothing downstream of it is modelled, and nothing upstream needs it.

## Consequences

The future theorem boundary is stated, not claimed: abstract output trace → encoded raw command trace (proved) → generated backend call trace (open, FVI-0022).
