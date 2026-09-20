---
id: FVD-0147
legacy-id:
status: accepted
date: 2026-09-20
phase: 16
area: surface
supersedes: []
superseded-by: []
related: [FVD-0137, FVD-0139, FVD-0145]
production: [ADR-0036/supports, ISS-0017/bears-on]
---

# FVD-0147: Semantic admissibility (`OutputContract`, `InputContract`) and deployment feasibility (`Feasible`) are separate judgments; `Admissible` is their conjunction

## Status

Accepted in Phase 16.

## Decision

`OutputContract Θ accepts P` (the encoder typed `rep -> raw` under no grant and
fitting the accepted type; no board) and `Feasible H P` (the requirements
allocate on the board; no type) are distinct decidable judgments, and Phase 14's
`Admissible Θ accepts H P ↔ OutputContract Θ accepts P ∧ Feasible H P`
(`admissible_iff`). A profile check in a package or a catalogue must report the
two separately.

## Alternatives rejected

One admissibility predicate whose failure is reported as one fact (a profile
"not compatible" when the board lacks a peripheral); feasibility including
backend support (production's `adapter.profile_unsupported`) — a second
feasibility half that is data about a target family, noted for production and
not modelled.

## Reason

`admissible_iff` is definitional. `exQ_contract_not_feasible`
(`CommunicationExamples.lean`): the pair-command profile satisfies the contract
for `DesiredPos`, is feasible on the Nano and admissible; on a one-pin board it
satisfies the same contract, is not feasible and is not admissible — the
contract judgment did not change between the boards.
