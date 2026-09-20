---
id: FVD-0140
legacy-id:
status: accepted
date: 2026-09-20
phase: 15
area: surface
supersedes: []
superseded-by: []
related: [FVD-0134, FVD-0133]
production: [ADR-0037/supports]
---

# FVD-0140: The adapter boundary is a policy, an abstract sink operation and a line, below the raw command and outside the behaviour

## Status

Accepted in Phase 15.

## Decision

The formal model extends one boundary beyond `RawCommand`: a `Policy` (`Value → Option Value`, the adapter's reading of a command, partial by design), the operation `Op = set m | refused | held` and the relation `AdapterOp` (gated by the output's clock activation, over the unchanged design), and the line `Line` as a fold over operations (start value, then the last accepted command). Reject-and-hold is a property of the fold, not of the encoder. Production's numeric policy is modelled mathematically (`duty8` on naturals); its `f64` rounding stays production's.

## Alternatives rejected

The policy or the hold inside the encoder (the encoder is a function of the current value, FVD-0133); an effect or an adapter primitive in `Core`; the `f64` rounding in the kernel; modelling the HAL or the register.

## Reason

`AdapterOp.det`, `adapter_of_sink` / `sink_of_adapter` (the operation is determined by the lowered sink's value: `lower_correspondence` carried one step), `adapter_downstream`, `Line.det`, `line_holds_on_refusal`, `line_holds_when_inactive`, `line_value_accepted`; executed `exA`–`exC`. Production's `AdapterOp`, `duty8` and `TickTrace.adapter` (ADR-0037) are the objects these mirror.
