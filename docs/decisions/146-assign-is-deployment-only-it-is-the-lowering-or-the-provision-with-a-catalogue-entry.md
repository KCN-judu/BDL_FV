---
id: FVD-0146
legacy-id:
status: accepted
date: 2026-09-20
phase: 16
area: surface
supersedes: []
superseded-by: []
related: [FVD-0121, FVD-0132, FVD-0145]
production: [ISS-0016/bears-on, ISS-0017/bears-on]
---

# FVD-0146: `assign` is deployment-only: it is the lowering or the provision with a catalogue entry, and edits no behaviour

## Status

Accepted in Phase 16.

## Decision

A deployment operation `assign <output> using <entry>` is
`assignOutput Δ en o d p e spec := lowerΔ Δ (en.realization o d p e) spec`;
`assign <source> using <entry>.channel i` is
`assignSource Δ en i r s clock := provision Δ (Provision.one r s clock ch)` for
the entry's `i`-th channel. Assignment selects provision or realization
evidence and deployment structure; it adds no construction of its own.

## Alternatives rejected

An `assign` that rewrites the driver, the output's accepted type or the
Source's interface (Model A, refuted in Phase 14); an assignment recorded in
the design graph.

## Reason

`assignOutput_behavior_unchanged` (the design is literally the same off the
fresh encoder identity — `behavior_unchanged`), `assignOutput_transparent`
(`lower_transparent`), `assignOutput_checked` (the assigned design is accepted
by the unchanged judgments: `lower_wf`, `lower_causal`, `lower_wellClocked`,
`lower_driveWF`, `lower_singleDriver`), `assignSource_transparent`
(`provisionOne_transparent`) — `BDL/Surface/Assignment.lean`.

## Consequences

Production's `DeviceBinding.realization` (ADR-0036) is an output assignment;
the Source binding ISS-0016 asks for is a Source assignment; both are
deployment data in the device body, never in the design.
