---
id: FVI-0026
legacy-id:
state: open
area: surface
opened: 2026-09-20
resolved-by: []
related: [FVI-0022]
production: [ISS-0017]
---

# FVI-0026: Atomic multi-value frames: per-tick batching, upstream product, or a many-to-one lowering

## Problem

One indivisible device frame carrying values from several independently
meaningful logical outputs (`oMode accepts Mode`, `oLevel accepts Level`; the
protocol refuses a partial frame). Phase 15 states the two representations the
current architecture offers — (A) two realizations whose operations the backend
commits in one tick (both sinks are set at every activation of the common clock,
`AdapterOp` per sink), (B) one upstream concept `Display accepts Mode × Level`
and one realization — and the criterion under which either fails: (A) fails if
the two outputs are in different clocks or the backend cannot batch; (B)
collapses two behaviour identities into one product the design may not mean.
Neither failure has a formal witness yet; `lowerMany` is not built (FVD-0136).

## Current evidence

Phase 14 report §14.2; FVD-0136 and its amendment; Phase 15 report §15.2.

## Dependencies

A device whose frame cannot be assembled by per-tick batching and whose values
the design does not want as one concept.

## Amendment (2026-09-20, Phase 16)

The paired axis (`YPosition` on two motors with prepare/prepare/commit) is not
an instance of this item: the design means one output, and the pair command or
two agreeing realizations carry it (FVD-0148, `paired_commands_of_one_value`).
The criterion — several independently meaningful outputs in one indivisible
frame — still has no witness.

## Resolution

Open.
