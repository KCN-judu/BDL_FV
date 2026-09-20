---
id: FVD-0136
legacy-id:
status: accepted
date: 2026-09-20
phase: 14
area: surface
supersedes: []
superseded-by: []
related: [FVD-0125]
production: []
---

# FVD-0136: The singleton output realization is primitive; a shared device batches per tick or is combined upstream

## Status

Accepted in Phase 14.

## Decision

`Realization` realizes one logical output by one encoder into one machine sink. A device that consumes several logical outputs at once is either (a) several machine sinks committed in the same tick — the runtime already commits all outputs of a domain together — or (b) one concept combined upstream in the behaviour (an H-bridge takes one `MotorSpeed = (forward?, magnitude)` and emits `(duty, direction)`, `exD_hbridge`), never (c) a many-to-one lowering primitive.

## Alternatives rejected

`lowerMany` (several drivers → one encoder → one sink) as the primitive, by analogy with Phase 13's shared raw reading.

## Reason

The analogy fails: a raw *reading* physically arrives as one image and the split is real, so shared-raw provision had to be primitive (FVD-0125); a device *frame* is assembled by the machine from values the behaviour already produces separately, and Phase 6 already places every combination of several behaviours into one target upstream of a single drive edge (Counterexample B). `lower_comm` shows independent singleton realizations compose in any order to one design. Whether an *atomic* multi-value frame ever forces a construction is FVI-0022.
