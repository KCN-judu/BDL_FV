---
id: FVD-0148
legacy-id:
status: accepted
date: 2026-09-20
phase: 16
area: surface
supersedes: []
superseded-by: []
related: [FVD-0134, FVD-0136, FVD-0140, FVD-0143]
production: [ISS-0017/bears-on]
---

# FVD-0148: A paired axis is one logical output with a pair command, or two realizations that agree tick by tick; commit order is below the operation; no transaction primitive

## Status

Accepted in Phase 16.

## Decision

A device protocol of the shape _prepare motor 2, prepare motor 3, commit_ for
one semantic `YPosition` is realized as one logical output whose raw command is
a pair `(p, p)` (`pairEnc`, `exN_pair`), or as two realizations of the one
output whose commands are the two encoders' transfers of the one value the
output carries (`paired_commands_of_one_value`). The order of the frames within
the tick is the backend's per-tick commit, below `AdapterOp` (FVD-0140). No
transaction, batch or frame primitive is added.

## Alternatives rejected

A transaction primitive; a `lowerMany` for this case (FVD-0136 stands); a
product concept `Motor2 × Motor3` at the behaviour level (the design means one
axis; the split is the device's).

## Reason

`paired_commands_of_one_value` (`BDL/Surface/Assignment.lean`): under
`SingleDriver`, two realizations of one output at one tick specify
`R₁.E.transfer v'` and `R₂.E.transfer v'` for the one value `v` the output
carries. Executed: `exN_pair` (`(10, 10)` then `(40, 40)` at the sink),
`exN_two_motors` (identity encoders on two sinks agree).

## Consequences

FVI-0026 is not touched: the paired axis is one meaningful output by design
intent, not several independently meaningful outputs in one frame. The device's
need for a commit is the adapter's (FVI-0023).
