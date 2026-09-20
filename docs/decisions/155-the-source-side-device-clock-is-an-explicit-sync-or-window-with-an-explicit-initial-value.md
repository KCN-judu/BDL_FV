---
id: FVD-0155
legacy-id:
status: accepted
date: 2026-09-20
phase: 18
area: surface
supersedes: []
superseded-by: []
related: [FVD-0141, FVD-0152, FVD-0149]
production: [ISS-0016/bears-on]
---

# FVD-0155: The Source-side device clock is an explicit `sync` of the raw reading (or Phase 9a's window over it) into the Source's domain with an explicit initial value — supplied or unavailable, never fabricated

## Status

Accepted in Phase 18.

## Decision

A Source device that samples in its own domain `pc` is provisioned by
`provisionSync`: the raw reading unresolved in `pc`, the Source realized as
`tr (sync pc init r)` in its own domain; an occurrence-like Source by
`provisionWindow`: Phase 9a's five declarations over the raw reading, the
Source realized over `window`. The initial value is an explicit `InitRep`
under one of two policies — `supplied` (a profile-given raw value) or
`unavailable` (`none` at an optional raw type, read by the design as absence).

## Alternatives rejected

A hidden provider clock; a fabricated default reading; activation gated on the
first sample (a schedule does not read an input); a second occurrence crossing.

## Reason

`provisionSync_target`, `provisionSync_transparent`, `provisionSync_causal`,
`provisionSync_wellClocked`, `syncRealizeAt_typed`, `provisionSync_wf`,
`provisionWindow_target`; executed `exB_sampled`, `exB_unavailable`,
`exB_window_edges`, `exB_structure`.

## Consequences

The explicit initial value is the one principle both boundaries share
(`InitRep` in `lowerSync`, `syncBody` and `provisionSync`); FVI-0024's
remaining "initial representation" is that object's choice on the output side.
