---
id: FVD-0151
legacy-id:
status: accepted
date: 2026-09-20
phase: 17
area: surface
supersedes: []
superseded-by: []
related: [FVD-0125, FVD-0149]
production: [ISS-0016/bears-on]
---

# FVD-0151: Several raw sources are several provisions; a merged batch is an explicit deterministic policy; no physical total order is assumed

## Status

Accepted in Phase 17.

## Decision

Deliveries from several raw sources before one activation are several raw
readings, one Phase-13 provision each, combined by the design. A provider that
merges them into one batch commits to an explicit deterministic policy —
`mergeBySource`, source order — and states it; the model invents no order.

## Alternatives rejected

An implicit total order across sources (no physical fact supplies one); a merge
left unspecified.

## Reason

`mergeBySource_interleaving`, `perSource_of_interleaving`: source order is an
interleaving, and any two interleavings agree on every source's subsequence — a
design that reads per source cannot tell the policies apart; only a design that
reads the merged order depends on it. Executed `exC_merge`.
