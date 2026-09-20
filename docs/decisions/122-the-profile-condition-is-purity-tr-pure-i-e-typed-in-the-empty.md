---
id: FVD-0122
legacy-id: D-122
status: accepted
date: 2026-09-20
phase: 13
area: surface
supersedes: []
superseded-by: []
related: []
production: [PRP-0001/audits]
---

# FVD-0122: The profile condition is purity: `tr.Pure`, i.e. typed in the empty design and delay-free

## Status

Accepted in Phase 13.

## Decision

`exD`: a term typed at `q0 -> q0` in the empty design with `delay` inside maps
the same raw value to different results at different ticks; typing is not
enough. `Channel.WF_refFree`, `pure_iff_delayFree_of_wf`.

## Alternatives rejected

"closed and well-typed" as the condition; stateful transducers in the first
version.

## Reason

The transfer must be a function of the raw reading for the induced input to be
defined and for `Transduces.mev` to hold.
