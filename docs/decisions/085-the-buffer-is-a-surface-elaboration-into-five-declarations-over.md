---
id: FVD-0085
legacy-id: D-85
status: accepted
date: 2026-09-17
phase: 9a
area: core
supersedes: []
superseded-by: []
related: []
production: [ISS-0001/bears-on]
---

# FVD-0085: The buffer is a surface elaboration into five declarations over `delay`/`sync`

## Status

Accepted in Phase 9a.

## Decision

`log @src := cons src (delay nil log)`, `logD @dst := sync src nil log`,
`seen := length logD`, `cursor := delay 0 seen`,
`window := reverse (take (seen − cursor) logD)`.

## Alternatives rejected

A buffer primitive; `Event τ`; a scheduler order; same-tick visibility.

## Reason

`buffer_window_correspondence` (Theorem M) — for every schedule, input, domain
and tick the window evaluates to the Phase-5 window exactly — with K/L for
typing and clocking. The Phase-5 `buffer_from_log_and_cursor` is reused.
