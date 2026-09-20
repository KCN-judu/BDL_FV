---
id: FVD-0048
legacy-id: D-48
status: accepted
date: 2026-09-15
phase: 5
area: core
supersedes: []
superseded-by: []
related: []
production: [ISS-0001/bears-on]
---

# FVD-0048: Event transport = window read; buffering derived, `Event` still not a primitive

## Status

Accepted in Phase 5.

## Decision

`opt_loses_multiplicity_under_sync` rejects `sync` as an _event_ transport;
`buffer_from_log_and_cursor` derives the exact window from `sync` of a log and
`delay` of a cursor; `policies_lose_information` fixes what each policy keeps.

## Alternatives rejected

`Event τ` as a kernel type; a buffer primitive.

## Pending

`Ty.list` to write the buffer in the object language; capacity is validation.
