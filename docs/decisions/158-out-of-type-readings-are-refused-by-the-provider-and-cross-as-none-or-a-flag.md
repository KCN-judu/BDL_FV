---
id: FVD-0158
legacy-id:
status: accepted
date: 2026-09-20
phase: 18
area: surface
supersedes: []
superseded-by: []
related: [FVD-0149, FVD-0150]
production: [ISS-0016/bears-on]
---

# FVD-0158: An out-of-type reading is refused by the checking provider and crosses as `none` at an optional Source or as a flag — semantic state if the product reacts, a backend diagnostic if not; no exception semantics

## Status

Accepted in Phase 18.

## Decision

`checkedProvide` validates every delivery before deduplication and the bound and
flags refusals; delivered items satisfy the validation and are typed by
construction. A malformed frame, a NaN, an invalid code, an out-of-range count
are provider refusals; a raw type that does not fit is deployment invalidity;
what the design must react to is `opt` or a flag.

## Alternatives rejected

Exception semantics; silent coercion; a malformed value entering as a default.

## Reason

`checked_items_ok`, `checked_typed`, `checked_refused_iff`; executed
`exE_checked`, `exC_provider_checks`.
