---
id: FVD-0036
legacy-id: D-36
status: accepted
date: 2026-09-15
phase: 4
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0004/supports, ADR-0016/supports]
---

# FVD-0036: `Signal` is not a type; `Event` is `opt`

## Status

Accepted in Phase 4.

## Alternatives rejected

`Ty.signal`, `Ty.event`.

## Reason

Under the tick semantics every declaration is a stream, so a signal type
distinguishes nothing; an event input is an `opt` stream by construction of
`Input`, and `event_encoding_equivalent` / `event_encoding_loses_multiplicity`
locate multiplicity in the cross-domain observation model (Phase 5).

## Claim strength

Engineering preference for `Signal`; equivalence by proof under the
single-domain model for `Event`.
