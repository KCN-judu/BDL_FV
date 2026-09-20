---
id: FVD-0150
legacy-id:
status: accepted
date: 2026-09-20
phase: 17
area: surface
supersedes: []
superseded-by: []
related: [FVD-0144, FVD-0149]
production: [ISS-0016/bears-on]
---

# FVD-0150: Deduplication is by transport identity below the boundary, never by payload; a retransmission is erased and a repeated command is not

## Status

Accepted in Phase 17.

## Decision

The provider keeps the transport identities it has delivered (`Seen`, adapter
state) and drops a delivery whose identity it has seen (`dedup`). Two deliveries
with distinct identities and equal payloads are two semantic occurrences. The
design never sees an identity.

## Alternatives rejected

Deduplication by payload (`Move(+10); Move(+10)` is two commands); the transport
identity in the Source's type (FVD-0144); deduplication in the design by
semantic id as the _only_ mechanism (it remains the design's option for semantic
identity, Phase 16 `exF_identity`, and is not the transport's).

## Reason

`dedup_of_fresh` (distinct identities all delivered), `dedup_retry`,
`run_retry`, `batch_retry`, `retry_invisible` (`BDL/Surface/Provider.lean`);
executed `exA_occurrences`, `exB_order`, `exB_all_ticks`, `exE_theorem`.
