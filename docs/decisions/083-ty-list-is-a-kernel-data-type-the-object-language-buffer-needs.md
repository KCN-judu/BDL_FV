---
id: FVD-0083
legacy-id: D-83
status: accepted
date: 2026-09-17
phase: 9a
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0024/supports]
---

# FVD-0083: `Ty.list τ` is a kernel data type; the object-language buffer needs it and nothing else

## Status

Accepted in Phase 9a.

## Alternatives rejected

`latest` (Model A), `count` (B), `coalesce μ` (C), a fixed tuple (D) as the
transported representation — each identifies distinct windows
(`latest_not_lossless`, `count_not_lossless`, `sum_not_lossless`,
`modelD_not_lossless`); every summary bounded to the newest `k` entries is lossy
(`bounded_summary_not_lossless`).

## Reason

Phase 5 showed multiplicity and order observable; a lossless summary is
injective and therefore unbounded.

## Claim strength

The list is the smallest general sequence representation _tested_, not the only
possible one.
