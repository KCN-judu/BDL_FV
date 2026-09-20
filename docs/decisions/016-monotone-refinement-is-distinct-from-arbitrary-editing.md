---
id: FVD-0016
legacy-id: D-16
status: accepted
date: 2026-09-14
phase: M
area: core
supersedes: []
superseded-by: []
related: [FVD-0007]
production: [ADR-0009/supports]
---

# FVD-0016: Monotone refinement is distinct from arbitrary editing

## Status

Accepted in Phase 1 (post-phase migration).

## Decision

(Generalizes FVD-0007, which covered only detaching.) Refinement steps — the
only operations covered by the preservation theorems — are: realize an
unresolved declaration; add public commitments; strengthen an interface while
preserving the expected type; strengthen a realized declaration with
re-verification.

## Not refinement

Changing the expected type (probe 4), removing a commitment (probe 5), detaching
a realization (FVD-0007), replacing a realization, changing identity (probe 3).
These are ordinary _edits_: they may invalidate transitive dependents and
require rechecking/revalidation.

## Alternatives rejected

Formalizing a general edit relation now.

## Reason

Nothing in Phases 0–1 needs it; the counterexamples already show what each edit
breaks. Revisit when a phase needs invalidation tracking.
