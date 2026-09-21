---
id: FVD-0162
legacy-id:
status: superseded
date: 2026-09-21
phase: 20
area: surface
supersedes: []
superseded-by: [FVD-0163]
related: [FVD-0161, FVD-0005, FVD-0011, FVD-0045]
production: [ADR-0034/bears-on]
---

# FVD-0162: A concept reference is a surface form that elaborates to a reference to the concept's producer; the kernel names declarations only, and the canvas draws both kinds of edge to the concept block

## Status

Accepted in Phase 20.

## Decision

The surface term language is the kernel's plus `cref C` (`ConceptRef.SExpr`).
Elaboration `elabS ids Δ` replaces `cref C` by `declRef d` where
`producerOf ids Δ C = some d`, and leaves the term open when no producer exists
yet. No kernel term names a concept (FVD-0005 stands: references are `declRef`
by `DeclId`). On the canvas a relationship's output socket connects only to the
concept it produces, and a relationship that reads a concept takes its edge from
that concept's block; relationships are not joined to relationships. A reader in
another clock domain reads the producer through a transport on the edge
(FVD-0045), which is a relay, not a producer.

## Alternatives rejected

- A kernel `cref`: evaluation would depend on `producerOf`, and every theorem
  over `Expr` would gain a case; the projection through elaboration keeps the
  kernel and is conservative (`elabS_embed`).
- Reference edges from relationship to relationship (ADR-0034's projection):
  correct under Model A, where a concept is only a type; under FVD-0161 the
  concept block is the value and the edge from it is the reference.

## Reason

`elabS_cref` (to the producer), `elabS_cref_none` (open before the producer
exists), `elabS_embed` (conservative), `elabS_congr` (depends on the design only
through `producerOf`), `elabS_refine` (stable under refinement), `valueOf_det`
(the value of a concept at a tick is determined); `read_by_concept` and
`temperature_value` executed on the Phase 19 sensor design.

## Consequences

The frozen Concept/Output projection resumes with the concept block as a value
node; production's `MappingAnalysis.references` (declaration identities) is what
an edge from a concept block elaborates to, so the wire format and the analysis
need no change — the projection draws the edge from `producerOf`'s concept
instead of from the declaration.
