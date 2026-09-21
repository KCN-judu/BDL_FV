---
id: FVI-0030
legacy-id:
state: resolved
area: experiments
opened: 2026-09-21
resolved-by: [FVD-0161]
related: [FVI-0014]
production: []
---

# FVI-0030: A design-meaning notion of "origin" of a concept value, and a design that needs two origins of one concept

## Problem

Phase 19 defined origin syntactically: `MkProduces Δ d C` holds when `d`'s body
contains a `mk C` or `d` is an unresolved Source of `C`. Two facts show the
syntactic count is not the count a designer means: Phase 14's
`light := mk Brightness (rep dial)` is a second origin of what `dial` supplies
while the wire `light := dial` is not (`rewrap_counts_as_origin`), and a
transport's explicit initial value `sync c (mk C 0) x` is an origin while
`sync c 0 x` is not (`transport_second_signature`). A lint on `MkUnique`
(FVD-0160) therefore decides by the shape of the term. Whether a semantic,
term-shape-independent notion of origin exists — "the value flow of `C` from
outside the design or from a representation computation" — and whether it is
decidable, is not established.

Second, Phase 19 found for every alternative-producer use in the development an
explicit-resolution form with intermediate concepts and one origin, with the
same downstream trace on the executed designs (`sensors_rewriting_same_trace`,
`override_rewriting_same_trace`). No design that _needs_ two origins of one
concept — one that no such rewriting reproduces — was found. Its absence is
recorded here; impossibility is not claimed, and no general trace-preservation
theorem for the rewriting is proved.

## Current evidence

`BDL/Experiments/ProducerAlternatives.lean`: `MkProduces`, `MkUnique`,
`mkUnique_refine`, `rewrap_counts_as_origin`, `transport_second_signature`, the
two rewritings and `sensorsC_mkUnique`;
[Phase 19](../reports/phase-19-may-several-declarations-produce-one-concept.md)
§19.5 – §19.6.

## Dependencies

Nothing in the kernel: FVD-0159 stands whatever the answer, because no kernel
judgment consumes an origin count. An answer would change only what an authoring
lint may claim (FVD-0160) and whether the intermediate-concept guidance is
complete.

## Resolution

Resolved by
[FVD-0161](../decisions/161-each-concept-has-one-producer-producerunique-is-a-global-invariant-beside-singledriver.md)
(Phase 20). The origin count is fixed by decision: a `mk C` outside the
initial-value position of a `delay`/`sync`, or a Source (`Expr.originSet`); the
transport's initial value is the relay's default, and the re-wrap is written as
a wire. The necessity witness is moot: producer uniqueness is a global invariant
of the design, and a design that needs two origins of one concept is refused, as
one with two drivers of one output is. What remains unproved — a general
rewriting theorem — is recorded in the Phase 20 claim audit, not as an open
item.
