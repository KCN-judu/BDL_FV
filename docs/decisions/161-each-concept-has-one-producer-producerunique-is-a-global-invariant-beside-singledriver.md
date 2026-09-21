---
id: FVD-0161
legacy-id:
status: accepted
date: 2026-09-21
phase: 20
area: core
supersedes: [FVD-0159, FVD-0160]
superseded-by: []
related: [FVD-0019, FVD-0020, FVD-0038, FVD-0052, FVD-0053, FVD-0068, FVD-0162]
production: [ADR-0034/bears-on, ADR-0032/bears-on]
---

# FVD-0161: Each concept has one producer — `ProducerUnique` is a global invariant beside `SingleDriver`; an origin is a construction outside initial-value positions or a Source; a shared concept is originated by at most one instance

## Status

Accepted in Phase 20; supersedes FVD-0159 and FVD-0160. Those two were **right
on their evidence**: Phase 19 showed that no kernel judgment consumed a producer
count and that the count was syntactic, and concluded that uniqueness bought
nothing. What changed is not the evidence but the requirement: the owner fixed
the design reading of a concept — _one product quantity, one value per tick, one
producer_ — and asked for the consumer Phase 19 found missing: a formula and a
canvas edge that name the concept and mean its value (FVD-0162). Under that
requirement the count has a purpose, and the syntactic edge cases are settled
here by definition.

## Decision

1. **The invariant.** `ProducerUnique Δ`: for every concept `C`, at most one
   declaration `d` with `Produces Δ d C`. It is a global judgment of a design,
   checked beside `SingleDriver` (FVD-0052) and never a typing rule; `Ty`,
   `Expr`, `HasType`, `Ev`/`MEv` and the grant are unchanged. A design with two
   producers of one concept is rejected as a design with two drivers of one
   output is.
2. **What an origin is.** `Produces Δ d C` holds when `d`'s body constructs `C`
   — a `mk C` — **outside the initial-value position** of a `delay` or a `sync`
   (`Expr.originSet`), or when `d` is unresolved with `C` in result position (a
   Source). A wire, a transport, a memory, a selection over references originate
   nothing: they relay. The explicit initial value of a transport or a memory is
   the relay's default, mandatory by FVD-0038, and not a producer; Phase 14's
   re-wrap `light := mk Brightness (rep dial)` _is_ a second producer and is
   written as the wire `light := dial`.
3. **Under composition.** A shared concept is originated by at most one
   instance, and by one declaration of it, where a required port or a parameter
   counts as no origin (`ExternalSingleProducer`, the concept analogue of
   `ExternalSingleDriver`); every required port and parameter is bound
   (`PortsBound`); internal concepts are freshened per instance. Two instances
   of one component that share a provided concept are refused; the concept is
   made instance-private, or one instance provides it.
4. **The form of alternatives.** Candidates for one concept are their own
   concepts (`SensorA`, `SensorB`, `EmergencyTarget`, `NormalTarget`,
   `BaseAngle`, `Correction`), and the one declaration that selects, blends or
   composes them is the concept's producer — Phase 6's principle "many
   contributors, one explicit final driver" (FVD-0053) with the contributors
   named.

## Alternatives rejected

- **Model A (FVD-0159)**: many producers legal. Consistent, but "the value of
  `C`" has no denotation (`two_C_values_coexist`) and a concept block on the
  canvas is a type, not a value; the reading the owner requires is unavailable.
- **Counting initial values** (Phase 19's `MkProduces`): every transported
  concept value becomes a second origin (`transport_second_signature`); with
  FVD-0038 no cross-domain concept could satisfy the invariant.
- **Uniqueness as a typing condition**: `HasType` is per declaration; the
  invariant is global like `SingleDriver`, and typing needs no change.
- **A resolver primitive**: the resolver is an ordinary declaration
  (`composition_unique`, `priority_unique`); Phase 19's finding stands.

## Reason

`ProducerUnique.refine`, `producerOf_refine`: preserved by refinement, the
producer does not move. `ProducerUnique.update_relay`: realizing with a relay
preserves it. `flatten_producerUnique` (and `_of_composeWF`, `_ofB`): preserved
by flattening under the boundary rule. `elabS_cref`, `valueOf_det` (FVD-0162):
what the invariant buys. The rewritten designs `composition_unique`,
`priority_unique`, `rewrap_unique`, `private_lamp_unique` with the same executed
traces; `transport_unique` for the initial-value definition.

## Consequences

`kernel.md` gains the invariant beside `SingleDriver`; `minimality.md` rows
"producer uniqueness per concept" (kernel: yes) and "resolver primitive" (no).
Phase 19's report §19.5 clock-domain line struck (the definition changed);
FVI-0030 resolved. Production: the Concept/Output projection may resume with the
concept block as a value node and both kinds of edge ending at concept blocks;
an authoring check "concept `C` has two producers" becomes a diagnostic of the
design, not a lint (note § 5).
