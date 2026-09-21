---
id: FVD-0163
legacy-id:
status: accepted
date: 2026-09-21
phase: 21
area: surface
supersedes: [FVD-0161, FVD-0162]
superseded-by: []
related: [FVD-0007, FVD-0015, FVD-0020, FVD-0005, FVD-0118, FVD-0159]
production: [ADR-0034/bears-on, ADR-0032/bears-on, ADR-0041/bears-on]
---

# FVD-0163: The design objects are Sem blocks (declarations of a concept, one value each) and mapping blocks (their realizations); a concept is the type template Sem blocks are created from; a rule is the template mapping blocks apply; several Sem blocks of one concept are ordinary

## Status

Accepted in Phase 21; supersedes FVD-0161 and FVD-0162, which were **right on
their requirement until it was withdrawn**: they gave a concept a value so that
a concept block could be drawn and read as one. The owner's generational
proposal moves the value where the kernel has always kept it — in the
declaration — and draws that: the block is the Sem, the concept is its type.
FVD-0159's kernel reading (a concept is a nominal type; many declarations of it
are legal) is thereby restored with the projection corrected; it stays
superseded so that the chain records the path.

## Decision

1. **Sem block.** A Sem block is a `DesignDecl` whose expected type is `sem C`:
   an instance of the concept `C`, with one value per tick (`sem_value_det`).
   Its identity is the `DeclId`; its interface is the block; its realization,
   when present, is its producer.
2. **Mapping block.** The realization of a Sem block, drawn as a node: a rule
   applied to the Sem blocks it reads. A Sem block has at most one producer by
   construction (`producedBy_unique`), write-once under refinement
   (`producedBy_refine`, FVD-0007); a Sem block without a mapping block is
   provided by the environment (a Source, FVD-0118).
3. **Templates.** A concept (`ConceptId`, its representation in `Θ`, its display
   metadata) is the template a Sem block is created from; a rule (an arrow-typed
   declaration) is the template a mapping block applies. Two Sem blocks of one
   concept, two mapping blocks of one rule, are ordinary (`rule_template`,
   `sensors_natural`); nothing counts them.
4. **Edges.** A mapping block has one edge into its Sem block (`ProducedBy`) and
   one edge from each Sem block or rule it reads (`Reads` = `DependsOn`,
   FVD-0005). Relationships are never joined to relationships; a reference is
   `declRef` to a Sem block; nothing is resolved by concept, and no concept
   reference exists in the surface language.
5. **Phase 20's invariant is optional.** `ProducerUnique` — one Sem block per
   concept, relays not counting — is a judgment a design may require
   (`Validation/Producer.lean`), with its refinement and composition theorems;
   it is not a condition of well-formedness (`judgment_optional`). The concept
   reference `cref`/`elabS` is an experiment for designs under that judgment.

## Alternatives rejected

- **The concept block as the value node** (FVD-0161/0162): needs a global
  invariant, an elaboration and a definition of origin with edge cases (initial
  values, re-wraps); the Sem block has the value structurally.
- **A Sem object distinct from the declaration**: a second identity for one
  object; `DesignDecl` already is interface + write-once realization.
- **One Sem block per concept as a condition**: refuses the natural form of
  redundancy and of a rule applied twice.

## Reason

`producedBy_unique`, `producedBy_refine`, `producedBy_of_refine`,
`reads_iff_dependsOn`, `new_sem_transparent`, `sem_value_det`
(`Surface/Sem.lean`); `lamp_picture`, `rule_template`, `sensors_natural`,
`judgment_optional` (`Experiments/SemExamples.lean`). Each is a restatement of a
Phase 0–1, 5 or 13 theorem, which is the point: the reading adds nothing to the
kernel.

## Consequences

`kernel.md`'s concept paragraph is rewritten; `minimality.md` rows: producer
uniqueness per concept — validation, optional; concept reference — experiment;
Sem/mapping blocks — the kernel's declaration. Production: the canvas draws Sem
blocks and mapping blocks with the two edge kinds; the Concept sheet (ADR-0041)
is the template; the Simulate probe is per Sem block; no diagnostic for "two Sem
blocks of one concept" (note §5).
