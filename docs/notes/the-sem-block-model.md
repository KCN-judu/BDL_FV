---
kind: note
phase: 21
area: surface
date: 2026-09-21
status: current
---

# The Sem-block model

For production's authoring surface and for the papers: the generational reading
of the design objects. Report:
[Phase 21](../reports/phase-21-sem-blocks-and-mapping-blocks.md); decision
FVD-0163; Lean: `BDL/Surface/Sem.lean`, `BDL/Experiments/SemExamples.lean`.
Replaces § 5 of [one-producer-per-concept.md](one-producer-per-concept.md) and
of [concepts-and-their-producers.md](concepts-and-their-producers.md).

## 1. The question and the answer

What is a block on the canvas? **A Sem block** — a declaration of a concept,
holding one value per tick — **or a mapping block**, the realization attached to
a Sem block, which is its one producer. A **concept** is the type template Sem
blocks are created from; a **rule** is the template mapping blocks apply.
Several Sem blocks of one concept are ordinary; each has one producer by
construction; a mapping reads Sem blocks, never "the concept". This is what the
kernel has been since Phase 1; only the projection changes.

## 2. What is proved

Every theorem on `propext`/`Quot.sound`, each a restatement of an earlier
phase's theorem: `producedBy_unique` (one producer per Sem block),
`producedBy_refine` / `producedBy_of_refine` (write-once; a producer never
arrives from elsewhere), `reads_iff_dependsOn` (read edges are the kernel's
dependency), `new_sem_transparent` (creating a Sem block changes no value),
`sem_value_det` (one value per tick). Executed: the canvas of the brief
(`lamp_picture`), a rule applied twice (`rule_template`), redundant sensors in
their natural form (`sensors_natural`), Phase 20's judgment as an option
(`judgment_optional`).

## 3. What is not established

Nothing new is claimed. Phase 20's open points (a general rewriting theorem,
`hbound` from `ComposeWF`) now concern an optional judgment.

## 4. Verdicts

Sem block, mapping block, concept template, rule template — the kernel's
declaration, read as such; `Surface/Sem.lean` the projection. `ProducerUnique` —
validation, optional. `cref`/`elabS` — experiment.

## 5. Production guidance

Each line is a _design recommendation_ unless marked.

- **Blocks.** Two kinds: a **Sem block** (a `mapping s : () -> C` in the text —
  a value declaration; a Source when it has no definition, ADR-0032) and a
  **mapping block** (its definition, drawn as a node: a rule applied to Sem
  blocks). ADR-0034's three shapes map as: _value_ → Sem block with a mapping
  block; _Source_ → Sem block alone; _rule_ → a template in the library or the
  design, applied by mapping blocks, not a node of the value graph.
- **Edges.** Mapping block → its Sem block: one, the definition (`ProducedBy`;
  _informed by FV_: write-once, `producedBy_refine`). Sem block → mapping block:
  one per Sem block the definition reads (`Reads` = `references`, the existing
  `MappingAnalysis.references`). No edge joins two mapping blocks or two Sem
  blocks. Dragging a Sem block into a mapping block's input is a text edit of
  the definition (ADR-0028); the wire format and the analysis need no change.
- **The concept is a template.** The Concept sheet (ADR-0041's category →
  concept) creates the template; _create a Sem block of `Temperature`_ is the
  instantiation, as many times as the product has temperatures (`sensorA`,
  `sensorB`, `roomTemp`). A concept node no longer appears on the canvas; the
  concept is the block's hue, socket shape and header type.
- **A rule is a template too.** `clamp`, `dimByTilt : Tilt -> Brightness` apply
  in any number of mapping blocks; a mapping block is one application.
- **No diagnostic for "two Sem blocks of one concept".** Two temperatures are
  two Sem blocks; a mapping that needs one of them names it. Phase 20's "one Sem
  block per concept" is an opt-in check for a design that wants it
  (`ProducerUnique`, `flatten_producerUnique_ofB`), never a default.
- **Cross-domain**: a mapping block in another clock domain reads a Sem block
  through a transport on the edge (the register mark), as before.
- **Simulate**: the probe is per Sem block — one value per tick
  (`sem_value_det`); _Carried by_ disappears with the concept node.
- **Composition**: a component's provided port is a Sem block; two instances
  provide two Sem blocks of one concept, which is ordinary; the external
  single-driver rule for sinks stays as is.
