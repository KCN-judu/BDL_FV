---
kind: note
phase: 20
area: core
date: 2026-09-21
status: current
---

# One producer per concept

For production's authoring surface — the Concept/Output projection that was
frozen during Phase 19 — and for the papers. It settles the reading of a
concept: **one product quantity, one value per tick, one producer**, and what
follows for the canvas, the checks and the naming of alternatives. Report:
[Phase 20](../reports/phase-20-one-producer-per-concept.md); decisions FVD-0161,
FVD-0162; Lean: `BDL/Validation/Producer.lean` (moved from `Core/` in Phase 21),
`BDL/Behavior/Producer.lean`, `BDL/Experiments/ConceptRef.lean` (moved from
`Surface/` in Phase 21), `BDL/Experiments/ProducerUniqueExamples.lean`.
Supersedes § 5 of
[concepts-and-their-producers.md](concepts-and-their-producers.md).

## Amendment (2026-09-21, Phase 21)

FVD-0163 supersedes FVD-0161/0162: the value block is the Sem block (a
declaration), several Sem blocks of one concept are ordinary, and
`ProducerUnique` is an optional judgment. The theorems of § 2 stand; § 5 is
replaced by [the-sem-block-model.md](the-sem-block-model.md) § 5.

## 1. The question and the answer

May several declarations produce values of one concept? **No, by design
decision** (FVD-0161): a concept has at most one _producer_ — a relationship
whose body constructs it, or a Source — and everything else that carries its
values (a wire, a transport with its initial value, a memory, a selection) is a
relay. The invariant is global, like the single driver of an output; it is
preserved by refinement and by composition under a boundary rule; and it gives a
concept a value: a formula may read the concept, and reads its producer
(FVD-0162).

## 2. What is proved

Every theorem on `propext`/`Quot.sound`.

- `ProducerUnique.refine`, `producerOf_refine`: realizing declarations never
  adds a producer and never moves one. `ProducerUnique.update_relay`: realizing
  with a relay keeps the invariant.
- `flatten_producerUnique`: a system of producer-unique templates, with every
  shared concept originated by at most one instance (ports not counting), every
  port bound and relaying bindings, flattens to a producer-unique design;
  `flatten_producerUnique_ofB` decides it by one Boolean over the templates'
  declaration lists.
- `elabS_cref`, `elabS_embed`, `elabS_congr`, `elabS_refine`: a concept
  reference elaborates to its producer, conservatively, and does not change
  while the design is realized. `valueOf_det`: the value of a concept at a tick
  is determined.
- Executed: Phase 6's composition and priority, Phase 14's light and Phase 8a's
  lamp rewritten in the invariant's form with the same traces
  (`composition_unique`, `priority_unique`, `rewrap_unique`,
  `private_lamp_unique`); a concept read by name (`read_by_concept`,
  `temperature_value`); a transport as a relay (`transport_unique`).

## 3. What is not established

That every design with several producers of one concept can be rewritten into
the invariant's form with the same trace — the invariant refuses such designs;
the rewriting is shown case by case. That `hbound` (originated concept
identities below the system width) follows from `ComposeWF` — taken as a
hypothesis. A theorem about production's code — none; the theorems are about the
model.

## 4. Verdicts

`ProducerUnique`, `originSet` — kernel, a global invariant. The boundary rule —
the composition judgment. `cref`/`elabS` — surface elaboration; no kernel term
names a concept. Resolver primitive — none.

## 5. Production guidance

Each line is a _design recommendation_ unless marked.

- **The concept block is a value node.** A concept has one input edge — from its
  producer (a relationship's output socket or a Source) — and any number of
  output edges to the relationships that read it. Relationships are never joined
  to relationships: ADR-0034's reference edge (relationship → formula line)
  becomes an edge from the **concept** block to the formula line. The kernel
  term is unchanged: the edge elaborates to `declRef` of the producer
  (`elabS_cref`, _informed by FV_), so `MappingAnalysis.references` and the wire
  format need no change; the projection draws the edge from the referenced
  declaration's produced concept.
- **A second producer is a diagnostic of the design**, in the class of "two
  drivers of one output": `concept C is produced by d₁ and d₂`. It is not a
  lint. Realizing a declaration never triggers it (`ProducerUnique.refine`);
  creating a second relationship whose output is an already-produced concept
  does, and the creation sheet should say so before the relationship exists.
- **What counts as a producer** (FVD-0161 §2): a relationship whose formula
  constructs the concept — in production's terms, a value or a Source whose
  output is the concept — outside the initial value of a `delay`/`sync`; a
  formula that only reads and re-exports (`light := dial`) is a wire. The
  _Produces_ row of ADR-0034 (the signature) stays for rules; _Carried by_ has
  exactly one row.
- **Composition**: the boundary rule at the system level mirrors the external
  sink rule — a shared concept is provided by at most one instance; a component
  that provides a concept its sibling also provides must make it private or the
  system must choose one provider. `flatten_producerUnique_ofB` is the check,
  over the templates' declaration lists.
- **Naming alternatives**: each candidate its own concept (`SensorATemperature`,
  `SensorBTemperature`, `ManualBrightness`, `AutoBrightness`, `BaseAngle`,
  `Correction`); the resolving relationship produces the shared concept. The
  library's value categories (ADR-0041) fit this: the candidates share a
  category, not a concept.
- **Cross-domain reads**: a reader in another clock domain reads the concept;
  the transport is the register mark on the edge (ADR-0034 §2's _spec_), not a
  second concept block and not a producer (`transport_unique`).
- **Simulation and probes**: a concept has one value per tick (`valueOf_det`):
  the probe for a concept shows that value; there is no "which producer" column.
