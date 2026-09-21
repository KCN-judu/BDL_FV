---
kind: report
phase: 21
area: surface
date: 2026-09-21
status: current
---

# Phase 21 — Sem blocks and mapping blocks: the design objects, and the concept as their type template

Question (the owner's generational proposal after Phase 20): if a **Concept** is
a type — a template — and a **Sem** is one instance of it holding one value, so
that the canvas draws Sem blocks rather than concept blocks and a designer
creates Sem blocks from a concept template, does everything become coherent?
Answer: **yes, and it coincides with the kernel's one object.** A Sem block is a
`DesignDecl` of type `sem C`: its interface is the block, its write-once
realization is the mapping block attached to it — the one producer of its value,
by construction (FVD-0007) — and when absent the environment provides the value
(a Source, FVD-0118). A rule — an arrow-typed declaration — is to mapping blocks
what a concept is to Sem blocks: a template applied as many times as there are
Sem blocks to produce. Several Sem blocks of one concept are ordinary
(`sensorA, sensorB, roomTemp : Temperature`), no invariant counts them, and a
mapping reads a Sem block by `declRef` — the kernel's only reference form — so
nothing is resolved by concept and no elaboration is needed. Every edge on the
canvas is either a mapping block into its Sem block (`ProducedBy`, functional
and write-once) or Sem blocks into a mapping block (`Reads` = `DependsOn`). The
theorems are restatements of Phases 0–1, 5 and 13 (`Surface/Sem.lean`); the
designs of the brief and of Phase 19 are read this way and executed
(`Experiments/SemExamples.lean`). Phase 20's `ProducerUnique` becomes an
optional design judgment — "one Sem block per concept" — and its concept
reference an experiment; both are demoted, not refuted, and their theorems
stand. Decision FVD-0163 (supersedes FVD-0161, FVD-0162); note:
[the-sem-block-model.md](../notes/the-sem-block-model.md).

## 21.1 The reading

| Design object          | Kernel object                                                               | Since              |
| ---------------------- | --------------------------------------------------------------------------- | ------------------ |
| Concept (template)     | `SemanticId` with its representation in `Θ` (nominal type `sem C`)          | Phase 2, 3         |
| Sem block (instance)   | `DesignDecl` with `expectedType = sem C`; one value per tick                | Phase 0, 1, 4      |
| its producer           | the block's `realization`, write-once; `none` = provided by the environment | FVD-0007, FVD-0118 |
| mapping block          | that realization, drawn as a node: a rule applied to Sem blocks             | Phase 1            |
| rule (template)        | an arrow-typed declaration                                                  | Phase 1            |
| produce edge           | `ProducedBy Δ s m` (= `realizationOf s = some m`)                           | —                  |
| read edge              | `Reads Δ s d` (= `DependsOn Δ s d`, FVD-0005)                               | —                  |
| Source                 | a Sem block with no producer                                                | FVD-0118           |
| instances of a concept | `Instances ids Δ C` — the Sem blocks typed `sem C`                          | —                  |

`Surface/Sem.lean` defines `IsSem`, `IsRule`, `Instances`, `ProducedBy`, `Reads`
and proves: `producedBy_unique` (one producer per Sem block — functional by
construction), `producedBy_refine` (write-once under refinement),
`producedBy_of_refine` (a producer after a refinement was there before or was
the refinement's `realize` step), `reads_iff_dependsOn` (the read edges are the
kernel's dependency relation), `new_sem_transparent` (creating a Sem block of
any concept, referenced by nothing, changes no value — from
`update_transparent`), `sem_value_det` (one value per tick, from `MEv.det`).

## 21.2 The designs

`Experiments/SemExamples.lean`, executed:

- `lamp_picture` — the canvas of the brief: `pressed : Pressed` a Sem block with
  no producer, `lit : Pressed -> Lit` a rule, `Lit := lit(pressed)` a Sem block
  whose producer is the mapping block; `Lit` reads `pressed` and the rule and
  nothing else; the light follows the button.
- `rule_template` — one rule, two mapping blocks, two Sem blocks of `Lit`
  (`Instances … Lit = [litV, litB]`), each with its one producer.
- `sensors_natural` — Phase 19's redundant sensors in their natural form: three
  Sem blocks of `Temperature`, two provided by the environment and one produced
  by a selection over them; `hot` reads the selection; the trace Phase 19
  executed. No intermediate concept.
- `judgment_optional` — the natural form is `GlobalWF` and not `ProducerUnique`;
  Phase 19's intermediate-concept form is. A design chooses.

## 21.3 What changes in the records, and what does not

- **Kernel**: nothing. No object, judgment or primitive is added or removed;
  `Surface/Sem.lean` is a projection. Phase 20's `Core/Producer.lean` moves to
  `Validation/Producer.lean` (an optional judgment beside hardware feasibility
  and capacity) and `Surface/ConceptRef.lean` to `Experiments/ConceptRef.lean`;
  every theorem of both stands.
- **Phase 19's audit** (FVD-0159: a concept is a nominal type with many
  producers) is the kernel reading FVD-0163 restores, now with the canvas fixed:
  what was wrong was never the kernel but the projection that drew a concept as
  a node with a value. FVD-0159 stays superseded (the chain 0159 → 0161 → 0163
  records the path).
- **Phase 20** (FVD-0161: one producer per concept as a global invariant;
  FVD-0162: a concept reference) was right on its requirement — a concept block
  that is a value — and that requirement is withdrawn: the value block is the
  Sem block. Its verdict lines are struck.
- **Production**: no semantic change; ADR-0034's canvas (relationships and
  concept nodes) becomes Sem blocks and mapping blocks with the two edge kinds;
  the Concept sheet (ADR-0041) is the template a Sem block is created from. The
  note §5 has the guidance.

## 21.4 Models tried

| Model                                     | Decided by                                                                                                                         |
| ----------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------- |
| concept block as a value node (Phase 20)  | needs a global invariant and an elaboration; the Sem block has the value structurally — `producedBy_unique`, `new_sem_transparent` |
| a Sem block distinct from its declaration | a second identity for one object; `DesignDecl` already is interface + realization                                                  |
| the mapping block as the rule declaration | a rule applied twice would give one block two output edges; the mapping block is the application — `rule_template`                 |
| one Sem block per concept, mandatory      | refuses `sensorA, sensorB : Temperature` (`judgment_optional`); optional instead                                                   |

## 21.5 Theorems

| Claim                                                                 | Theorem                                                                            | Hypotheses                            |
| --------------------------------------------------------------------- | ---------------------------------------------------------------------------------- | ------------------------------------- |
| one producer per Sem block                                            | `producedBy_unique`                                                                | —                                     |
| the producer is write-once; never arrives from elsewhere              | `producedBy_refine`, `producedBy_of_refine`                                        | `EnvRefines Δ₁ Δ₂`                    |
| read edges are dependency                                             | `reads_iff_dependsOn`                                                              | —                                     |
| creating a Sem block is transparent                                   | `new_sem_transparent`                                                              | `GlobalWF`, fresh id, inputs avoid it |
| one value per tick                                                    | `sem_value_det`                                                                    | —                                     |
| the picture, the template, the natural sensors, the optional judgment | `lamp_picture`, `rule_template`, `sensors_natural`, `judgment_optional` (executed) | closed designs                        |

11 theorem-like declarations added; every one on `propext`/`Quot.sound`
(`#print axioms` on all ten headline theorems); no `sorry`; the whole
development 1 623 across 75 files; `lake build` 78 jobs, clean, no warnings.

## 21.6 Claim audit

- **Proved**: the six theorems of `Surface/Sem.lean`; each is immediate from an
  earlier phase's theorem and is reported as such.
- **Executed**: the four designs.
- **Definitional**: the table of §21.1 — a reading of existing objects.
- **Not established**: nothing new is claimed; Phase 20's unproved items (a
  general rewriting theorem; `hbound` from `ComposeWF`) stay as recorded there
  and now concern an optional judgment.
- **Design recommendation**: the canvas as Sem blocks and mapping blocks; the
  concept as a template; the note §5.

## 21.7 Verdicts

- Sem block = `DesignDecl` of concept type; mapping block = its realization;
  concept = template; rule = template — **KEEP IN KERNEL** as what the kernel
  already is (FVD-0163); `Surface/Sem.lean` — **KEEP IN SURFACE-DESUGAR** as the
  projection.
- `ProducerUnique` (one Sem block per concept) — **MOVE TO VALIDATION**,
  optional (FVD-0163).
- `cref`/`elabS` — **MOVE TO EXPERIMENTS**: not part of the surface language; a
  reference is `declRef` to a Sem block (FVD-0163).
- intermediate concepts for alternatives — **not required**; a guidance of style
  only.
