---
id: FVD-0164
legacy-id:
status: accepted
date: 2026-09-21
phase: 22
area: core
supersedes: []
superseded-by: []
related: [FVD-0163, FVD-0019, FVD-0020, FVD-0161, FVD-0162]
production: [ADR-0013/bears-on, ADR-0034/bears-on, ADR-0041/bears-on]
---

# FVD-0164: The concept ladder — a concept is a type named by `ConceptId`, a Sem block is its instance, `sem C` reads "a Sem of `C`"; the vocabulary is fixed in the code, and Phase 20's machinery is an experiment

## Status

Accepted in Phase 22. Extends FVD-0163 (the Sem-block model) with the naming
that makes it readable without the report.

## Decision

1. **The ladder.** representation (`Θ C = R`) → **concept** (`ConceptId`, the
   nominal type `sem C`; a template) → **Sem block** (a `DesignDecl` of type
   `sem C`; an instance holding one value per tick) → **value**
   (`Value.sem C v`). In parallel: rule (arrow-typed declaration; a template) →
   mapping block (a Sem block's realization; an instance).
2. **Names.** The type-level identity is `ConceptId` (was `SemanticId`).
   `Ty.sem C` is "the type of the Sem values of `C`" and `Value.sem C v` "a Sem
   value of `C`"; both keep their constructor names because they name the
   instance level, which is what _Sem_ means. `internalConcept`, `conceptBound`,
   `inst_concept_disjoint`, `inst_concept_not_global` replace their
   `sem`-spelled predecessors. Theorem names keep their historical spelling; in
   a theorem name "semantic identity" reads "concept identity". Docstrings say
   _concept identity_, _Sem value_, _Sem type_, _concept-free_.
3. **What the ambiguity had produced is removed or demoted.** The concept
   reference (`cref`/`elabS`) and the intermediate-concept rewritings are
   deleted; `ProducerUnique` with its refinement, composition and decision
   theorems moves to `Experiments/` as a tested discipline with no consumer. No
   theorem statement elsewhere changes.
4. **Production follows** with the same rename and vocabulary (a brief in the
   correspondence page); until it does, `bdl_model::SemanticId` is read as
   `ConceptId`.

## Alternatives rejected

- Keep `SemanticId` and explain the ladder in prose: the names would keep saying
  the opposite of the ladder to every new reader.
- Rename the instance word instead (_Value block_): the owner's product word is
  _Sem_; the code follows the product.
- Rename `Ty.sem`/`Value.sem` to `concept`: wrong level — they name Sem values,
  not concepts.
- Rename the theorems: cited by two papers and by production's records; the gain
  is spelling only.
- Delete Phase 20 entirely: its theorems are the record of what "one Sem block
  per concept" costs, and they are cheap to keep as experiments.

## Reason

Definitional. `lake build` unchanged in content after the α-conversion (76 jobs;
1 607 theorem-like declarations after the 16 deletions); `Surface/Sem.lean`'s
theorems (`producedBy_unique`, `reads_iff_dependsOn`, `new_sem_transparent`) are
the ladder's instance level, and they needed no edit.

## Consequences

`kernel.md` states the ladder; `layout.md` and `minimality.md` follow the moves;
the records cite `ConceptId`. Production's rename is the next brief.
