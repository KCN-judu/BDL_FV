---
kind: report
phase: 22
area: core
date: 2026-09-21
status: current
---

# Phase 22 — The concept ladder: concept = type, Sem block = instance; `ConceptId`; Phase 20 demoted to an experiment

Question (the owner, after Phase 21): the vocabulary of the code put the word
_semantic_ on the type side (`SemanticId`, "semantic identity") while the
product word _Sem_ names the instance; a reader — human or agent — could not
tell from the names which level is the type and which the instance. Fix the
ladder in the code and the records, and remove the proofs that existed only
because of the ambiguity. Answer: **done.** The ladder is

| Level             | Object                                  | Formal                                          | Role                             |
| ----------------- | --------------------------------------- | ----------------------------------------------- | -------------------------------- |
| 0 representation  | "an angle", "a truth value"             | `Θ C = R` (`q d`, `bool`, …)                    | the type of the type             |
| 1 **concept**     | `Tilt`, `Brightness`, `Temperature`     | `ConceptId`; the nominal type `sem C`           | **type — a template**            |
| 2 **Sem block**   | `sensorA : Temperature`, `roomTemp : …` | `DesignDecl` with `expectedType = sem C`        | **instance**, one value per tick |
| 3 value at a tick | 310 K                                   | `Value.sem C v` (a tagged representation value) | the instance's state             |

and in parallel: a **rule** (arrow-typed declaration) is a template, a **mapping
block** (a Sem block's realization) its instance. `sem C` is read "a Sem of
`C`": the type of the Sem values of concept `C`. Concept : Sem block = rule :
mapping block = type : instance. Decision FVD-0164.

## 22.1 The renaming (no theorem statement changes)

`BDL/`: `SemanticId` → `ConceptId` (190 occurrences, 38 files);
`BehaviorComponent.internalSem` → `internalConcept`; `Realizes.semBound` →
`conceptBound`; `inst_sem_disjoint` → `inst_concept_disjoint`;
`inst_sem_not_global` → `inst_concept_not_global`; docstrings: "semantic
identity" → "concept identity", "semantic value/type" → "Sem value/type",
"semantic-free" → "concept-free". Kept: `Ty.sem`, `Value.sem`, `Expr.mk`,
`Ty.SemFree`, `Ty.grant` (their meaning is the instance level, which is what
_Sem_ now names), the namespace `Experiments.Semantic`, and every theorem name —
`semantic_identity_mismatch_rejected`,
`temporal_state_preserves_semantic_identity`,
`sync_preserves_semantic_identity`, `no_semantic_value_without_declaration`, …
keep their historical spelling (cited by the papers and by production);
"semantic identity" in a theorem name reads "concept identity". The records were
corrected mechanically (`ConceptId`, the four renamed identifiers, the moved
paths) as factual identifier corrections; the papers were not touched (their
`SemanticId` is a figure name, listed in the impact note).

## 22.2 Proofs removed or demoted

Phase 20 existed because the concept was read as holding a value. Under the
ladder that reading is gone, and so is the consumer of its invariant:

- **Deleted**: `Experiments/ConceptRef.lean` (the concept reference `cref` and
  its elaboration: a reference is `declRef` to a Sem block; 7 theorems) and
  `Experiments/ProducerUniqueExamples.lean` (Phase 6/8a/14 rewritten with
  intermediate concepts to satisfy an invariant no longer asked; 9 theorems).
  Their statements stay in the Phase 20 report as the record of what was proved;
  Git has the sources.
- **Demoted to experiments**: `Validation/Producer.lean` →
  `Experiments/ProducerUnique.lean`, `Behavior/Producer.lean` →
  `Experiments/ProducerUniqueComposition.lean` — the invariant "one Sem block
  per concept", its refinement and flattening theorems and its decision
  procedure, kept as the record of what that discipline would cost (32 theorems,
  unchanged).
- **Kept**: Phase 19's `Experiments/ProducerAlternatives.lean` (the audit's
  witnesses: several Sem blocks of one concept are well formed and invisible to
  each other; signature-uniqueness is refuted by bindings and transports) and
  Phase 21's `Surface/Sem.lean`, `Experiments/SemExamples.lean`.

## 22.3 Theorems

No new theorem. The whole development: 1 607 theorem-like declarations across 73
files (1 623 − 16 deleted); `lake build` 76 jobs, clean, no warnings;
`propext`/`Quot.sound` only (the rename is α-conversion; the axiom base of every
module is unchanged).

## 22.4 Claim audit

- **Definitional**: the ladder — a naming of objects that exist since Phases
  1–3; nothing is proved by it and nothing needs to be.
- **Corrected from Phase 21**: Phase 21 placed `ProducerUnique` in `Validation/`
  as an optional judgment; Phase 22 places it in `Experiments/` — it is not a
  judgment the development offers, it is the record of a tested discipline
  (§22.2). Phase 21's verdict line is struck.
- **Not established**: nothing new.

## 22.5 Verdicts

- `ConceptId` as the name of the type-level identity; `sem C` read "a Sem of
  `C`" — **KEEP IN KERNEL** (FVD-0164).
- `ProducerUnique` and its composition theorem — **MOVE TO EXPERIMENTS**
  (FVD-0164; tested design, no consumer).
- `cref`/`elabS`, the intermediate-concept rewritings — **REMOVE** (FVD-0164;
  artifacts of the superseded reading).
- Production: the same rename (`SemanticId` → `ConceptId` in `bdl-model`, the
  protocol's field names where they say _semantic_, Studio's vocabulary) — the
  brief in the correspondence page's Phase 22 paragraph.
