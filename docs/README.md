# BDL_FV records

The front door for everything about _what the kernel is, why each construct is
there, what each phase established, and what is still open_. The Lean sources
under `BDL/` are the authority; these pages are their record. The production
implementation keeps its own records in the sibling repository `../BDL`
(`docs/README.md` there), and consumes this one through
[production-correspondence.md](project/production-correspondence.md).

## Layout

One folder per kind of record; every page carries a header that
`scripts/validate_docs.py` verifies against its folder.

| Folder                              | Holds                                                                       | Mutability                                            |
| ----------------------------------- | --------------------------------------------------------------------------- | ----------------------------------------------------- |
| [`kernel/`](#kernel)                | what the kernel is now: summary, file map, construct-by-construct verdicts  | current truth, edited in place                        |
| [`reports/`](reports/README.md)     | what one phase asked, tried, proved and concluded                           | written once; later corrections recorded, not applied |
| [`decisions/`](decisions/README.md) | why a model choice was made and what was rejected (FVD-NNNN)                | append-only; superseded, never rewritten              |
| [`notes/`](notes/README.md)         | the phase's account for a reader outside the Lean, with production guidance | current, kept true                                    |
| [`issues/`](issues/README.md)       | questions recognised and not answered (FVI-NNNN)                            | open · deferred · resolved                            |
| [`project/`](#project)              | status, governance, production correspondence, the migration report         | current                                               |

## Where to look

| I want…                                                                | Read                                                                                                                                                                               |
| ---------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **the kernel in one page**                                             | [kernel/kernel.md](kernel/kernel.md)                                                                                                                                               |
| **which file defines what**                                            | [kernel/layout.md](kernel/layout.md)                                                                                                                                               |
| **whether a construct is kernel, surface, validation or removed**      | [kernel/minimality.md](kernel/minimality.md)                                                                                                                                       |
| **what a phase proved, and on what hypotheses**                        | [reports/README.md](reports/README.md), then the phase                                                                                                                             |
| **why a choice was made**                                              | [decisions/README.md](decisions/README.md)                                                                                                                                         |
| **the result without reading Lean; what production should do with it** | [notes/README.md](notes/README.md)                                                                                                                                                 |
| **what is not modelled, proved or tested**                             | [issues/README.md](issues/README.md)                                                                                                                                               |
| **what builds, on which axioms, which phases exist**                   | [project/status.md](project/status.md)                                                                                                                                             |
| **which production ADR / issue / proposal used which phase**           | [project/production-correspondence.md](project/production-correspondence.md)                                                                                                       |
| **how these records work; the old ids**                                | [project/governance.md](project/governance.md) · [project/migration-report.md](project/migration-report.md) · [project/decision-id-migration.md](project/decision-id-migration.md) |
| **the monograph**                                                      | `../paper/paper.md` (canonical), `../paper/build.sh`                                                                                                                               |

## Pages

### Kernel

| Page                                  | What it fixes                                                                                                 |
| ------------------------------------- | ------------------------------------------------------------------------------------------------------------- |
| [kernel.md](kernel/kernel.md)         | the cumulative kernel after Phase 16: objects, judgments, primitives, the refinement/edit split               |
| [layout.md](kernel/layout.md)         | every Lean file and the definitions and theorems it holds                                                     |
| [minimality.md](kernel/minimality.md) | every construct ever proposed with its verdict: kernel · surface · library · validation · UI · defer · remove |

### Project

[status.md](project/status.md) · [governance.md](project/governance.md) ·
[production-correspondence.md](project/production-correspondence.md) ·
[migration-report.md](project/migration-report.md) ·
[decision-id-migration.md](project/decision-id-migration.md)

## Current snapshot — 2026-09-20

- **Kernel:** `DeclEnv : DeclId → Option DesignDecl`; a declaration is a stable
  id, an interface (frozen expected type + monotone public commitments) and a
  write-once realization. Types:
  `bool | nat | arr | sem SemanticId | q Dim | opt | list | prod`. One temporal
  primitive `sync c init e` (`delay` its own-domain instance), one list recursor
  `fold`, `rep`/`mk` under a grant, tick-indexed evaluation `Ev ⊂ MEv`. Outputs
  are nominal sinks with a write-once drive edge and one global single-driver
  invariant; hardware feasibility is a separate decidable validation. Everything
  else — behaviours, groups, buffers, the equation library, units, charts,
  natural binders, the unit domain, Source provision, output realization, the
  adapter boundary and the device clock — is a construction over designs proved
  to preserve the kernel's judgments.
- **Phases:** 0–7, 8a/8b, 9a–9c, 10, 10b, 11, 12, 13, 14, 15, 16 complete; 148
  decisions; 29 items: 9 open, 9 deferred, 11 resolved. Build clean on Lean
  4.33.1, no `sorry`, `propext`/`Quot.sound` only.
- **Not started:** Phase 8c (surface elaboration of the remaining
  designer-facing forms, executable semantics); the final minimality audit.
- **Recently changed:** Phase 16 — communication as state: the auto_typer stress
  case (queue, cancellation, freshness, faults, acknowledgement, cross-clock
  delivery, a paired axis) encoded and executed on the unchanged kernel, no
  message/event/queue/transaction primitive; Source-side non-interference
  (`two_providers_same_behavior`) completing the replacement-invariance
  criterion; catalogue profiles with an unread origin and the deployment-only
  `assign`; contract separate from feasibility; the audit of every open item
  against Phases 8a–14 and production `6be778b` (eleven resolved, deferred or
  merged; FVI-0022 split into FVI-0023 … FVI-0027; FVI-0011 narrowed, FVI-0028
  split off) and Phase 15 — the adapter boundary (policy, operation, line;
  `adapter_of_sink`) and the explicit device clock (`lowerSync_correspondence`);
  no stateful realization primitive (`exE_slew`); Phase 14 — output realization
  by device encoders, the output-side dual of Source provision: a logical output
  is semantic intent, the mechanism (PWM / GPIO / I²C / UART) is a deployment
  lowering that adds a pure encoder and a machine sink and changes nothing the
  behaviour observes; the machine boundary is the `RawCommand` relation, never
  an `R -> ()` term; correspondence is directional and admits quantization;
  Phase 13 — Source provision by device transducers, the audit of production's
  PRP-0001 (four of seven claims corrected: purity is the profile condition, the
  transfer function is carried on values, commitments are obligations on the
  profile, trace equality needs a joint section); Phase 12 — the canonical type
  `() -> B` as an interface normalization above the kernel, the source role as a
  realization state, `A -> ()` unable to name a consumer (consumed by
  production's ADR-0029 and ADR-0032); the records reorganised into this tree
  (2026-09-20).

## Rules in one paragraph

The kernel pages are current truth, edited in place. A model choice gets a
decision that is never rewritten — supersede it. A phase gets one report,
written once; a later phase that overturns a claim strikes the line and says so
in its own claim audit. A question without an answer is an open item, not a
decision. What exists is in `project/status.md`. A new page goes into its kind's
folder with a header and a row on this page. Run `just docs-check` and
`lake build` before committing. The full rules:
[project/governance.md](project/governance.md).
