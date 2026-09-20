---
kind: project
area: process
status: current
---

# Migration report — 2026-09-20

Until 2026-09-20 the development's records were thirteen Markdown files at the
top of the repository: one report for every phase, one decision ledger, one
minimality table, nine notes, and a README that carried the status. On
2026-09-20 they were reorganised into `docs/` on the model the production
repository uses ([governance.md](governance.md)). This page maps every old file
to its new place so that citations in the paper, in the Lean comments and in the
production repository can be followed; the text of each record was moved, not
rewritten, and Git keeps the originals.

## File map

| Old file (top level)                                         | New place                                                                                                            | What changed in the move                                                                                                                                                                                                                                                                      |
| ------------------------------------------------------------ | -------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `REPORT.md` — _The kernel in one paragraph_                  | [`docs/kernel/kernel.md`](../kernel/kernel.md)                                                                       | frontmatter; intro paragraph                                                                                                                                                                                                                                                                  |
| `REPORT.md` — the _Layout_ table                             | [`docs/kernel/layout.md`](../kernel/layout.md)                                                                       | frontmatter; the rows for Phases 10–13, missing from the table, were added from the file list                                                                                                                                                                                                 |
| `REPORT.md` — `## Phase N …` sections                        | [`docs/reports/phase-NN-slug.md`](../reports/README.md), one per phase                                               | frontmatter (`phase`, `area`, `date` from the commit that added the section); `###` headings promoted one level; the trailing rule removed                                                                                                                                                    |
| `REPORT.md` — _Open items carried to later phases_           | [`docs/issues/NNN-slug.md`](../issues/README.md), OI-01 … OI-21                                                      | one record per bullet; struck-through bullets became `resolved` items whose `resolved-by` names the phase report                                                                                                                                                                              |
| `REPORT.md` — the project-state paragraph                    | [`docs/project/status.md`](status.md)                                                                                | rewritten against HEAD (the paragraph said "Phase 11 complete"; thirteen phases exist)                                                                                                                                                                                                        |
| `DESIGN_DECISIONS.md` (D-01 … D-130)                         | [`docs/decisions/NNN-slug.md`](../decisions/README.md), one per decision                                             | frontmatter (`date` from the commit that introduced the entry, `phase` from its section, `related` from the D-numbers it cites); the entry's own `Rejected:` / `Reason:` / `Consequence:` / `Verification:` / `Claim strength:` markers became headings; D-98's `related` set to D-90 by hand |
| `MINIMALITY.md`                                              | [`docs/kernel/minimality.md`](../kernel/minimality.md)                                                               | frontmatter; title case                                                                                                                                                                                                                                                                       |
| `BEHAVIOR_NOTE.md`                                           | [`docs/notes/behavior-as-a-first-class-design-object.md`](../notes/behavior-as-a-first-class-design-object.md)       | frontmatter                                                                                                                                                                                                                                                                                   |
| `BEHAVIOR_GROUPING_NOTE.md`                                  | [`docs/notes/behavior-grouping-and-component-extraction.md`](../notes/behavior-grouping-and-component-extraction.md) | frontmatter                                                                                                                                                                                                                                                                                   |
| `BEHAVIOR_SYSTEM_REQUIREMENTS.md`                            | [`docs/notes/behavior-system-requirements.md`](../notes/behavior-system-requirements.md)                             | frontmatter                                                                                                                                                                                                                                                                                   |
| `BUFFERING_NOTE.md`                                          | [`docs/notes/lossless-buffered-cross-domain-events.md`](../notes/lossless-buffered-cross-domain-events.md)           | frontmatter                                                                                                                                                                                                                                                                                   |
| `POLYMORPHIC_EQUATION_LANGUAGE_NOTE.md`                      | [`docs/notes/polymorphic-equation-language.md`](../notes/polymorphic-equation-language.md)                           | frontmatter                                                                                                                                                                                                                                                                                   |
| `UNITS_NOTE.md`                                              | [`docs/notes/unit-coordinates-and-formula-assembly.md`](../notes/unit-coordinates-and-formula-assembly.md)           | frontmatter                                                                                                                                                                                                                                                                                   |
| `NATURAL_SYNTAX_NOTE.md`                                     | [`docs/notes/natural-expression-surface.md`](../notes/natural-expression-surface.md)                                 | frontmatter                                                                                                                                                                                                                                                                                   |
| `UNIT_DOMAIN_NOTE.md`                                        | [`docs/notes/unit-domain-normalization.md`](../notes/unit-domain-normalization.md)                                   | frontmatter                                                                                                                                                                                                                                                                                   |
| `PROVISION_NOTE.md`                                          | [`docs/notes/source-provision-by-device-transducers.md`](../notes/source-provision-by-device-transducers.md)         | frontmatter                                                                                                                                                                                                                                                                                   |
| `README.md` — the status paragraph and the per-phase bullets | [`docs/project/status.md`](status.md)                                                                                | the README keeps the one-line description, the build command and the front-door pointer                                                                                                                                                                                                       |

In every moved record a reference to an old file name was rewritten to the new
path (`MINIMALITY.md` → `docs/kernel/minimality.md`, and so on); a reference of
the form `REPORT §1.5` was left as it was — the section numbers are unchanged
inside the phase reports.

## Citations outside this repository

- The monograph (`paper/paper.md`) named `MINIMALITY.md`, `DESIGN_DECISIONS.md`
  and `BEHAVIOR_SYSTEM_REQUIREMENTS.md`; the three mentions were updated and
  `body.typ` regenerated. `paper/NOTES.md` is a dated changelog and keeps the
  old names as history.
- The production repository (`../BDL`) cites the old names in its
  `formal-correspondence.md`, several ADRs, issues and the proposal — about
  thirty mentions. They are production's records to update; until then the table
  above resolves each name.
- `BDL/Core/Interface.lean` cited the ledger's D-16 in a comment; it now cites
  the record by its stable id (FVD-0016).

## What was not migrated

- `paper/` is unchanged: the monograph and its own `NOTES.md` are a separate
  product with a separate history.
- No decision was superseded, merged or renumbered. D-98's reversal of the
  Phase-9b `lt` generalisation is recorded as `related`, because D-90 (the
  record that mentions the generalisation) is still accepted for `eq`.
- No open item was closed or opened by the move; the five resolved items were
  already struck through in the old list.

## The same day, later: identifiers

The `D-NN` ids this page mentions were replaced by `FVD-NNNN` (and the open
items' `OI-NN` by `FVI-NNNN`) later on 2026-09-20; the map and the policy are in
[decision-id-migration.md](decision-id-migration.md). This page keeps the old
names because it describes the state the layout migration produced.
