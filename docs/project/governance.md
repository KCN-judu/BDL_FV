---
kind: project
area: process
status: current
---

# Record governance

How BDL_FV keeps four things apart: **what the kernel is now**, **why each
choice was made**, **what each phase established**, and **what is still open**.
The model is the one the production repository (`../BDL`,
`docs/project/governance.md` there) uses, sized down to a formal development:
the same kinds, the same frontmatter discipline, the same rule that a fact lives
in one place and history is never rewritten.

## The record kinds

| Kind                | Answers                                                                                | Lives in                                    | Mutability                                                | ID         |
| ------------------- | -------------------------------------------------------------------------------------- | ------------------------------------------- | --------------------------------------------------------- | ---------- |
| **Kernel page**     | what the kernel is now: the summary, the file map, the construct-by-construct verdicts | `docs/kernel/*.md`                          | mutable current truth                                     | —          |
| **Phase report**    | what one phase asked, tried, proved and concluded                                      | `docs/reports/phase-NN-slug.md`             | written once; later corrections are recorded, not applied | phase      |
| **Design decision** | why a model choice was made, what was rejected, the formal reason                      | `docs/decisions/NNN-slug.md`                | append-only once accepted                                 | `FVD-NNNN` |
| **Design note**     | the phase's account for a reader outside the Lean sources; production guidance         | `docs/notes/slug.md`                        | mutable while its claims are current                      | —          |
| **Open item**       | a question the development has recognised and not answered                             | `docs/issues/NNN-slug.md`                   | mutable while open, frozen at resolution                  | `FVI-NNNN` |
| **Status**          | which phases exist, what builds, on which axioms                                       | `docs/project/status.md`                    | mutable                                                   | —          |
| **Correspondence**  | which production record consumed which phase, at which strength                        | `docs/project/production-correspondence.md` | mutable index of links                                    | —          |

The **monograph** (`paper/paper.md`, built to
`paper/BDL_behavior_design_language.pdf`) is the conceptual synthesis of all of
the above: organized by concept, pinned to one production commit, and edited as
a whole; it cites the records and never replaces them. A phase report is the
local experiment record; a decision record the stable conclusion; a note the
focused derivation with production guidance; the monograph the current
synthesis; `paper/archive/` the history. The roles are different and none is
derived from another by tooling.

The Lean sources under `BDL/` are the authority for what is defined and proved;
every record above cites them and none of them replaces them. The monograph in
`paper/` is a separate product with its own history (`paper/NOTES.md`). The
production repository keeps its own records; this repository never edits them
and carries only the correspondence.

The front door for all of it is [docs/README.md](../README.md).

## Selecting the record: what kind of fact changed?

| The fact that changed                                                | Record to touch                                                                            | Not this                               |
| -------------------------------------------------------------------- | ------------------------------------------------------------------------------------------ | -------------------------------------- |
| a kernel object, judgment or primitive is added, removed or re-typed | `docs/kernel/kernel.md`, `layout.md`, the row in `minimality.md`                           | a note; the decision that chose it     |
| a phase completed                                                    | a new report; `status.md`'s phase row; the decisions it made                               | rewriting an earlier report            |
| a model choice was **made**                                          | a new decision (or one that `supersedes` an old one)                                       | editing the old decision's reason      |
| a later phase **corrects** an earlier claim                          | a struck-through line in the earlier report naming the phase; the new report's claim audit | silently editing the old text          |
| a question is recognised and unanswered                              | an open item                                                                               | a decision with a tentative answer     |
| an open item is answered                                             | `state: resolved`, `resolved-by`, the Resolution section, the index row moves              | deleting the item                      |
| the production repository consumed a result                          | `production-correspondence.md`                                                             | a stronger word than the theorem earns |
| the axiom base, the toolchain, the build changed                     | `status.md`                                                                                | the reports                            |

One phase usually touches a report, several decisions, the kernel pages,
`status.md`, and resolves or opens items — each **once**. A refactor that
changes no theorem statement touches nothing here; Git has it.

## Lifecycles

### Design decision

- **Created** when a model choice is made that a theorem, counterexample or
  definitional argument decided: a construct enters or leaves the kernel, a
  judgment's shape, a boundary between kernel / surface / validation.
- **Fields**: frontmatter `id`, `legacy-id` (the ledger number a record had
  before 2026-09-20, if any), `status`, `date`, `phase`, `area`, `supersedes`,
  `superseded-by`, `related`, `production` (§ IDs). Body: Status (prose),
  Decision, Alternatives rejected, Reason, Consequences (when any). A dated
  `## Amendment` may be appended when the choice is extended without being
  replaced (FVD-0106's Phase-10b revision); it does not rewrite the text above.
- **Statuses**: `accepted` · `superseded` · `withdrawn`. There is no `proposed`
  decision: an undecided question is an open item.
- **Immutable after acceptance** except the frontmatter, an appended amendment,
  and factual corrections (a wrong path, a typo).
- **Superseded** by a new decision that lists it in `supersedes`; the old one
  gets `superseded-by` and status `superseded`, and the new one says whether the
  old choice was _wrong on the same evidence_ or _right until the model
  changed_. The kernel pages cite only the replacement.
- **Never deleted, renumbered or reused.** The numbers are cited by the
  monograph, the Lean comments and the production repository's records.

### Phase report

- **Created** when a phase's `lake build` is clean: the question, the model, the
  alternatives tried, the theorems (with hypotheses), the executed cases, the
  claim audit, the verdicts. Section numbers are `N.k`; other records cite them
  as `REPORT §N.k`.
- **Corrected, not rewritten.** When a later phase overturns a claim, the old
  line is struck through with the phase that changed it, and the new report's
  claim audit says what it replaced (Phase 9c did this to 9b's `lt`).
- One file per phase; a sub-phase (`8a`, `10b`) is its own file.

### Open item

- **Created** when a phase notices a construct it did not model, a theorem it
  did not prove, or a boundary it did not test.
- **Fields**: `id`, `legacy-id`, `state`, `area`, `opened`, `resolved-by` (a
  report or a decision), `related`, `production`; body: Problem · Current
  evidence · Dependencies · Resolution.
- **States**: `open` · `deferred` (a decision _not to decide now_, with the
  reason) · `resolved`.
- **Resolved** ⇒ `resolved-by` names the record; the row moves from _Active_ to
  _Resolved_ in the index; the record stays.

### Design note

- **Created** when a phase's result needs an account for someone who will not
  read the Lean: the production repository, a reviewer, the paper.
- Carries the same claim-strength words as the report and never a claim the
  report does not; production guidance is labelled as such.
- Edited when a later phase changes a claim it makes, recording the change.

### Status

- One row per phase with its title, area, files, report, note and decision
  range; the build, toolchain and axiom facts as of HEAD. "Complete" means the
  report exists and `lake build` passes with no `sorry`.

## IDs and production correspondence

Two prefixes, both four digits, sequential and append-stable, never renumbered:
`FVD-NNNN` for a formal design decision, `FVI-NNNN` for a formal open item. A
number says nothing about a phase — the phase is metadata — and nothing about
production. Production's records are `ADR-NNNN`, `PRP-NNNN` and `ISS-NNNN`
(`../BDL/docs/project/governance.md`), and the two namespaces never overlap.

Every FVD and FVI record carries a `production` field naming the production
record that decided, proposed or raised the same architectural question, with
the relation `supports` (the formal result backs an accepted ADR), `audits` (the
formal result audits a proposal) or `bears-on` (the formal result speaks to an
open issue); an empty list means FV-only. Current documents cite the two
together — `ADR-0032 (FVD-0118)`, `PRP-0001 (FVD-0121 … FVD-0130)` — so that one
architectural fact has one production identity and its formal evidence beside
it, and no competing number is minted here for a fact production already names.
The validator refuses a `production` entry that is not one of the three
production prefixes.

The ledger numbers `D-NN` and the interim `OI-NN` of 2026-09-20 are retired; the
permanent map is [decision-id-migration.md](decision-id-migration.md), each
record keeps its old number in `legacy-id`, and the validator refuses a retired
id anywhere else in the current pages. Archived material is never rewritten to
the new ids.

## Metadata

Decisions and open items carry YAML frontmatter with scalar values and inline
lists (`[a, b]`, possibly wrapped onto the next line by Prettier) — the subset
`scripts/validate_docs.py` parses without a YAML library. The production
snapshot the correspondence is stated against lives in exactly one place, the
`snapshot` field of
[production-correspondence.md](production-correspondence.md); the monograph
cites it. Reports and notes carry `kind`, `phase`, `area`, `date`, `status`;
kernel and project pages carry `kind`, `area`, `status`. Every page lives in the
folder of its kind, and the validator checks that the kind matches the folder,
that no page sits loose at the top of `docs/`, and that the front door registers
every page. File names are lowercase kebab-case.

`area` is one of: `core`, `validation`, `behavior`, `surface`, `experiments`,
`paper`, `process`. It names the source directory whose objects the record is
about (`BDL/Core`, `BDL/Validation`, `BDL/Behavior`, `BDL/Surface`,
`BDL/Experiments`), the monograph, or the records themselves.

### Claim strength

Records say how strong a claim is, with these words and no others:

| Word                    | Means                                                                                            |
| ----------------------- | ------------------------------------------------------------------------------------------------ |
| _proved_                | a named theorem in `BDL/` proves the stated property, on `propext` / `Quot.sound` only           |
| _executed_              | a `#eval` / `decide` case in `BDL/Experiments` shows the behaviour for that input; not a theorem |
| _tested design failure_ | a candidate model was formalised and a theorem or counterexample killed it                       |
| _definitional_          | the claim is the definition; the theorem is immediate and is reported as such                    |
| _not established_       | stated, not modelled or not proved; an open item names it                                        |
| _design recommendation_ | guidance to production with no theorem behind it                                                 |

A theorem about the model never proves the Rust or Dart code; the production
repository labels what it takes from here as _formally proved (model)_,
_informed by FV_ or _design recommendation_ in its own records, and
[production-correspondence.md](production-correspondence.md) lists those links.

## What every change to the records must do

1. Route the fact (table above) and touch each authority once.
2. If a decision was replaced, supersede — never rewrite.
3. Sweep for stale claims in the authorities you did not touch:
   `grep -rn -E "not proved|not modelled|untested|pending|TODO|revisit" docs/kernel docs/project docs/issues README.md`
   plus the phase number and any decision or item ID involved. Fix only what is
   stale.
4. Run `just docs-fmt` (Prettier + `scripts/md_normalize.py` + markdownlint
   fixes), then `just docs-check` (the same in check mode plus
   `scripts/validate_docs.py`), then `lake build`.
5. Update [docs/README.md](../README.md)'s _Current snapshot_ if what a newcomer
   should know first has changed.
