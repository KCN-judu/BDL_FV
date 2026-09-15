# BDL_FV — formal-design experiment for a Behavior Design Language kernel

A Lean 4 project that treats the BDL proposal as a *candidate* specification
and derives, by construction / counterexample / proof, what its kernel
actually needs.  No dependencies beyond core Lean.

```bash
lake build
```

* `paper/` — the BDL paper (Typst source, `paper/build.sh` compiles it)
* `REPORT.md` — formal results per phase
* `DESIGN_DECISIONS.md` — every model choice and rejected alternative
* `MINIMALITY.md` — construct-by-construct kernel / surface / validation / remove table

Status: Phases 0–7 complete (lifecycle/refinement; cross-declaration
preservation; semantic identity; representation binding + dimensions;
reactive core; clock domains + synchronization; physical outputs +
single-driver discipline; hardware constraint validation + resource
allocation). Remaining: Phase 8 surface elaboration + executable semantics;
final minimality audit.

Kernel in one line: `DeclEnv : DeclId → Option DesignDecl`, where a
`DesignDecl` is a stable id, a `DeclInterface` (expected type + monotone
public commitments), and an optional realization. Types include nominal
semantic concepts `Ty.sem SemanticId` (Phase 2) and quantities `Ty.q Dim`
(Phase 3). A write-once `ConceptEnv` binds concepts to sem-free
representations; `rep` observes freely, `mk s` constructs only inside a
realization whose own signature announces `sem s` (Phase 3). One temporal
primitive `delay init e` and a tick-indexed evaluation relation give the
single-domain reactive semantics: deterministic, total on causal designs, and
every designer-facing temporal operator derived (Phase 4). Nominal clock
domains with a schedule, a domain judgment, and one transport primitive
`sync src init e` (of which `delay` is the own-domain instance) give the
multi-domain semantics; the single-domain one embeds exactly (Phase 5).
Physical sinks are nominal resources with an accepted type and clock; a
write-once drive edge per declaration, checked by type and clock equality,
and one global invariant — at most one driver per sink — connect values to
hardware; all combination is ordinary computation (Phase 6). A separate
validation layer (`BDL/Validation/`) decides whether a design is realizable
on a declared target board — a finite resource/capability table with a
sound and complete solver — without the design ever depending on the board
(Phase 7). Typing sees only the
expected type; validation may rely on commitments and evidence; monotone
refinement preserves earlier commitments; anything else is an edit that
requires rechecking dependents.
