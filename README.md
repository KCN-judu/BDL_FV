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

Status: Phase 1 (cross-declaration references, dependency) complete; kernel
ontology migrated from "holes" to declarations (REPORT §M).

Kernel in one line: `DeclEnv : DeclId → Option DesignDecl`, where a
`DesignDecl` is a stable id, a `DeclInterface` (expected type + monotone
public commitments), and an optional realization. Typing sees only the
expected type; validation may rely on commitments and evidence; monotone
refinement preserves earlier commitments; anything else is an edit that
requires rechecking dependents.
