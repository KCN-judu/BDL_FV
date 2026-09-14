# BDL_FV — formal-design experiment for a Behavior Design Language kernel

A Lean 4 project that treats the BDL proposal as a *candidate* specification
and derives, by construction / counterexample / proof, what its kernel
actually needs.  No dependencies beyond core Lean.

```bash
lake build
```

* `REPORT.md` — formal results per phase
* `DESIGN_DECISIONS.md` — every model choice and rejected alternative
* `MINIMALITY.md` — construct-by-construct kernel / surface / validation / remove table

Status: Phase 1 (cross-hole references, dependency) complete.
