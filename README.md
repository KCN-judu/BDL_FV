# PersistentHole

A deliberately small Lean 4 formalization testing one question:

> Can a typed hole be modeled as a persistent, referable design entity whose
> specification is progressively refined — preserving identity and earlier
> commitments — until it is realized by a concrete term?

No dependencies beyond core Lean (no Mathlib). Builds with

```bash
lake build
```

| File | Contents |
|---|---|
| `PersistentHole/Syntax.lean` | Tiny STLC, `HasType`, decidable `infer`, uniqueness of typing |
| `PersistentHole/Spec.lean` | `Spec`, `Refines` (preorder), `Evidence`, `Satisfies`, Theorem 5, completeness of `Refines` |
| `PersistentHole/Hole.lean` | `HoleId`, `DesignHole`, `WellFormedHole` |
| `PersistentHole/Refinement.lean` | `HoleRefines`, Theorems 1–6, closure `HoleRefinesStar`, characterization `HoleLeq` |
| `PersistentHole/Artifact.lean` | References by id, hole environments, stability of references under refinement |
| `PersistentHole/Examples.lean` | Concrete lifecycle checked by `decide`; counterexamples A–D |
| `REPORT.md` | Findings |
