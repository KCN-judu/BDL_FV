---
kind: report
phase: 11
area: surface
date: 2026-09-18
status: current
---

# Phase 11 — Natural expression surface as conservative desugaring

Question: can `all/any/map/filter x in xs: body`, `x in lo .. hi` and `x ?? d`
be added purely as surface elaboration over the Phase-9 library with no kernel
change and no semantic loss? Yes. Files: `BDL/Surface/Natural.lean`,
`BDL/Experiments/NaturalExamples.lean`; `filter_spec` added to `Stdlib.lean`;
note `docs/notes/natural-expression-surface.md`.

`NatExpr` (closed core embedding, named local, app, binder, range, coalesce)
with `desugar` under a binder stack: a local is the lambda parameter's de Bruijn
index (nearest binder). Proved: scoping (`desugar_local_nearest`,
`desugar_shadow`, `desugar_unbound`, `desugar_core`), alpha-equivalence under
fresh renaming (`desugar_rename`, `alpha`), no construction
(`desugar_constructs`), typing (`binder_*_typed`, `binder_local_type` inversion,
`range_typed`, `range_bounds_forced`, `coalesce_typed`), evaluation as the
library (`binder_*_eval` from `all_spec`/`any_spec`/`map_spec`/`filter_spec`;
`natural_forall`, `natural_exists`; `range_eval` = `lo ≤ x ∧ x ≤ hi`), clocks
(`binder_clock`, `range_clock`). Executed A–J: call-form vs natural-form
equality by `rfl`, units before ranges, nested binders, shadowing, alpha,
nominal `Tilt` ranges (concept bounds accepted, `q Angle` bounds rejected, `rep`
accepted), `MotorAngle` predicate rejected on a `Tilt` local, negatives
(`all x in 5`, `filter … : 5`, `angle in 2 s .. 3 s`, unordered concept, unbound
locals). Verdicts: all forms SURFACE-DESUGAR; interval type, general
comprehension and general quantifier REMOVE; `??` SURFACE-DESUGAR. 49 theorems
on `propext`/`Quot.sound`.
