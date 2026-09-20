---
kind: report
phase: M
area: core
date: 2026-09-14
status: current
---

# Migration (post-Phase 1) — Migration: holes → declarations

Performed after Phase 1, before Phase 2. Semantic-preserving; the declaration
inventory (201 `theorem`/`def`/`structure`/… items) is identical before and
after modulo the rename map, and the axiom profile is unchanged.

## M.1 Which names changed?

| Old                                                                     | New                                                                                                     |
| ----------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------- |
| `HoleId`                                                                | `DeclId`                                                                                                |
| `DesignHole` (field `spec`)                                             | `DesignDecl` (field `interface`)                                                                        |
| `HoleEnv`                                                               | `DeclEnv`                                                                                               |
| `Expr.holeRef`                                                          | `Expr.declRef`                                                                                          |
| `Expr.HoleFree` (+ `holeFree_*` lemmas)                                 | `Expr.RefFree` (+ `refFree_*`)                                                                          |
| `HoleLeq` / `HoleRefines` / `HoleRefinesStar` / `HoleRefinesStar_iff`   | `DeclLeq` / `DeclRefines` / `DeclRefinesStar` / `DeclRefinesStar_iff`                                   |
| `WellFormedHole`                                                        | `WellFormedDecl`                                                                                        |
| `Spec` (field `obligations`)                                            | `DeclInterface` (field `commitments`)                                                                   |
| `Refines`, `Refines_iff_semantic`, `Refines_addObligation`, `SpecEquiv` | `InterfaceRefines`, `InterfaceRefines_iff_semantic`, `InterfaceRefines_addCommitment`, `InterfaceEquiv` |
| `spec_refines`, `obligations_subset`                                    | `interface_refines`, `commitments_subset`                                                               |
| `NaiveHoleRefines` (experiment)                                         | `NaiveDeclRefines`                                                                                      |
| files `Hole.lean`, `Spec.lean`, `HoleCounterexamples.lean`              | `Decl.lean`, `Interface.lean`, `DeclCounterexamples.lean`                                               |

Kept unchanged: `tyView`, `Evidence`, `Evidence.Monotone`, `Satisfies`,
`GlobalWF`, `EnvRefines`, `DependsOn`, `Reaches`, `Unfolds`, `HasType`, `infer`,
all probe names. No aliases were retained.

## M.2 Which semantics changed?

None. Every definition is textually identical up to the rename; every theorem
statement and proof is unchanged. The build succeeded on the first attempt after
the mechanical rename, before any docstring was touched.

## M.3 Which semantics intentionally did NOT change?

- `tyView` still exposes only `expectedType`; the `declRef` typing rule still
  reads only `tyView`. Typing does not see commitments, realizations, or
  evidence.
- `Evidence` remains `DeclEnv → Expr → PropertyId → Prop`, and
  `Evidence.Monotone` is unchanged as a definition. Only its _description_
  changed: it is the stability condition for refinement-surviving evidence, not
  a claim about all evidence.
- Realization remains write-once; no edit relation was added.
- `DependsOn` remains realization-only; `Unfolds` remains the Phase-1 semantics;
  cycle results unchanged.
- Commitments and validation obligations are still the same `PropertyId`; the
  distinction is documented in `Interface.lean`, not implemented.

## M.4 Did any old theorem depend on the hole-centric formulation?

No. This was tested, not assumed: the rename was applied mechanically and the
whole project compiled without a single proof edit. Two identifiers
(`HoleRefinesStar_iff`, `NaiveHoleRefines`) were missed by the first
word-boundary pass and renamed in a second; that is a tooling detail, not a
semantic one.

The only place where the old vocabulary was doing conceptual work was in prose:
docstrings that described `realization = none` as "a hole" and described
`Evidence.Monotone` as a property of all valid evidence. Both were misleading
relative to the Phase-1 results and have been rewritten.

## M.5 Does the declaration-centric model better match the Phase-1 results?

Yes, and the fit is exact rather than cosmetic:

- Phase 1 proved that `id` is used only as an environment key
  (`EnvRefines_update`) — i.e. it _is_ a declaration name. `DeclId` says so;
  `HoleId` suggested a syntactic position that never existed in the model
  (nothing in `DesignDecl` mentions where a reference occurs).
- Probe 5 proved that commitments are load-bearing for dependents — i.e. they
  are part of the public interface. `DeclInterface.commitments` says so;
  `Spec.obligations` framed them as private proof duties.
- Probes 3–5 showed that retyping, dropping commitments, and re-identification
  are not covered by any preservation theorem. Documenting the refinement/edit
  split names that fact instead of leaving it implicit in which relations happen
  to exist.

## M.6 Kernel concepts vs surface metaphors, now

| Kernel (formal object)                                               | Surface metaphor / display                       |
| -------------------------------------------------------------------- | ------------------------------------------------ |
| `DeclId` — ordinary declaration key                                  | "hole", display name, `?f` notation              |
| `DesignDecl` with `realization = none`                               | "unresolved typed hole", "signature-first block" |
| `DeclInterface` = type + commitments                                 | "signature" plus "declared properties"           |
| `InterfaceRefines` / `DeclLeq` / `EnvRefines`                        | "progressive formalization"                      |
| edits outside the order (retype, drop, detach, replace, re-identify) | "editing the block" — must trigger rechecking    |
| `tyView`                                                             | what the type checker shows                      |
| `Evidence`, `Evidence.Monotone`                                      | validation overlay                               |

## M.7 Ready for Phase 2?

Yes, with two caveats stated honestly:

1. The vocabulary is clean, but the _representation_ still carries one Phase-0
   shortcut: `commitments : List PropertyId` doubles as the set of validation
   obligations. Phase 2 (semantic types) does not need to resolve this; Phase 11
   (validation) will.
2. No edit relation exists. Phase 2 will add semantic-type declarations; if it
   needs to talk about "changing a declaration's semantic type", it will have to
   say _edit_, not _refine_, and there is currently no formal object for that.
   This is intentional (nothing forces it yet), but it is the first thing to
   revisit if Phase 2 needs invalidation tracking.

No hole-centric terminology remains in the kernel, the experiments, or the
documents except where "hole" is named explicitly as a surface metaphor.
