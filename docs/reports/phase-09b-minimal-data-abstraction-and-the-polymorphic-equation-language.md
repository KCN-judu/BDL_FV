---
kind: report
phase: 9b
area: surface
date: 2026-09-17
status: current
---

# Phase 9b — Minimal data abstraction and the polymorphic equation language

Research question (brief §1): the smallest typed data/function basis for
reusable equations, generic collection operations, conditions over finite
collections, ranges, min/max/clamp, pairs, designer predicates and finite
any/all, preserving nominal identity, dimensions, determinism, clocks, the grant
discipline and a small kernel. Files: kernel changes in `Base`, `Typing`,
`Dependency`, `Reactive`, `Clock` (+ `Rename`, experiments);
`BDL/Surface/Poly.lean` (schemes, matching), `BDL/Surface/Stdlib.lean` (the
definitional library, its typing and evaluation theorems),
`BDL/Surface/Generic.lean` (nominality through generics; structural equality),
`BDL/Experiments/PolyAlternatives.lean` (models A–E, toy System F, constraints),
`BDL/Experiments/EquationExamples.lean` (cases A–M). Design note with the
production guidance: `docs/notes/polymorphic-equation-language.md`.

## 9b.1 The kernel extension (all of it)

| addition                                           | why not derivable                                                                                                  | proved                                                                                                                        |
| -------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------ | ----------------------------------------------------------------------------------------------------------------------------- |
| `Ty.prod`, `Value.pair`, `pair`/`fst`/`snd`        | function encodings are arrows, not data: `arrow_not_delayable`; Church pairs need rank 2: `church_fst_rank`        | `prod_data`; `pair_state_delayable`; `Red` product clause                                                                     |
| `Expr.fold f z l` (list recursor, a term former)   | no recursion in the kernel; the one construct that applies a function value during evaluation — operators never do | `HasType.fold`, `infer` rule, `Ev.foldNil/foldCons` (syntactic unrolling through the environment), `fold_total`/`mfold_total` |
| `eq τ h`, `lt τ h` at every data `τ` (proof field) | equality on `bool`/`sem`/pairs/lists was unwritable; production encoded boolean equality                           | `Value.beq`/`blt` structural; `Red_prim`; `Value.beq_iff` on first-order values                                               |
| `drop τ`, `toList τ`                               | `toList` makes `fold` the option eliminator; `drop` for `zip`                                                      | `Red_prim` cases                                                                                                              |

Every earlier theorem was re-established with unchanged statements: `Ev.det`,
`MEv.det`, `reactive_total`, `multi_domain_total`, `Ev.tag_provenance`,
`MEv.tag_provenance`, `Ev.noClo`, `unfolds_preserves_eval`,
`single_domain_embedding`, `HasType.rename`, `Clocked.rename`, the Phase-8a/8b
semantics theorems (`eval_flat_to_inst`, `eval_inst_to_flat`,
`eval_orig_to_flat`), the 9a buffer. New kernel lemmas: `Ev.pure` (a pure term
in a pure environment has the same value in every design, input and tick),
`Ev.noCloV`, `Ev.foldCons_move`.

## 9b.2 Polymorphism: models A–E

| model                  | verdict                            | evidence                                                                                                                                                                                                                        |
| ---------------------- | ---------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| A monomorphic kernel   | KEEP                               | unchanged rules                                                                                                                                                                                                                 |
| B duplication per type | what the kernel sees               | `instances_are_monomorphic`                                                                                                                                                                                                     |
| C rank-1               | **ADOPT as definitional families** | every `Stdlib` entry is `Ty → Expr`/`Dim → Expr` with `*_typed` at every instance; use-site instantiation = matching: `matchTy_sound`, `matchTy_complete`, `Scheme.instantiate_sound`; `min_instantiation`, `sum_instantiation` |
| D System F             | REJECT                             | toy `FTy`, `rank`; prenex = family instantiation                                                                                                                                                                                |
| E higher rank          | REJECT                             | `applyBoth_rank = 2`, `existential_rank = 2`; `applyBoth_replacement`                                                                                                                                                           |

Constraints: closed vocabulary {Data}; `Scheme.dataVars`; the `eq`/`lt` proof
field enforces it in the kernel syntax; `minByF` shows dictionary passing
collapses to a comparator argument. Dimension variables: `PDim.dvar`, no kind
system (`sumScheme`).

## 9b.3 Nominality and dimensions through generics

`generic_preserves_identity`, `generic_preserves_dimension` (any family at
`α → α → α`), `pair_projections_keep_concepts`, `map_keeps_concepts`,
`eq_across_concepts_rejected`; executed `exI`, `exJ` (`infer = none` for the
mixed uses). Library discipline: `lib_comb`, `HasType.comb_irrelevant`,
`lib_eval_context_free`, `lib_clocked`, `Comb.noConstruct`, `lib_expansion`
(typing, construction, clocking of an inlined use).

## 9b.4 Collections and the derived vocabulary

| designer form                                                | elaboration                         | theorem                                                                  |
| ------------------------------------------------------------ | ----------------------------------- | ------------------------------------------------------------------------ |
| `any xs P` / `exists x in xs, P`                             | `fold` with `or`                    | `any_spec`, `exists_in_list`                                             |
| `all xs P` / `forall x in xs, P`                             | `fold` with `and`                   | `all_spec`, `forall_in_list`                                             |
| `x in {c₁,…}`                                                | `contains x [c₁,…]`                 | `contains_spec`, `oneOf_mem`, `oneOf_dup_irrelevant`                     |
| `map`, `filter`, `append`, `sum`, `zip`, `optElim`, `mapOpt` | folds                               | `map_spec`; typed at every instance; executed F, G, H, `options_by_fold` |
| `min`, `max`, `clamp`, `inRange`, interval                   | `lt` + `ite`                        | `min_spec`, `max_spec`, `clamp_spec`, `inRange_spec`                     |
| records                                                      | nested pairs, positional projection | `recE_typed`, `projE_typed`, `records_are_pairs`                         |
| enums with payload                                           | tag × optional payload              | `exM` (executed; kernel `sum` deferred)                                  |

## 9b.5 Cases A–M (executed, `decide` through `Value.beq`)

A clamp Brightness (5 ↦ 10, 100 ↦ 90, result still Brightness); B mode ∈ {1,2};
C all temperatures below threshold; D any severe fault; E (temperature,
humidity) and `fst`; F map a calibration; G zip two collections (truncating); H
`head xs` or default; I `min` at `q Length` typed, mixed with `q Time` rejected;
J `min` at Brightness typed, Opacity rejected, `eq`/`contains` across concepts
rejected; K `hum ∈ [30, 60]`; L a piecewise rule over a range, a collection
predicate and a boolean; M an enumeration with a payload. `examples_well_typed`
(`GlobalWF` by `decide`), `examples_causal`.

## 9b.6 Minimality audit

| construct                                                                                                                                                     | verdict                                                 |
| ------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------- |
| `prod`, `fold`, generic `eq`/`lt`, `drop`, `toList`                                                                                                           | KEEP IN KERNEL                                          |
| rank-1 polymorphism                                                                                                                                           | KEEP IN SURFACE (families + matching); kernel untouched |
| capability constraints                                                                                                                                        | closed {Data}; enforced syntactically                   |
| records, set literals, intervals, min/max/clamp, any/all, map/fold library, `fn` helpers, finite quantifier syntax, piecewise notation, enums                 | KEEP IN SURFACE-DESUGAR                                 |
| `Set` type, record type, typeclasses, higher-rank, System F terms, existentials, row polymorphism, GADTs, dependent types, general quantifiers in expressions | REMOVE / REJECT                                         |
| unbounded quantification, symbolic obligations, physical invariants                                                                                           | MOVE TO VALIDATION (future)                             |
| kernel `sum`                                                                                                                                                  | DEFER (encoded)                                         |

Claim strength: "smallest design found that supports the required cases",
minimal among the tested candidates; no global minimality theorem.

## 9b.7 Answers

1. weakest useful polymorphism: rank-1 by families, constrained by Data;
2. products in the data core: yes; 3. kernel Set: no; 4. finite ∀/∃ as folds:
   yes, proved; 5. existentials: no; 6. user typeclasses: no;
3. ceiling: total first-order-data computation with higher-order functions and
   one list recursor, generic definitions instantiated at closed types.

## 9b.8 What is not established

Library evaluation lemmas assume an "implements" hypothesis on the predicate
value; `sum` types are encoded not added; the structural order on `sem s` is the
representation's; no minimality theorem.
