# Natural Expression Surface as Conservative Desugaring

*A formal note on Phase 11 of the BDL development (`BDL/Surface/Natural.lean`,
`BDL/Experiments/NaturalExamples.lean`; `filter_spec` added to
`Stdlib.lean`), followed by production guidance for `KCN-judu/BDL`.*

## 1. The hypothesis, and the answer

Binder syntax (`all/any/map/filter x in xs: body`), closed ranges
(`x in lo .. hi`) and coalesce (`x ?? d`) are conservative surface
abstractions over the Phase-9 equation language: every form elaborates
into terms that already exist — the library combinator applied to an
ordinary lambda — and introduces no kernel type, expression, runtime
value, evaluator rule, clock rule or capability. Formally the surface
model is `NatExpr` (an embedded closed core term, a named binder local,
application, the four binders, a range, a coalesce) and `desugar`, a
one-way elaboration under a binder stack:

    all x in xs: p    ↦  app2 (allF τ) (lam τ p') xs'        (any, map, filter alike)
    x in lo .. hi     ↦  app3 (inRangeF o) x' lo' hi'
    x ?? d            ↦  app2 (getOrElseF τ) x' d'

A binder local *is* the kernel's lambda parameter: `desugar` resolves a
name to its de Bruijn index in the stack; nothing else is added.

## 2. What is proved (all on `propext`/`Quot.sound` only)

| claim | theorem |
|---|---|
| a local resolves to the nearest binder; shadowing; an unbound name is an error, not a free variable | `desugar_local_nearest`, `desugar_shadow`, `desugar_unbound` |
| ambient references are untouched by binders | `desugar_core` |
| alpha-equivalence: renaming a binder and its occurrences to a fresh name does not change the elaboration | `desugar_rename`, `alpha`; executed `exF` |
| binders construct no concept: no `mk` unless an embedded core has one | `desugar_constructs`, `no_construction` |
| typing: local at the element type; `all/any/filter` need a `bool` body, `map` gives `list σ` | `binder_all_typed`, `binder_any_typed`, `binder_map_typed`, `binder_filter_typed` |
| the local's type is *forced* by the collection (inversion) | `binder_local_type`; executed `local_type_forced` |
| range typing: `x`, `lo`, `hi` at one ordered type, by the 9c policy; other bounds rejected | `range_typed`, `range_bounds_forced` |
| evaluation is exactly the library's: `List.all/any/map/filter` | `binder_all_eval`, `binder_any_eval`, `binder_map_eval`, `binder_filter_eval` (from `all_spec`, `any_spec`, `map_spec`, `filter_spec`) |
| finite ∀/∃ meaning | `natural_forall`, `natural_exists` (from `forall_in_list`, `exists_in_list`) |
| range is `lo ≤ x ∧ x ≤ hi` on the compared magnitudes | `range_eval` (from `inRange_spec`) |
| clocks: the elaborated term is clocked iff its operands are | `binder_clock`, `range_clock` (from `lib_clocked`) |
| coalesce typing | `coalesce_typed` |

The conservativity family the brief asked for (`natural_elab_typed`,
`natural_elab_eval`, `natural_elab_clock`) is these per-construct
theorems; they cover exactly the six forms of `NatExpr`, no more.

## 3. Executed cases

A `all x in xs: x > 0` equals the hand-written call (`rfl`), types at
`bool`, true on `[1,2,3]`, false on `[0,1]`; `any`. B `map x in xs: x + 5`
= `[6,7,8]`; `filter`. C `angle in 10 deg .. 45 deg` after unit elaboration
(no unit reaches the kernel), true at 30°, false at 60°, and `lo ≤ x ≤ hi`
checked at 9/10/11/44/45/46°; the principle case `all reading in
readings: reading in 10 deg .. 45 deg`. D nested `all row in rows: any v
in row: v > 0`. E shadowing: `all x in xs: any x in ys: x > 5` — the inner
`x` ranges over `ys`; and a two-name variant. F alpha-renaming `x ↦ y`,
`x ↦ reading`, `x ↦ z` under shadowing. G nominal: `all t in tilts: t in
loT .. hiT` accepted with `Tilt` bounds, rejected with `q Angle` bounds,
accepted through `rep t` against `q Angle` bounds; a `MotorAngle`
predicate cannot take the `Tilt` local. H negatives: `all x in 5: true`,
`filter x in xs: 5`, `angle in 2 s .. 3 s`, an unordered concept in a
range (`ordB = false`), a binder variable outside its body, an unbound
name in a body. I `x ?? 0`. J no construction.

## 4. Verdicts

| construct | verdict |
|---|---|
| natural binder syntax `all/any/map/filter x in xs:` | KEEP IN SURFACE-DESUGAR (to the Phase-9 library + `lam`) |
| `BinderKind` | KEEP IN SURFACE-DESUGAR (an elaboration tag; the body type for `map` is inferred) |
| `Range` surface node `x in lo .. hi` | KEEP IN SURFACE-DESUGAR (to `inRangeF`; never a value, never stored, never compared) |
| interval kernel type | REMOVE — no case stores, passes, lists or compares a range |
| general comprehension (generators, `yield`, `where`) | REMOVE — nested binders cover every required case (`exD`, `exE`) |
| general quantifier (`∀`/`∃` as syntax, unbounded) | REMOVE — the forms are finite list equations (`natural_forall`) |
| coalesce `??` | KEEP IN SURFACE-DESUGAR (to `getD`; trivially conservative) |

Claim strength: proved for the six-form fragment; executed cases A–J;
minimal among the tested alternatives; no global compiler theorem.

## 5. Answers

* **Q1** No kernel change: `desugar` targets existing terms only.
* **Q2** Yes: a binder local is the lambda parameter (`desugar_local_nearest`, `binder_local_type`).
* **Q3** Yes: the local has the collection's nominal element type; `mk` is never introduced (`desugar_constructs`); a `MotorAngle` predicate cannot take a `Tilt` local (`nominal_slot`).
* **Q4** No: a range is a surface node elaborated to `inRangeF`.
* **Q5** Yes, completely (`exC` is `rfl` on the elaboration).
* **Q6** Yes: the same `Ordered` evidence and 9c policy; concept bounds for a concept value, `q d` bounds only through `rep`; unordered concepts rejected (`exG`, `negatives`).
* **Q7** No. **Q8** No.
* **Q9** No: evaluation is the library's (`*_eval`), clocks are the operands' (`*_clock`).
* **Q10** Yes, for the covered fragment: the elaborations are literally equal (`exA`, `exB`, `exC`, `exE`).

## 6. Production guidance for `KCN-judu/BDL`

Formally proved above: the elaboration targets and its typing,
evaluation, clock and nominality properties. Everything below is
engineering recommendation.

* **Parser / contextual keywords.** `all`, `any`, `map`, `filter` are
  contextual keywords only in the head position `kw Ident in Expr :`; `in`
  is contextual inside that head and in `Expr in Expr .. Expr`. Elsewhere
  they remain identifiers, so existing designs that name a concept `all`
  keep parsing.
* **Binder local scope.** The local is visible in the body only; nested
  binders shadow (nearest wins, `desugar_shadow`); a local used outside
  its body or an unbound name is `formula.name.unknown` with the binder
  locals in scope listed as fixes.
* **CST / formatter.** Keep the natural form as authored; never
  reconstruct binder syntax from Core (elaboration is one-way). Two
  spellings of one term — `all(xs, x => p)` and `all x in xs: p` — are
  intentional and both stay as written.
* **`..` precedence.** Bind `..` tighter than `in` and looser than
  arithmetic: `x in lo + 1 .. hi - 1` parses as `x in (lo+1) .. (hi-1)`;
  a range expression is legal only as the right operand of `in` — it is
  not a value (`Range` has no other parent in the CST).
* **Local type inference.** Element type from the collection's inferred
  type (`list τ ⇒ x : τ`), exactly the kernel's `binder_local_type`; body
  checked at `bool` (`all/any/filter`) or inferred (`map`); range: the
  value's type must admit `Ordered` under the 9c policy and both bounds
  must have that same type — report "expected a Tilt bound; a `q Angle`
  needs `rep`" in concept language.
* **FormulaProjection.** Project the natural form to the same Core term
  as the call form; projections are of Core, so nothing new.
* **Formula Composer.** Represent a binder as a node with a fresh local
  name (`x₁`, `x₂`, …); `desugar_rename` guarantees fresh names are
  semantically invisible; a range slot is two expression slots of the
  value's type.
* **Rename / references.** A binder local is a local symbol with its own
  definition site; rename is textual within the body and, by `alpha`,
  meaning-preserving whenever the new name is fresh in the formula.
* **Semantic tokens.** Binder keyword; local (definition and uses);
  range operator.
* **Diagnostics.** "`5` is not a collection"; "the condition after `:`
  must be true or false"; "these bounds are times; `angle` is an angle";
  "Mode values have no order, so `in lo .. hi` does not apply";
  "`y` is not defined here (locals in scope: `x`)".
* **Backward compatibility.** Additive: no existing formula changes
  meaning; the call forms remain valid and elaborate identically.

## 7. Not established

No parser is modelled; type annotations in `NatExpr` are the *output*
of local inference, which is described, not proved. Negative magnitudes
(`-45 deg`) are outside the `Nat` kernel's executed examples (exact in
the Phase-10 symbolic model). The forms are the six of `NatExpr`.
