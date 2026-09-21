---
kind: note
phase: 9b
area: surface
date: 2026-09-17
status: current
---

# Minimal Data Abstraction and the Polymorphic Equation Language

_A formal note on Phases 9b and 9c of the BDL development (`BDL/Core/Base.lean`,
`Typing.lean`, `Reactive.lean`, `Clock.lean` — kernel; `BDL/Surface/Poly.lean`,
`Stdlib.lean`, `Generic.lean` — surface;
`BDL/Experiments/PolyAlternatives.lean`, `EquationExamples.lean` — alternatives
and executed cases), followed by production guidance for `KCN-judu/BDL`._

## 1. The question and the answer in one paragraph

The question was the smallest typed data/function basis that supports reusable
equations, generic collection logic, conditions over finite collections, ranges,
min/max/clamp, pairs, designer predicates and finite any/all quantification,
while keeping nominal identity, dimensions, determinism, the clock semantics,
the grant discipline and a small explainable kernel. The smallest design found
that supports every required case is: the existing monomorphic core, plus
**products** (`A × B`), plus **one list recursor** (`fold`) as a term former,
plus **structural equality on every data type** (`eq` at any `Data` type;
ordering `lt` stays a _quantity_ comparison — Phase 9c, §11), plus two
first-order list/option operators (`drop`, `toList`). Nothing else entered the
kernel. Parametric polymorphism is real but definitional: a generic equation is
a family of monomorphic kernel terms indexed by the types (and dimensions) it is
used at, instantiated by first-order matching at the use site. The kernel never
sees a type variable, a type abstraction, a constraint, a set, an interval, a
record or a quantifier.

## 2. What was added to the kernel, and why each item could not be derived

| addition                                                                | verdict                                                                  | why not derived                                                                                                                                                                                                                                                                                                                                                     |
| ----------------------------------------------------------------------- | ------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Ty.prod a b`, `Value.pair`, `pair`/`fst`/`snd`                         | KEEP IN KERNEL                                                           | a pair encoded as a function is an arrow, and arrows are not data: they cannot be delayed or transported (`arrow_not_delayable`). Paired state (`delay` at `prod`, `pair_state_delayable`) needs a data product. The Church encoding also needs rank-2 types to be first-class (`church_fst_rank`).                                                                 |
| `Expr.fold f z l`                                                       | KEEP IN KERNEL                                                           | the kernel has no recursion; a total language needs an eliminator for its inductive data. `fold` is the _one_ term former that applies a function value during evaluation — registered operators still never do. `map`, `filter`, `any`, `all`, `contains`, `append`, `sum`, `zip`, `optElim`, `mapOpt` are definitions over it.                                    |
| `eq τ h` for every data `τ` (was `q d` only); `lt d` on quantities only | KEEP IN KERNEL (`eq` generalized; `lt` **reverted** to quantities in 9c) | equality on `bool`, `sem s`, pairs, lists and options was not writable; production encoded boolean equality as `(a∧b)∨(¬a∧¬b)`. The proof field `h : τ.Data` makes an inadmissible instance unwritable. Ordering is not a property of data: 9c found no behaviour-design meaning for `<` on modes, pairs, lists, options or booleans, so the kernel has none (§11). |
| `drop τ`, `toList τ`                                                    | KEEP IN KERNEL (registered operators)                                    | `toList : opt τ → list τ` makes `fold` eliminate options too — without it `opt` has no eliminator that does not need a default. `drop` is the dual of `take`; `zip` needs it.                                                                                                                                                                                       |

Every earlier theorem — determinism, totality in one and many domains,
provenance, unfolding, the Phase-8 preservation results, the Phase-9a buffer —
was re-established without change of statement. The logical relation gained the
product clause, and totality of `fold` is a separate lemma by induction on the
list (`fold_total`, `mfold_total`).

## 3. Polymorphism: rank-1, by families, no kernel type variables

The five models of the brief:

| model                          | status                                | evidence                                                                                                                   |
| ------------------------------ | ------------------------------------- | -------------------------------------------------------------------------------------------------------------------------- |
| A — monomorphic STLC kernel    | kept, unchanged                       | typing rules unchanged; `HasType.unique`                                                                                   |
| B — per-type duplication       | what the kernel _sees_                | `instances_are_monomorphic`: three uses of `min` are three kernel terms                                                    |
| C — rank-1 parametric          | **adopted, as definitional families** | every library entry is `Ty → Expr` (or `Dim → Expr`); `*_typed` prove its scheme at every instance                         |
| D — System F (`Λ`, `[τ]`, `∀`) | rejected                              | a toy `FTy` with `rank` shows what it would add; its prenex fragment _is_ instantiation of families                        |
| E — higher rank                | rejected                              | every candidate use has rank ≥ 2 (`applyBoth_rank`, `existential_rank`) and a rank-1 replacement (`applyBoth_replacement`) |

Why C needs no kernel support: a use site always has _closed_ argument types —
every declaration's expected type is frozen and closed since Phase 1, and
`infer` is bottom-up — so finding the instance is one-way matching of the scheme
against closed types (`matchTy`), which is decidable and returns the unique
substitution on the scheme's variables (`matchTy_sound`, `matchTy_complete`).
There is no unification of two open types, no let-generalization inside
expressions, and no principal type search: those problems arise when a
_definition_ is inferred from its body. BDL definitions carry their signature
(mappings do already; a helper `fn` would too), so the elaborator only ever
instantiates.

Dimension polymorphism (`sum : list (q d) → q d`, `min` at `q d`) uses the same
mechanism with dimension variables (`PDim.dvar`, `sumScheme`). No kind, no
`Type + Dim` universe, no `Fω`: the dimension algebra already lives in the
primitive table, so a dimension variable is just a second kind of pattern
variable in the elaborator.

Constraints (§5, revised by the 9c audit, §11): the closed vocabulary is
**{Data, Eq, Ord}** (`Poly.Cap`). `Data` is what `delay`/`sync` need and what
the kernel's one proof field (`eq τ h`) checks; `Eq` coincides with `Data` on
the current type grammar (`Cap.eq_iff_data`, a proved coincidence kept as a
separate name for diagnostics); `Ord` is a _surface_ capability — a quantity, or
a concept the designer declared ordered and represented by a quantity
(`Ty.ordB`, `Stdlib.Ordered`) — with no kernel counterpart: an ordered concept
compares through `rep`. A scheme lists the capability of each variable
(`Scheme.caps`); instantiation checks them (`Scheme.instantiate_sound`).
`Numeric` is not a constraint but a shape (`q d`), matched directly.
User-definable classes were not needed by any behaviour-design case: a
designer's custom order is an explicit comparator argument (`minByF`), proved to
recover `min` (`minBy_recovers_min`), which is what dictionary passing would
produce anyway.

## 4. Nominality survives generics — proved

`generic_preserves_identity`: _any_ family typed at `α → α → α`, instantiated at
concept `s`, rejects an argument of concept `s' ≠ s`; the representations are
not consulted. `generic_preserves_dimension` is the same for `q d` vs `q d'`.
Through pairs (`pair_projections_keep_concepts`), through lists and `map`
(`map_keeps_concepts`), through equality (`eq_across_concepts_rejected`) — no
path identifies Brightness with Opacity though both are `q 0` underneath.
Executed: `exJ` (`min` at Brightness typed; with an Opacity argument
`infer = none`; `eq` and `contains` across concepts `= none`), `exI` for
dimensions.

The library adds no privilege: every entry is a _combinator_ — no reference, no
state, no transport, no `rep`, no `mk` (`lib_comb`) — and for combinators typing
is independent of the design, the concept environment and the grant
(`HasType.comb_irrelevant`), the value is the same in every design at every tick
(`lib_eval_context_free`, from `Ev.pure`), the domain judgment is that of the
argument alone (`lib_clocked`, `lib_expansion`), and no semantic value is
constructed (`Comb.noConstruct`). That is the expansion/inlining story of §21 of
the brief, proved once for the whole library.

## 5. Collections, sets, predicates, intervals, quantifiers, records

- **Lists.** `fold` is the eliminator; the collection operations are
  definitions, each proved to compute the mathematical function: `any_spec` (=
  `List.any`), `all_spec` (= `List.all`), `contains_spec` (=
  `List.any (beq x)`), `map_spec` (= `List.map`); `min_spec`, `max_spec`,
  `clamp_spec`, `inRange_spec` by the structural order. `filter`, `append`,
  `sum`, `zip`, `optElim`, `mapOpt` are typed at every instance and executed
  (`exF`, `exG`, `exH`, `options_by_fold`).
- **Finite quantification.** `forall_in_list`: `∀ x ∈ xs, P x` iff `all xs P`
  evaluates to `true`; `exists_in_list` likewise with `any`. For a finite list
  the logical quantifier and the executable fold coincide; no quantifier enters
  the expression language.
- **Sets.** No kernel `Set`. `x ∈ {c₁,…,cₙ}` is `contains x [c₁,…,cₙ]`
  (`oneOfE`), and it means membership (`oneOf_mem`, via `beq_iff` on first-order
  values); duplicates do not change the answer (`oneOf_dup_irrelevant`), so a
  uniqueness convention is unnecessary for membership. Set _algebra_ (union,
  difference) is list definitions when needed; nothing tested needs a canonical
  form.
- **Predicates.** `Predicate α = α → bool` is an ordinary function type; every
  predicate use above is an ordinary lambda.
- **Intervals.** A pair with the convention `(lo, hi)`; membership is a function
  of the pair (`inIntervalF`), `clamp` is `max lo (min x hi)`.
- **Records.** Labeled products elaborate to right-nested pairs (`recTy`,
  `recE`, `projE`; `recE_typed`, `projE_typed`, `records_are_pairs`). Labels
  resolve to positions at elaboration; no row polymorphism, and no record type
  in the kernel.
- **Enumerations.** Production's
  `enum LampMode { Off, Automatic, Manual(Brightness) }` is encodable as a tag
  paired with an optional payload, with `match` as conditionals on the tag
  (`exM`). A kernel sum type is _deferred_: nothing tested needs more than this
  encoding gives; the cost of a kernel `sum` would be one more term former for
  its eliminator, exactly like `fold`.

## 6. What was rejected, and why the use cases do not justify it

| family                                     | verdict          | reason                                                                                                                                                                                                          |
| ------------------------------------------ | ---------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| higher-rank types                          | REJECT           | no behaviour-design case passes a polymorphic function as a value; each candidate is two instantiations and a pair (`applyBoth_replacement`)                                                                    |
| System F term-level `Λ`/`[τ]`              | REJECT           | the prenex fragment is family instantiation; the extra syntax would exist only to be erased                                                                                                                     |
| user-defined typeclasses / dictionaries    | REJECT           | the closed vocabulary {Data} covers `eq`/`lt`/`delay`/`sync`; custom orders are comparator arguments                                                                                                            |
| row polymorphism                           | REJECT           | records are positional nested pairs resolved at elaboration; no case needs a function generic over record shapes                                                                                                |
| existential types                          | REJECT           | hiding is provided by Phase 8a components: private concepts and identities are freshened per instance (`inst_decl_disjoint`), the public contract is the interface; the encoding is rank 2 (`existential_rank`) |
| GADTs, dependent types, impredicativity    | REJECT           | no case; the kernel's only type-level computation is the dimension algebra in `Prim.ty`                                                                                                                         |
| effect systems                             | REJECT (Phase 6) | unchanged                                                                                                                                                                                                       |
| a `Set` type                               | REJECT           | membership is a fold; canonical forms are not observable by any tested case                                                                                                                                     |
| general logical quantifiers in expressions | REJECT           | `forall_in_list`/`exists_in_list` cover finite collections; unbounded `∀ x : Real` belongs to the commitment/validation layer, which this phase did not build                                                   |

## 7. Decidability, inference and diagnostics

- Kernel typing is syntax-directed and decidable (`infer`, unchanged in
  character; `fold` is one more syntax-directed rule).
- Use-site instantiation is first-order matching against closed types:
  decidable, unique, no search (`matchTy_sound`/`_complete`,
  `Scheme.instantiate_sound`).
- The two failure points have designer-level explanations: _no instance_ (the
  argument does not fit the scheme's shape: "expected a collection") and
  _constraint failed_ (a type variable at a function type: "cannot compare
  functions"). A nominal mismatch is reported by the kernel's own unique typing
  as "Brightness and Opacity are different concepts"
  (`generic_preserves_identity`) — never as a unification residue, because there
  is no unification.
- Explicit annotations at public boundaries remain the rule: every declaration's
  type is frozen; a definitional helper carries its scheme.

## 8. The seven questions

1. **Weakest useful polymorphism.** Rank-1, realized as type- and
   dimension-indexed families of monomorphic terms instantiated by matching;
   constrained by the closed vocabulary {Data, Eq, Ord}, of which only `Data`
   has kernel evidence. No kernel type variable.
2. **Products in the data core.** Yes: `prod` is data, so paired state can be
   delayed and transported; function encodings cannot (`arrow_not_delayable`).
   Products are value composition only — never component interfaces, output
   bundles or system structure (Phases 6, 8a/8b are untouched).
3. **A kernel Set type.** No. Finite-set literals are `contains` over a list
   literal (`oneOf_mem`).
4. **Finite forall/exists as folds.** Yes, proved: `forall_in_list`,
   `exists_in_list`.
5. **Existential types today.** No; Phase-8a components already hide
   representation and identity.
6. **User-defined typeclasses.** No; the closed vocabulary {Data, Eq, Ord} plus
   explicit comparator arguments covers the standard library.
7. **Expressiveness ceiling.** Total, first-order-data computation over `bool`,
   quantities, nominal concepts, options, lists and pairs, with higher-order
   functions and one list recursor; generic definitions instantiated at closed
   types; no general recursion, no type abstraction in terms, no sums yet
   (encoded), no unbounded quantification. This is a _design recommendation_
   backed by the twelve executed cases and the proved library, not a minimality
   theorem: minimal among the tested candidates.

## 9. Claim discipline

Formally proved: everything named above in `Poly`, `Stdlib`, `Generic`, the
kernel theorems (`fold_total`, `Ev.pure`, the preservation of every earlier
result). Executable examples: `exA`–`exM`, `records_are_pairs`,
`options_by_fold`, `min_instantiation`, `sum_instantiation`. Type-system
experiments: the toy `FTy` and its ranks. Design recommendations: the surface
vocabulary (§10), the deferral of sums, the diagnostics wording. Rejected
alternatives: §6.

## 10. Production guidance for `KCN-judu/BDL`

What exists today (inspected): `bdl-ir` mirrors the kernel without
`list`/`prod`/`fold` and with `Lt`/`Eq` on `Q` only; the formula elaborator
(`bdl-elab/formula.rs`) types first-order surface expressions (`STy`: `Q`,
`Bool`, `Nat`, `Sem`, `Opt`), supports `if`, `match` on `Option`, calls to
mappings, and — per ADR-0013 — has no user functions or loops and encodes
boolean equality; `enum` parses but is not part of the design (DI-19); the
standard library is a _concept_ library (templates), not an equation library.

| layer                                | what to implement                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| ------------------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **core IR** (`bdl-ir`)               | `Ty::List`, `Ty::Prod`; `Expr::Fold { f, z, l }`; `Prim::{Pair, Fst, Snd, Nil, Cons, Length, Take, Drop, Reverse, Head, ToList}`; generalize `Prim::Eq` to `{ ty }` with the `is_data` check at construction; **keep `Prim::Lt { dim }` on quantities only** (9c). `Value::List`, `Value::Pair`; structural `beq` on values (closures compare false); **no `blt`** — any ordering the compiler needs for maps or serialization is internal and never surfaces as `<`.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| **type checker** (`bdl-check`)       | the `fold` rule; `is_data` on `prod`/`list`; nothing else — the checker remains the authority and stays monomorphic. Reject `Eq` at non-data types at IR construction, not by a typing rule; `Lt` is dimension-indexed as before.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| **reference evaluator / codegen**    | `fold` by iteration (`foldr`; a stack-free `foldl` over `reverse` is equivalent for finite lists); pairs and lists as values; `beq`/`blt` structural. No closure escapes into state: the `Data` check already guarantees it.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| **elaborator** (`bdl-elab`)          | (1) schemes as patterns with type and dimension variables; use-site instantiation by matching (`matchTy`), then the capability check (`Data`/`Eq`: `is_data`; `Ord`: a quantity, or a concept marked `ordered` in the project with a quantity representation — `Ty.ordB`); `<`/`min`/`max`/`clamp`/`inRange` on an ordered concept elaborate to the quantity comparison of `rep`s (`ltAt`), returning the original values; (2) the definitional library as _elaboration templates_ producing closed Core terms (`Stdlib.lean` is the reference: each entry is a closed de Bruijn term); (3) records → nested pairs with positional projections; finite-set literals → `contains` over a list literal; intervals → pairs; `forall x in xs, P` → `all xs (λx. P)`, `exists` → `any`; `fn` helpers → closed lambdas inlined at each use (no declaration is created; §21 guarantees nothing changes); (4) `enum` → tag × optional payload, `match` → conditionals on the tag; (5) replace the boolean-equality encoding by `Eq { ty: Bool }`. |
| **parser / surface** (`bdl-syntax`)  | list literals `[a, b]`, set literals `{a, b}`, tuple literals `(a, b)`, record literals `{ temperature: …, humidity: … }`, range forms `x in [lo, hi]`, `forall x in xs, P` / `exists x in xs, P`, lambda-free predicate syntax (`all(xs, x => P)` or the quantifier form), `fn name<T>(…) : … = …` with an explicit signature; no `Λ`, no `∀` in user types.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| **standard library** (`bdl-library`) | a second library beside concepts: equation templates with schemes and Core bodies (`id, const, swap, min, max, clamp, inRange, inInterval, any, all, contains, map, filter, append, sum, foldr, optElim, mapOpt, getOrElse, zip`), data-driven like `concepts.toml`, versioned; a template change never changes a stored design because bodies are inlined at analysis time.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| **IDE** (`bdl-ide`, Studio)          | expose _intent_ forms only — "any", "all", "in range", "one of", "pair", "optional value", "collection", "clamp", "reusable equation"; never show schemes, folds, products or `Data`. Diagnostics in concept language ("Brightness and Opacity are different concepts", "expected a collection of Temperature", "cannot compare functions").                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| **validation**                       | unchanged: capacity for buffers (9a), hardware (7). Unbounded logical quantification, symbolic obligations and physical invariants remain a future commitment layer, not expressions.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |

Do not implement: type variables in Core IR, a `Set` type, a record type,
typeclasses, higher-rank types, existentials, a kernel sum type (until a case
needs exhaustiveness beyond the tag encoding), or any new temporal, output or
component construct.

## 11. The Phase-9c capability audit: Data vs Eq vs Ord

**Question.** Does "may be delayed/transported as data" imply "has meaningful
equality", and does that imply "has meaningful ordering"?

**Findings, by type, for a behaviour designer:**

| expression                          | meaning                                                                                                  | verdict                                                                        |
| ----------------------------------- | -------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------ |
| `temperature1 == temperature2`, `<` | magnitude comparison of one quantity                                                                     | Eq, Ord (`q d` only; `q Length < q Time` rejected as before, `exI`)            |
| `brightness1 < brightness2`         | the concept is a magnitude the designer declared ordered                                                 | Ord _by declaration_, through the representation (`Ordered.sem`, `exA`, `exJ`) |
| `mode1 == mode2`                    | same mode                                                                                                | Eq                                                                             |
| `mode1 < mode2`                     | none — any order would come from a code, a constructor tag or a `ConceptId`                              | **rejected** (`lt_rejected`, `min_mode_rejected`)                              |
| `pair1 == pair2`                    | same reading (both components)                                                                           | Eq                                                                             |
| `pair1 < pair2`                     | lexicographic order is a mathematical convenience with no design meaning ("is (temp, hum) less than …?") | **rejected**                                                                   |
| `list1 == list2`                    | same collection, same order                                                                              | Eq                                                                             |
| `list1 < list2`                     | none                                                                                                     | **rejected**                                                                   |
| `optional1 == optional2`            | both absent, or both present and equal                                                                   | Eq                                                                             |
| `None < Some x`                     | a constructor-tag artifact                                                                               | **rejected**                                                                   |

So: `Data ⇒ Eq` holds (extensionally, on this grammar: `Cap.eq_iff_data`), but
`Eq ⇏ Ord`. The Phase-9b choice — `lt` at every data type through a structural
order — was formally consistent and semantically wrong: it exposed
`mode1 < mode2`, `None < Some x` and lexicographic pairs/lists as language
capabilities. Phase 9c removed the structural order from the kernel entirely
(`Value.blt` deleted, `lt d` restored to quantities), which also makes 9b
_smaller_.

**Models compared** (§2 of the 9c brief):

| model                                     | verdict                                                                                                                                                                                             |
| ----------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| A {Data} for both `eq` and `lt`           | rejected: conflates state with order                                                                                                                                                                |
| B {Data, Eq}, `lt` on ordered shapes only | correct at the kernel: `eq` on Data, `lt` on `q d`; but the _surface_ must still name Ord for ordered concepts                                                                                      |
| C {Data, Eq, Ord} closed capabilities     | **adopted at the surface** (`Poly.Cap`); `Ord` = quantities + declared-ordered concepts; the kernel needs no Ord evidence because an ordered concept's `<` is `lt d` on `rep` — already expressible |
| D user-defined typeclasses                | rejected: no case; instance search and superclasses unnecessary                                                                                                                                     |
| E comparators only                        | kept as the escape hatch: `minByF`/`maxByF`, with `minBy_recovers_min` proving the comparator form loses nothing                                                                                    |

**Internal vs language order.** A compiler may need a total order on values for
maps, canonical forms, serialization and tests. That is an implementation detail
of the toolchain and is _not_ `<` in BDL: the kernel has no such order, and
`Ty.ordB` never grants one to a non-quantity.

**Enums.** Equality is natural; ordering is not automatic. Declaration order
must never silently become behavioural order: an enumeration is ordered only if
declared so, exactly like a concept (the same `OrdDecl` flag is the intended
production mechanism).

**Kernel minimality.** Eq/Ord never appear as kernel types or classes. The
kernel carries one capability proof field (`eq τ (h : τ.Data)`) and one
dimension-indexed comparison (`lt d`). The kernel is monomorphic.

**Re-proved after the change** with unchanged statements: determinism, totality
(`fold_total`, `mfold_total`), provenance, library expansion (`lib_expansion`,
with `rep` now admitted in combinators and Θ held fixed), finite quantifiers,
the 9a buffer, the Phase-8 preservation theorems,
`generic_preserves_identity`/`_dimension`; 178 theorems in the 9a/9b/9c modules
audited on `propext`/`Quot.sound` only.

**Stdlib reclassification.** Eq: `contains`, `oneOf`, equality predicates. Ord:
`min`, `max`, `clamp`, `inRange`, `inInterval` (all take `Ordered` evidence).
Neither: `map`, `fold`, `any`, `all`, `filter`, `append`, `zip`, `optElim`,
`mapOpt`, `sum` (dimension-indexed).

**Diagnostics.** "Mode values can be compared for equality, but they have no
default order" (Ord failed on a concept not declared ordered); "a pair has no
order — compare its components" (Ord on `prod`); "cannot compare functions"
(Eq/Data on an arrow); never a class-solving residue, because there is no class
solving.

**Final answer to the 9c question.** `Ty.Data` is a sufficient boundary for
_equality_ and for _state_ — not for _ordering_. The smallest closed split that
supports every tested case is {Data, Eq, Ord} at the surface with Eq ≡ Data
today and Ord = quantities ∪ declared-ordered concepts (represented by
quantities), and nothing but `eq τ (h : τ.Data)` and `lt d` in the kernel. Claim
strength: minimal among the tested models; an executed and proved
reclassification, not a minimality theorem.

## 12. Assumptions and limits

- `contains`/`oneOf` use structural equality on data values; `min`/`max`/
  `clamp`/`inRange` use the quantity order, on a concept through its
  representation and only when the concept is declared ordered (§11).
- Library evaluation lemmas are stated with an "implements" hypothesis on the
  predicate/function value (`Implements`, `ImplementsF`); the executed cases
  discharge it concretely.
- The examples run over the kernel's `Nat` quantities (ADR-0011 records
  production's float deviation).
- `zip` is derived through `fold`, `take 1`, `drop 1` and `reverse`; a direct
  primitive would be an optimization, not a semantic change.
- Sums are encoded, not added; a kernel `sum` with an eliminator term former is
  the natural next step if `match` exhaustiveness is required.
