# Report: persistent typed design holes — a Lean 4 feasibility experiment

Everything below refers to definitions and theorems in `PersistentHole/`.
The project builds with `lake build`, contains no `sorry`, and the theorems
depend on no axiom beyond `propext`.

## 1. What is the minimal formal object corresponding to a persistent typed design hole?

```lean
structure Spec       where expectedType : Ty;  obligations : List PropertyId
structure DesignHole where id : HoleId;  spec : Spec;  realization : Option Expr
```

together with the lifecycle preorder, which `HoleRefinesStar_iff_HoleLeq`
proves is *exactly* the reflexive–transitive closure of the three step rules
(`refine`, `realize`, `strengthen`):

```lean
HoleLeq ev Γ h₁ h₂ :=
  h₁.id = h₂.id                                           -- identity frozen
  ∧ Refines h₁.spec h₂.spec                               -- type frozen, obligations ⊆
  ∧ (∀ e, h₁.realization = some e → h₂.realization = some e)  -- write-once realization
  ∧ (∀ e, h₂.realization = some e → Satisfies ev Γ e h₂.spec) -- realization meets current spec
```

So the minimal object is: **a fixed name, paired with a point in the
join-semilattice `Ty × Finset PropertyId` (ordered by `=` on the type and `⊆`
on obligations), paired with a write-once cell, subject to one invariant.**
Nothing in `DesignHole` mentions a syntactic position; a hole is a declaration,
not a location.

## 2. Which invariants are required for progressive refinement?

Five, and each is discharged by a counterexample in `Examples.lean` showing
what breaks without it:

| Invariant | Encoded where | Breaks without it |
|---|---|---|
| `expectedType` is frozen | `Refines` | Theorem 5 (`loose_breaks_theorem5`); clients typed against the old type become ill-typed (`client`) |
| obligations only grow | `Refines` | Theorem 5 (`forgetful_breaks_theorem5`): a commitment is silently forgotten |
| identity is preserved by every step | every constructor of `HoleRefines` reuses `id` | References go stale (`consumer.RefersTo h₂ ∧ ¬ consumer.RefersTo h₃'`); the environment slot readers look at is never updated (`fresh_id_breaks_env_refinement`) |
| a realization is write-once and immutable | shape of `HoleRefines` | (not tested; needed for `HoleLeq.toStar` and for `final_realization_satisfies_all` to be about *the* realization) |
| **strengthening a realized hole re-verifies the term** | premise `hs` of `HoleRefines.strengthen` | Theorem 4 (`naive_breaks_wellformedness`) |

The last row is the one the experiment was run to find. See §4.

## 3. Which of the intended theorems were provable?

All of them, for the final `HoleRefines`:

| Theorem | Lean name | Notes |
|---|---|---|
| 1 identity preservation | `HoleRefines.id_eq` | `cases h <;> rfl` — definitional, as intended |
| 2 type commitment preservation | `HoleRefines.expectedType_eq` | |
| 3 obligation monotonicity | `HoleRefines.obligations_subset` | |
| 4 refinement preserves well-formedness | `HoleRefines.preserves_wellFormed` | see §4 |
| 5 realization satisfies earlier specs | `Satisfies.of_refines` (2-step), `Satisfies.of_refines_star` (n-step), `HoleRefinesStar.final_realization_satisfies_all` (hole level) | |
| 6 multi-step refinement | `HoleRefinesStar`, `HoleRefinesStar.of_two`, lifted versions of 1–4 | `HoleRefines` itself is *not* transitive (`refine` then `realize` has no single-step form) so the closure is used |
| reference stability | `Artifact.refersTo_of_refines`, `EnvRefines_update`, `resolve_update_refines` | |

Two results not in the brief turned out to be the most informative:

* **`Refines_iff_semantic`**: with evidence abstract, the syntactic relation
  "same type ∧ obligations ⊆" is *exactly* "every realization of the new spec
  realizes the old spec, for every evidence relation". So choosing a small
  decidable refinement relation over "arbitrary logical implication" costs
  nothing at this level of abstraction.
* **`HoleRefinesStar_iff_HoleLeq`**: the operational three-rule lifecycle
  collapses to the closed-form preorder in §1.

`SpecEquiv` is a genuine equivalence but not antisymmetric, because obligations
are a `List` (`[total, total]` vs `[total]`). Cosmetic; a `Finset` would fix it
at the cost of a Mathlib dependency.

## 4. Which intended theorem failed, and why?

**Theorem 4 fails for the natural first definition of the lifecycle**, in
which a realized hole may have its spec strengthened by merely `Refines S S'`
(`NaiveHoleRefines` in `Examples.lean`). Concretely: `constZero = λx:nat. 0`
realizes `S₁ = ⟨nat→nat, [total]⟩`; strengthen to `S₂ = S₁ + monotone`; the
hole is now ill-formed because there is no evidence that `constZero` is
monotone (`naive_breaks_wellformedness`).

The missing assumption is isolated by `naive_strengthen_wf_iff`: a naive
strengthen step preserves well-formedness iff the existing term satisfies the
*strengthened* spec. So the corrected rule carries that as a premise:

```lean
| strengthen (h : Refines S S') (hs : Satisfies ev Γ e S') :
    HoleRefines ev Γ ⟨id, S, some e⟩ ⟨id, S', some e⟩
```

Semantic justification: "adding a commitment" to a hole that already has a
body is not a spec-only operation — it is a claim about the body, and must be
discharged when made, not deferred.

A more uncomfortable observation: in the proof of `preserves_wellFormed`, the
hypothesis `WellFormedHole ev Γ h₁` is used in *no* case. Well-formedness of
the target follows from the step's own premises. This means Theorem 4 is not
a theorem *about* the relation so much as a check that the invariant has been
correctly pushed into the definition. That is fine for a calculus — but it
also means the theorem has no independent content.

## 5. Does persistent identity add anything beyond `let f : A → B := ?` or an abstract declaration?

Formally, in this model: **very little**, and one should be precise about
what little.

* Theorems 2–6 never use `id` except to pass it along. Delete the `id` field
  and every single-hole theorem survives unchanged. Persistent identity is
  therefore not what makes refinement work; it is orthogonal to refinement.
* `id` does real work exactly once: in `EnvRefines_update`, where
  `HoleRefines.id_eq` is what guarantees that writing the new state back
  lands on the slot existing references read from. But this is precisely the
  role a *name* plays in any declaration-based system. `let f : A → B := ?`
  also has a stable name `f` that clients refer to, and clients do not need
  editing when `?` is filled in.
* Metavariable systems (Lean `?m`, Agda `?0`, Coq evars) already have
  persistent, referable identities and write-once assignment. The
  `write-once realization` half of `HoleLeq` is exactly a metavariable
  assignment.

What `DesignHole` has that `let f : A → B := ?` does not is the **monotone
obligation set that may grow after declaration and after realization**. But
that is a property of the *spec* (it is a semilattice element rather than a
fixed type), not of *identity*. The honest summary of the model is:

> a named, write-once cell whose "type" is `Ty × (growing finite set of
> obligation labels)`, plus the rule that growth after assignment re-checks
> the assignment.

That is an abstract declaration with a mutable-but-monotone set of proof
obligations — structurally similar to a Coq `Program`/`Obligation` or an
Agda postulate whose set of pending goals can only shrink (here: only grow,
but the same monotonicity).

## 6. Which existing notion is the abstraction closest to?

A combination, with weights:

* **Contextual metavariables** (strongest match): persistent id, referable
  before assignment, write-once assignment, typed. Missing from mvars: the
  post-declaration growth of obligations.
* **Refinement systems** (second): `Refines` is a spec preorder and Theorem 5
  is the standard "a refined spec has fewer models" fact; `Refines_iff_semantic`
  says the syntactic order is complete for it. But there is no *type*
  refinement here — the type is frozen — so it is refinement of an
  obligation set only.
* **Abstract declarations**: what `DesignHole` reduces to once `id` is seen as
  a name.
* **Typed holes** (Hazel-style): weak match. Those holes are syntactic
  positions with live semantics (hole environments, evaluation around holes);
  `DesignHole` has no position and no evaluation.
* **Program sketching**: no match; there is no search, and `Evidence` is not a
  solver.

## 7. Based only on the formal model, what is the genuine PL contribution?

Being critical: **as it stands, the model does not contain a new PL result.**
Every theorem is either definitional (1–3, 6), a check that an invariant was
placed correctly (4), or a two-line consequence of `⊆` (5). The completeness
result `Refines_iff_semantic` is neat but is also a symptom: because evidence
is fully abstract, obligations are opaque labels, and any set-inclusion order
on labels is trivially complete.

What the exercise *does* establish:

1. The abstraction is **coherent**: there is a clean closed-form preorder
   (`HoleLeq`) and the operational lifecycle is exactly its closure.
2. The abstraction has **one non-obvious invariant** — re-verification on
   post-realization strengthening — that a naive design misses and that the
   counterexample makes concrete.
3. The three weakenings the brief was worried about (retyping, forgetting,
   re-identifying) each break a specific theorem, so the invariants are
   necessary, not decorative.

What it does *not* establish is that "persistent design hole" is more than
"named declaration + monotone obligation set + write-once body". To find out
whether there is more, the next experiment should add the one thing this
model deliberately omits, which is also the only place identity can do
non-trivial work:

* **Let realizations contain holes** (`Expr.hole : HoleId → Expr`), typed
  against the hole environment. Then a term that realizes hole `A` may refer
  to hole `B`; realizing `B` later must preserve the typing and the
  obligations of `A` *without editing `A`'s term*. That theorem is the actual
  content of "persistent, referable identity"; in the present model it is
  trivial because artifacts are inert lists of ids. It also forces the
  questions that would distinguish this from metavariables — cyclic
  references, obligations on `A` whose evidence depends on `B`'s realization,
  and whether strengthening `B` can invalidate `A`.
* Secondarily, allow the expected type to be *narrowed* (a subtyping or
  refinement-type order on `Ty`). Theorem 5 then stops being `⊆` and acquires
  variance conditions on `arr`, which is where a "refinement system" reading
  would start to have teeth.

Until one of those is done, the safe claim is that the formal core of the
idea is a well-behaved but standard structure, and the novelty (if any) lies
in the *combination* with position-independence and cross-hole reference —
neither of which this minimal model yet exercises.
