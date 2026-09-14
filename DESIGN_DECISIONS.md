# DESIGN_DECISIONS — model choices and rejected alternatives

Numbered, append-only.  Each entry: the choice, the alternative(s) rejected,
and the formal reason.

## Phase 0

**D-01. Obligations are atomic labels; evidence is abstract.**
Rejected: modelling semantic properties (monotonicity etc.) in Lean.
Reason: the experiment is about refinement structure; `Refines_iff_semantic`
shows the syntactic order is complete for abstract evidence, so nothing is
lost at this level.

**D-02. `Refines` freezes the type and grows obligations; not logical implication.**
Rejected: `Refines := ∀ realizations, Satisfies new → Satisfies old`.
Reason: equivalent (`Refines_iff_semantic`) and the syntactic form is decidable.

**D-03. `strengthen` on a realized hole carries a re-verification premise.**
Rejected: `strengthen` with only `Refines S S'`.
Reason: Theorem 4 fails (`naive_breaks_wellformedness`).

**D-04. `Spec.obligations` is a `List`, not a `Finset`.**
Rejected: Mathlib `Finset`.
Reason: avoids the dependency; cost is that `SpecEquiv` is not antisymmetric.  Cosmetic.

## Phase 1

**D-05. References are by `HoleId` inside `Expr` (`holeRef`), not a separate `DesignExpr`.**
Rejected: a two-level syntax.
Reason: nothing distinguishes a realization from any other term except that
it may mention holes; one syntax with `refs` is smaller.

**D-06. The `holeRef` typing rule reads `Δ.tyView` only.**
Rejected: a rule that also inspects the referenced hole's realization or obligations.
Reason: this is the formal content of "signature-first".  It makes
`local_refinement_preserves_global_typing` immediate and is *necessary*
(probe 4).  Reported as a definitional theorem.

**D-07. Realization is write-once; "detach" is not a refinement step.**
Rejected: allowing `some e ↝ none` in `HoleLeq`.
Reason: detaching preserves typing of clients (tyView unchanged) but is not
monotone for evidence — any client evidence that consulted `B`'s realization
is invalidated.  Detaching is therefore an *edit* that re-opens validation
of all transitive dependents, not a refinement.  The paper's "definitions may
coexist, one active" is carried as a pending surface question
(`MINIMALITY.md`).

**D-08. The structural order (`HoleLeq`, `EnvRefines`) is separated from the invariant (`GlobalWF`).**
Rejected: Phase 0's `HoleLeq` which bundled well-formedness of the target.
Reason: the typing theorem holds under the structural order alone; bundling
would have hidden that its hypotheses are weaker than the commitment
theorem's.  The Phase-0 characterization survives as
`HoleRefinesStar_iff : … ↔ HoleLeq h₁ h₂ ∧ WellFormedHole ev Δ Γ h₂`.

**D-09. `Evidence` takes the environment as an argument.**
Rejected: Phase 0's `Expr → PropertyId → Prop`.
Reason: compositional discharge ("A monotone because B committed monotone",
`compEv`) is otherwise inexpressible, and it is exactly the case that makes
probe 5 fail.  Constant evidence is a special case
(`Evidence.Monotone.of_const`).

**D-10. `Evidence.Monotone` is a kernel-imposed constraint on the validation layer.**
Rejected: leaving discharge mechanisms unconstrained.
Reason: `local_refinement_preserves_global_wf` is false otherwise (probe 6,
`badEv_not_mono`).  Positivity in the environment is the minimal condition
found; whether some weaker condition suffices was not investigated because
the counterexample is already a one-hole, one-step case.

**D-11. Semantics at Phase 1 is unfolding to a hole-free term.**
Rejected: a denotational semantics with fixpoints.
Reason: the paper's pure fragment has no general recursion (§4.5); unfolding
is the smallest semantics that distinguishes "well-typed partial" from
"executable".  Consequence: every reference cycle is meaningless
(`Unfolds.not_of_cyclic`).  Revisit when delay exists.

**D-12. Acyclicity is witnessed by a rank function.**
Rejected: `WellFounded` on the dependency relation; a finite-graph DFS.
Reason: rank is the simplest witness that makes `Unfolds.exists_of_acyclic`
a direct strong induction; it is sufficient and for finite graphs equivalent.
`Acyclic.not_cyclic` connects it to the cycle predicate.

**D-13. Phase 0's `Artifact` (bare list of ids) removed.**
Reason: subsumed by `holeRef`; keeping it would violate minimality.

**D-14. Display names are not in the kernel.**
Reason: the paper itself says renaming is a refactoring over the stable id
(§3.2).  `HoleId` is the only identity the kernel needs.
