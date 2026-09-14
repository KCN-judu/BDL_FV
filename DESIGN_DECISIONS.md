# DESIGN_DECISIONS — model choices and rejected alternatives

Numbered, append-only.  Each entry: the choice, the alternative(s) rejected,
and the formal reason.

## Phase 0

**D-01. Commitments are atomic labels; evidence is abstract.**
Rejected: modelling semantic properties (monotonicity etc.) in Lean.
Reason: the experiment is about refinement structure; `InterfaceRefines_iff_semantic`
shows the syntactic order is complete for abstract evidence, so nothing is
lost at this level.

**D-02. `InterfaceRefines` freezes the type and grows commitments; not logical implication.**
Rejected: `InterfaceRefines := ∀ realizations, Satisfies new → Satisfies old`.
Reason: equivalent (`InterfaceRefines_iff_semantic`) and the syntactic form is decidable.

**D-03. `strengthen` on a realized declaration carries a re-verification premise.**
Rejected: `strengthen` with only `InterfaceRefines S S'`.
Reason: Theorem 4 fails (`naive_breaks_wellformedness`).

**D-04. `DeclInterface.commitments` is a `List`, not a `Finset`.**
Rejected: Mathlib `Finset`.
Reason: avoids the dependency; cost is that `InterfaceEquiv` is not antisymmetric.  Cosmetic.

## Phase 1

**D-05. References are by `DeclId` inside `Expr` (`declRef`), not a separate `DesignExpr`.**
Rejected: a two-level syntax.
Reason: nothing distinguishes a realization from any other term except that
it may mention declarations; one syntax with `refs` is smaller.

**D-06. The `declRef` typing rule reads `Δ.tyView` only.**
Rejected: a rule that also inspects the referenced declaration's realization or commitments.
Reason: this is the formal content of "signature-first".  It makes
`local_refinement_preserves_global_typing` immediate and is *necessary*
(probe 4).  Reported as a definitional theorem.

**D-07. Realization is write-once; "detach" is not a refinement step.**
Rejected: allowing `some e ↝ none` in `DeclLeq`.
Reason: detaching preserves typing of clients (tyView unchanged) but is not
monotone for evidence — any client evidence that consulted `B`'s realization
is invalidated.  Detaching is therefore an *edit* that re-opens validation
of all transitive dependents, not a refinement.  The paper's "definitions may
coexist, one active" is carried as a pending surface question
(`MINIMALITY.md`).

**D-08. The structural order (`DeclLeq`, `EnvRefines`) is separated from the invariant (`GlobalWF`).**
Rejected: Phase 0's `DeclLeq` which bundled well-formedness of the target.
Reason: the typing theorem holds under the structural order alone; bundling
would have hidden that its hypotheses are weaker than the commitment
theorem's.  The Phase-0 characterization survives as
`DeclRefinesStar_iff : … ↔ DeclLeq h₁ h₂ ∧ WellFormedDecl ev Δ Γ h₂`.

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
the counterexample is already a one-declaration, one-step case.

**D-11. Semantics at Phase 1 is unfolding to a reference-free term.**
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
Reason: subsumed by `declRef`; keeping it would violate minimality.

**D-14. Display names are not in the kernel.**
Reason: the paper itself says renaming is a refactoring over the stable id
(§3.2).  `DeclId` is the only identity the kernel needs.

## Post-Phase-1 migration

**D-15. Kernel ontology migrated from holes to declarations.**
Rejected: treating an unresolved declaration as a syntactic hole
(`HoleId`, `DesignHole`, `holeRef`, `Spec.obligations`, …).
Reason: Phase 1 showed (a) identity is used only as an environment key —
ordinary declaration identity, not a new abstraction (`EnvRefines_update`,
REPORT §1.5); (b) clients reference the *interface* (`tyView` for typing,
commitments for validation), never a syntactic position — nothing in the
kernel object records where a reference occurs; (c) unresolvedness is
exactly `realization = none`.  The hole vocabulary therefore described a
concept the model never contained.
Consequence: kernel names are `DeclId`, `DesignDecl`, `DeclEnv`, `declRef`,
`DeclInterface` (with `commitments`), `DeclLeq`/`DeclRefines`,
`WellFormedDecl`.  "Hole" remains available only as a surface/HCI metaphor
for a declaration whose realization is absent.  No aliases retained.
Verification: mechanical rename compiled with zero proof edits; declaration
inventory identical modulo the rename map (REPORT §M).

**D-16. Monotone refinement is distinct from arbitrary editing.**
(Generalizes D-07, which covered only detaching.)
Refinement steps — the only operations covered by the preservation theorems —
are: realize an unresolved declaration; add public commitments; strengthen
an interface while preserving the expected type; strengthen a realized
declaration with re-verification.
Not refinement: changing the expected type (probe 4), removing a commitment
(probe 5), detaching a realization (D-07), replacing a realization, changing
identity (probe 3).  These are ordinary *edits*: they may invalidate
transitive dependents and require rechecking/revalidation.
Rejected: formalizing a general edit relation now.
Reason: nothing in Phases 0–1 needs it; the counterexamples already show
what each edit breaks.  Revisit when a phase needs invalidation tracking.

**D-17. Commitments and validation obligations share `PropertyId` for now.**
The field is named `commitments` because, from a dependent's perspective,
these are public promises; the validation layer turns each into a proof
obligation to discharge.  Rejected: a separate obligation datatype.
Reason: no phase yet distinguishes them operationally; introducing the
split before Phase 11 would be speculative.

**D-18. `Evidence.Monotone` is a stability condition, not a definition of validity.**
Documentation correction.  Monotonicity is required of evidence intended to
*survive* monotone environment refinement.  Environment-sensitive evidence
that is rechecked on every change is a legitimate future category and is
not excluded by the kernel; it is simply not covered by
`local_refinement_preserves_global_wf`.

## Phase 2

**D-19. Semantic identity lives in the type: `Ty.sem : SemanticId → Ty`.**
Rejected: (B) a `semanticRole` field in `DeclInterface` with a separate
checker; (C) concepts as `DesignDecl`s with identity = `DeclId`.
Reason: B-weak is evaded by η-expansion (`bweak_evaded_by_eta`); B-strong is
`HasType` over `Ty`-with-`sem` run a second time; a role change is an edit
that flips unchanged clients (`role_change_flips_unchanged_clients`), so the
field would have to be frozen exactly like the type.  C admits category
errors (`conceptC_usable_as_value`, `conceptC_realizable_by_a_number`).
Consequence: `Ty` gains one constructor; `DeclInterface` and `tyView` are
unchanged; all Phase 0/1 theorems hold verbatim.

**D-20. `SemanticId` is independent of `DeclId` and of display names.**
Rejected: deriving concept identity from a declaration id (Model C) or from
the surface name (Counterexample C, `rename_under_name_identity_breaks_client`).
Reason: a concept is a type, a declaration is a value; names are renameable.
Consequence: three distinct things — internal identity (`SemanticId`),
display name (surface `Concept.name`), representation (`ρ : SemanticId → Ty`,
used only by erasure in Phase 2).

**D-21. No introduction/elimination forms for semantic types in Phase 2.**
Rejected: adding `mk`/`rep` now.
Reason: distinctness needs only the nominal constructor.  Without `mk`/`rep`,
`no_semantic_value_without_declaration` shows semantic values flow only
through declarations — the intended discipline.  `mk`/`rep` are a
representation binding, needed to realize mappings by formulas, and belong
with Phase 3 where the representation is `Q[d]`.

**D-22. Explicit cross-concept mappings are ordinary declarations.**
Rejected: a kernel conversion relation, coercion, or subtyping.
Reason: `tiltToMotor : sem tilt → sem motor` as a declaration is already
signature-first, may remain unresolved, and makes the conversion visible in
every term that uses it (`explicit_mapping_allows_cross_semantic_conversion`).

**D-23. Semantic identity change is an edit.**
In every model tried.  Formally in A it is a type change
(`semantic_identity_change_is_not_refinement`); the Phase-1 edit/refinement
split (D-16) covers it without extension.

**D-24. Canonical closed inhabitants replaced by unresolved declarations.**
`Ty.canon` removed; `InterfaceRefines_iff_semantic` now inhabits a type by
`declRef` in a one-declaration environment (`DeclEnv.single_hasType`).
Reason: opaque semantic types have no closed inhabitants, and
signature-first typing never needed them.
