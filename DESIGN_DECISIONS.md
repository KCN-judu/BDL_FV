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
Rejected (with claim strength): (B-weak) a `semanticRole` field in
`DeclInterface` with a direct-wire checker — *tested design failure*:
evaded by η-expansion (`bweak_evaded_by_eta`), and a role change flips
verdicts on unchanged clients (`role_change_flips_unchanged_clients`), so
the field would have to be frozen exactly like the type.  (B-strong) a
compositional role judgment — *engineering preference*: any sound checker
must be compositional over terms, i.e. of type-system strength; the tested
role-per-subterm formulation duplicates nominal typing with no observed
benefit; the broader family of compositional semantic analyses is not
universally ruled out.  (C) concepts as *ordinary* `DesignDecl`s with
identity = `DeclId` — *tested design failure*: category errors
(`conceptC_usable_as_value`, `conceptC_realizable_by_a_number`).  A
stratified concept sort is not rejected but reintroduces an independent
`SemanticId`.
Consequence: `Ty` gains one constructor; `DeclInterface` and `tyView` are
unchanged; all Phase 0/1 theorems hold verbatim.  This is the smallest
mechanism among the tested designs, not a proof that nominal typing is the
only possible one.

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

**D-22. Explicit semantic mappings are ordinary declarations.**
Rejected: a kernel conversion relation, coercion, cast, or subtyping.
Reason: `tiltToMotor : sem tilt → sem motor` is a *design relationship*
between concepts, not a representation conversion.  As a declaration it is
already signature-first, may remain unresolved, and makes the mapping
visible in every term that uses it (`explicit_semantic_mapping_accepted`).
Terminology: "explicit semantic mapping"; the words conversion / coercion /
cast are reserved for representation-level mechanisms, none of which exist
in the Phase-2 kernel.

**D-23. Semantic identity change is an edit.**
In every model tried.  Formally in A it is a type change
(`semantic_identity_change_is_not_refinement`); the Phase-1 edit/refinement
split (D-16) covers it without extension.

**D-25. Future constraint for Phase 3: representation binding must not
defeat semantic identity.**
Unrestricted `rep : sem s → R` and `mk : R → sem s` would let
`mkMotor (repTilt x)` reconstruct an implicit `Tilt → MotorAngle` path with
no declared semantic mapping, falsifying `no_semantic_value_without_declaration`
and reducing `Ty.sem` to ceremony.  Phase 3 must decide which representation
observations are safe, which semantic constructions are safe, and when
crossing `SemanticId`s must require a declared mapping; it must test
(A) unrestricted symmetric `mk`/`rep`, (B) restricted/capability-controlled
construction, (C) binding available only inside realization/elaboration,
(D) an explicit witness `RepresentationBinding s r`, (E) semantic mappings as
the only user-visible cross-identity path — starting with an attempt to
construct the bypass counterexample.  Not solved here.

**D-24. Canonical closed inhabitants replaced by unresolved declarations.**
`Ty.canon` removed; `InterfaceRefines_iff_semantic` now inhabits a type by
`declRef` in a one-declaration environment (`DeclEnv.single_hasType`).
Reason: opaque semantic types have no closed inhabitants, and
signature-first typing never needed them.

## Phase 3

**D-26. Unrestricted symmetric `mk`/`rep` rejected.**
Rejected: global `rep_s : sem s → R` and `mk_s : R → sem s` (Model A).
Reason: *formally rejected by counterexample* —
`unrestricted_representation_binding_bypasses_semantic_identity` gives a
closed `Tilt → MotorAngle` in the empty environment;
`hidden_crossing_inside_unrelated_body` hides it inside an unrelated
signature; Phase-2 provenance becomes false.

**D-27. Representation types are sem-free (`ConceptEnv.WF`).**
Rejected: allowing `Θ s = some (sem s')`.
Reason: `rep` would then be a hidden mapping under every policy
(`binding_to_semantic_type_is_hidden_mapping`).  A constraint the brief did
not anticipate; discovered while building Model A.

**D-28. Observation is unrestricted; construction is licensed by the realized declaration's signature.**
Rejected: (B) observation only — safe (`provenance`) but *formally unable*
to realize any mapping by a formula (`modelB_cannot_realize_mapping`);
(D-alone) a witness with no policy — it is a component, not a model.
Chosen: `rep` everywhere; `mk s` iff the grant permits `s`; client code at
`Grant.none`; a realization at `Grant.of` its own signature.
Reason: `constructs_granted` (a `sem s` value is built only inside a
declaration announcing `sem s`), `grant_provenance`,
`hidden_crossing_rejected_under_grant`, and the positive
`explicit_semantic_mapping_can_use_representation_formula`.  The signature is
the smallest authority that makes every crossing visible at the design level
and needs no new annotation.  Claim strength: smallest among tested designs.

**D-29. Representation binding is a separate, write-once concept environment `Θ`.**
Rejected: storing the binding in `DeclInterface`; indexing `Ty.sem` by the
representation (`Sem[n,d]`).
Reason: a concept is a type, not a declaration (Phase 2, Model C); the
binding is deferred like a realization (`unbound_concept_still_wires`),
monotone to bind (`HasType.mono_concept`, `GlobalWF.of_conceptRefines`), and
an edit to change (`representation_change_is_edit_not_refinement`, both
forms).  Typing reads `Θ` only through `Θ s = some R`.
**Consequence (major):** typing now consults two environments — `Δ.tyView`
and `Θ` — plus a grant.  `tyView` itself is unchanged.  The brief's
`HasType` / `Realizes` split is realized as one judgment family indexed by
the grant.

**D-30. Unfolding preserves typing under `Grant.all`, not under the client grant.**
Rejected: pretending the flattened executable is semantically isolated.
Reason: each inlined `mk` was authorized at its own declaration
(`constructs_granted` per body); the executable is where isolation has been
discharged.  Recorded honestly in `Unfolds.preserves_typing`.

**D-31. Dimensions in `Ty` as `q d`; algebra in `Prim.ty`; no dimension rule.**
Rejected: dimensions as metadata or validation obligations (not formalized;
engineering preference — `mul`/`div` *produce* dimensions, so any checker
recomputes inference); a dimension-specific typing rule (unnecessary —
registered operators carry their types).
Reason: `dimension_mismatch_rejected`; the numeric baseline is erased
dimensional typing (`HasType.eraseDim`,
`counterexampleB_baseline_accepts_length_plus_time`).  `Dim` is an exponent
vector over three bases, chosen to keep proofs decidable.

**D-32. Units are surface: elaborated to scaled dimensioned literals.**
Rejected: units in `Ty`.
Reason: `unit_scaling_preserves_dimension`, `unit_change_is_value_not_type`;
mixed-unit addition works after elaboration.  Affine units not modelled.

**D-33. Semantic identity is not indexed by dimension.**
Rejected: `SemanticId d`, `Ty.sem s d`.
Reason: `same_dimension_does_not_imply_same_semantic_identity` — Tilt and
MotorAngle share `q Angle` and stay distinct with the direct wire rejected;
the association lives in `Θ` (D-29).  This is what Phase 2 + Phase 3 yield
*instead of* the paper's `Sem[name, dimension]`.

## Phase 4

**D-34. One temporal primitive: `delay init e`.**
Rejected as primitives: `previous`, `hold`, `count`, `since`, `once`,
`every`, `rise`, `Event`, `Signal`.  Each was reduced to `delay` plus
`Prim` and executed (`*_trace`).  Reason: no candidate adds observable
behaviour, changes causality beyond one delayed self-edge, or needs its own
storage.  Claim strength: expressibility by execution; there is no kernel
definition for them to be equivalent to.

**D-35. `delay` is data-typed and top-level (empty context).**
Rejected: delay at function types; delay under lambdas.
Reason: forced by the totality proof — closures cannot be transported across
ticks (`Red_data` needs `τ.Data`), and a delay under a lambda would evaluate
its operand at the previous tick under a current-tick environment.
Consequence: temporal state belongs to declarations; mappings are pointwise;
reusable stateful components need instantiation (Phase 8).  Also scopes
`HasType.weaken_append` / `Unfolds.preserves_typing` to the delay-free
fragment — the domain of validity of the Phase-1 inlining results.

**D-36. `Signal` is not a type; `Event` is `opt`.**
Rejected: `Ty.signal`, `Ty.event`.
Reason: under the tick semantics every declaration is a stream, so a signal
type distinguishes nothing; an event input is an `opt` stream by
construction of `Input`, and `event_encoding_equivalent` /
`event_encoding_loses_multiplicity` locate multiplicity in the cross-domain
observation model (Phase 5).  Claim strength: engineering preference for
`Signal`; equivalence by proof under the single-domain model for `Event`.

**D-37. Causality replaces blanket acyclicity: `Causal` on `InstDependsOn`.**
Rejected: deleting `Unfolds.not_of_cyclic`; keeping structural acyclicity
as the execution criterion.
Reason: `Unfolds` stays correct wherever it exists (`unfolds_preserves_eval`
on wiring designs) and is the delay-free special case
(`Causal_iff_acyclic_of_delayFree`); execution exists exactly on causal
designs (`reactive_total`, `Ev.not_of_strictCyclic`).  Known gap:
lambda-guarded cycles are rejected conservatively.

**D-38. Explicit initial value on every delay.**
Rejected: `previous : τ → opt τ` as the primitive (derivable); no init
(undefined or nondeterministic first tick, `first_tick_*`); init as a
validation obligation (nothing to validate without a unique first step).

**D-39. State has no identity; state is structural.**
Rejected: `StateId`, reuse of `DeclId`/`SemanticId` for cells.
Reason: a delay node is referred to by nobody; consumers reference the
declaration.  "Multiple writers" does not arise until actions (Phase 6).

**D-40. Representation types are data (`ConceptEnv.WF` strengthened).**
Reason: a semantic value may be delayed; a function-typed representation
would carry a closure across ticks.

**D-41. Temporal changes are realization edits.**
Adding/removing a delay or changing an initial value is not `DeclLeq`
(`temporal_change_is_edit`); D-16 applies unchanged.

**D-42. The reactive semantics is a relation, not yet a machine.**
Rejected for now: an explicit `MachineState`/`Step` with stored cells.
Reason: the tick-indexed relation is the specification and suffices for
determinism, totality, causality, provenance, and the Event comparison; the
stored-state machine is an implementation to be proven equivalent in Phase 8.
