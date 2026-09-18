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

## Phase 5

**D-43. Time is one global tick with a schedule; no rates, no timestamps in the kernel.**
Rejected: domain-local counters with a scheduler relation; physical timestamps.
Reason: the global tick with `Sched` is the smallest model that distinguishes
the behaviours in question (Counterexamples A, B, F); a period induces a
schedule (`Sched.periodic`) and everything numeric is validation (D-47).

**D-44. Nominal `ClockId`, stored per declaration in `ClockEnv Κ`; `none` = domain-agnostic pure mapping.**
Rejected: inferred domains (would make an unresolved declaration's domain
depend on future realizations — the Phase-1 signature-first property);
domains by rate (`equal_rate_not_same_domain`).
Reason: clients' validity depends on the producer's domain
(`clock_change_invalidates_clients`), so the domain is interface data and must
be declarable before realization.

**D-45. One transport primitive `sync src init e`, reading strictly before.**
Rejected: same-tick-visible transport (makes scheduler order semantic,
`scheduling_order_observable`); separate `hold`/`latest`/`sample` primitives
(all are `sync`); a buffering primitive (derivable: `buffer_from_log_and_cursor`).
Reason: `delay_is_sync_own` — the Phase-4 state primitive is this primitive at
the own domain, so the kernel has *one* temporal read; `MEv.det`,
`multi_domain_total`.

**D-46. The clock is interface data held in a projection, not a record field.**
The public interface is semantically `expectedType × commitments × clock`
(Counterexample E; frozen under refinement; edit to change).  It is stored in
`Κ`, as the representation is stored in `Θ`, rather than in `DeclInterface`.
Rejected: `Ty`-indexed clocks (`clocked_type_forces_polymorphism`).  Folding
`Κ` into the record is churn, not semantics; deferred.

**D-47. Rates, drift, jitter, latency, buffer capacity, value age are validation.**
None affects `Clocked`, `MEv.det`, or `multi_domain_total`; a rate change
alters the induced schedule (observed values) but no client's well-formedness.

**D-48. Event transport = window read; buffering derived, `Event` still not a primitive.**
`opt_loses_multiplicity_under_sync` rejects `sync` as an *event* transport;
`buffer_from_log_and_cursor` derives the exact window from `sync` of a log and
`delay` of a cursor; `policies_lose_information` fixes what each policy keeps.
Rejected: `Event τ` as a kernel type; a buffer primitive.
Pending: `Ty.list` to write the buffer in the object language; capacity is
validation.

**D-49. The logical relation is generic in the application relation.**
`Red Θ A` with `A : App`, so Phase 4 (`Apply Δ I t`) and Phase 5
(`MApply S Δ I c t`) share `Red_prim`, `Red_data`, `RedEnv`.  Refactor, no
semantic change.

## Phase 6

**D-50. Physical sinks have nominal identity (`OutputId`), separate from `SemanticId` and `DeclId`.**
Rejected: type-keyed sinks (`type_keyed_binding_collides`); `SemanticId` as
sink (one concept, many devices); `DeclId` as sink (Counterexample A becomes
unstatable); deployment-only binding (completeness is a design-time acceptance
condition).

**D-51. A drive edge is a per-declaration write-once projection `β`, checked by type and clock equality.**
Rejected: an output expression primitive; output binding in `Ty` or in
`HasType`; a binding that coerces or synchronizes.
Reason: `output_binding_preserves_semantic_identity_and_dimension`,
`output_binding_respects_clock_domain`; keying `β` by declaration (not by
sink) keeps single-driver a real global check (D-52).

**D-52. Single-driver is a global invariant; completeness is the executable condition.**
`SingleDriver β` (at most one) for partial designs, `CompleteOutputs β req`
(exactly one required) for executable ones.  Local typing is insufficient
(`two_direct_drivers_locally_fine`).  Joins commitments, causality, clock
consistency as global structure beyond STLC typing.

**D-53. No runtime arbitration, no implicit priority, no merge policy.**
Rejected: first/last/numeric-priority policies; effect-handler arbitration.
Reason: hidden policies are observable (`hidden_arbitration_observable`);
priority, max, blend, clamp are ordinary declarations of the target type
(`explicit_priority_single_driver`).  Claim strength: unnecessary in the
tested architecture; not a universal impossibility.

**D-54. Effect rows and action values rejected for this kernel.**
Direct effect rows are `β` (`single_driver_iff_direct_rows_disjoint`);
propagated rows produce false positives
(`propagated_effect_rows_false_positive`); action values relocate the
conflict into a collector that must be a policy
(`action_values_relocate_conflict`).  Claim strength: the tested
formulations add no rejection or expressive capability.

**D-55. First binding is a refinement; rebinding is an edit; a second driver is invalid.**
`first_output_binding_is_monotone` (side condition: the sink is undriven),
`second_binding_invalid`, `rebinding_invalidates_design`.  Same write-once
philosophy as realizations (D-07) with one global side condition.

**D-56. Sinks are terminal.**
Physical feedback is another input declaration through ordinary clocks and
delays; no instantaneous world edge.

## Phase 7

**D-57. Hardware feasibility is a validation layer over `Design × Target`, not typing.**
Rejected: `Ty.pwm`/`Ty.pin`/…; feasibility as a semantic commitment.
Reason: `seven_pwm_design_semantically_valid ∧ seven_pwm_unsat_on_nano`; the
same requirements are SAT on a larger board; the solver's type never
mentions `Δ`.

**D-58. Resources carry capabilities and per-capability units; sharing is a per-capability policy.**
Rejected: `allDifferent` (Counterexample E); capability counts (C); pin
capability without units (`timers_matter`); protocol-specific solver logic
(board tables carry pin sets and units; grouping is generic `UnitRel.same`).

**D-59. Requirements are independent variables with nominal `RequirementId`, optional fixed resource, optional unit relation.**
Rejected: reusing `DeclId`/`OutputId` (one sink ⇒ several requirements);
composite peripheral requirements (independent + `same` unit suffices);
pins as `OutputId` (swapping boards must not change the design).

**D-60. Validity is unary support plus pairwise compatibility; the solver is exhaustive DFS, proved sound and complete.**
Rejected for now: SMT integration; minimal unsat cores.
Reason: all tested constraints are unary/binary, so pruning on prefixes is
complete (`solve_complete`); `decide` runs the instances in seconds;
`diagnose` gives a first dead end.  Claim strength: for the tested
pin/peripheral scope.

**D-61. Hardware extension is monotone; requirement extension, strengthening, fixing, and resource removal are revalidation triggers.**
`hardware_extension_preserves_satisfiability`; G, H, F, A.

**D-62. Deployment feasibility is environment-sensitive evidence, not `Evidence.Monotone`.**
`feasibility_not_monotone_under_extension`: a monotone design extension can
falsify it.  Phase 1's stable/sensitive distinction is realized as two
layers that are never merged.

**D-63. Numeric electrical/timing constraints deferred.**
Voltage, current, thermal, memory, CPU, deadlines, bandwidth, torque,
travel, power, PWM frequency values remain outside; the architecture leaves
room for set-level constraints but establishes nothing about them.

## Phase 8a

**D-64. Behaviour components are surface objects; the kernel is unchanged.**
Rejected: a kernel term for components/instances; a second typing judgment
for components.
Reason: every property the milestone needs is a property of the flattened
design under the *existing* judgments (`flatten_WF`, `union_globalWF`);
`BDL/Core` is untouched.

**D-65. A port is a template declaration by identity, with its public interface and clock.**
Rejected: ports by display name; ports as a separate kernel sort; physical
sinks as ports.
Reason: bindings must respect `tyView` and commitments (Phase 1), so the
port *is* the declaration's interface; sinks are resources, not
relationships (Phase 6), and stay in `Ω`/`β` (`ExternalSingleDriver`).

**D-66. Instantiation renames every identity the template owns; concepts and sinks are partitioned into internal (fresh) and global (shared).**
Rejected: identity by name; a global concept table per component; renaming
globals.
Reason: Counterexample 3 (`identity_renaming_aliases`,
`internal_concept_not_shared`); `Tilt` must be the same concept in every
instance, a private accumulator concept must not be.  The encoding
`W·(k+1)+n` is a device; only injectivity, decodability, and disjointness
from globals `< W` are used.

**D-67. Binding is a Phase-1 realization step.**
Rejected: a binding relation in the kernel; substitution of the source
body into the destination.
Reason: `binding_satisfies` + `local_refinement_preserves_global_wf`
give Theorem C/D for free; write-once realization means a port is bound at
most once (`dstNodup`).  Transport bindings elaborate to `sync` with an
explicit initial value (Phase 5); the source must be clocked.

**D-68. Composition well-formedness is stated on interfaces, never on bodies.**
Reason: substitutability (`substitute_composeWF`) is then a consequence of
`IfaceRefines`.  The two conditions beyond existing judgments are
`dstNodup` and `ExternalSingleDriver` (Counterexample 5).

**D-69. Causality across instances is a validation condition on the inter-instance direct-binding graph.**
Rejected: "causal components compose causally" (Counterexample 1);
port-level graphs (finer; deferred).
Reason: `flatten_causal`; self-edges are treated conservatively.

**D-70. Clock parameters are nominal variables substituted by κ at instantiation; rates never enter.**
Rejected: clock-indexed component types; frequency matching.
Reason: `Clocked.rename` holds for any κ, including one that merges two
parameters into one system domain; mismatch without `sync` is rejected
(Counterexample 2).

**D-71. Evidence must be equivariant and port-sound.**
Reason: `Evidence.Equivariant` is what "template validity is independent of
instance identity" means for commitments; `Evidence.PortSound` is what
makes binding by reference inherit commitments.  Both are conditions on
the validation layer, like `Evidence.Monotone`.

**D-72. Hierarchy is packaging, not a tree constructor.**
Rejected: an inductive `BehaviorSystem` tree with offset threading.
Reason: a flattened system is a design over identities `< flatWidth`, hence
a template (`toComponent`); nesting is instantiating packages.  The
`Realizes` proof for a package is a decidable side condition, not yet
discharged.

**D-73. Theorem J is proved on the single-domain wiring fragment with direct/constant bindings.**
Reason: the precedent of `unfolds_preserves_eval`; the multi-domain case
needs a domain-indexed input for transported ports, which `Input` cannot
express.  Recorded as an open item.

## Phase 8b

**D-74. A behaviour group is authoring metadata; `eraseGroups` is a projection.**
Rejected: a group as a kernel term; a group as a declaration; groups
carrying types, clocks, outputs or formulas.
Reason: Theorems A–G of `Group.lean` are `rfl`/`Iff.rfl` — the group never
enters the design, so nothing it could carry would be semantic.

**D-75. Group operations are semantic no-ops, not refinements or edits.**
Every operation (`group`, `ungroup`, `addMember`, `removeMember`, `move`,
`merge`, `split`) is the identity on `design`
(`group_is_identity_on_design`).  They are a fourth invalidation class
below "validation-only": nothing is rechecked.

**D-76. Aggregate sockets are projections of `DependsOn`.**
Rejected: socket declarations; fan-out edges; "union of input concepts".
Reason: Counterexample 6 (`fanout_false_dependency`); `socket_no_fanout`.
The dependency model is declaration-based, so the socket is
`crossIn`/`crossOut` over it.

**D-77. Boundary inference: required = crossing-in, provided = crossing-out, private = the rest without a sink, clocks = all clocks.**
Rejected: required = all member references (Counterexample 1); required =
own open declarations only (Counterexample 2); no clock parameters
(Counterexample 3).  Physical sinks are never semantic ports
(Counterexample 4); the drive edge stays with the member.

**D-78. Extraction = two restrictions of the design reconnected by Phase-8a bindings.**
Rejected: translating members into a new calculus; a tuple-returning
declaration (Counterexample 5); body substitution across the boundary.
Reason: the component body *is* the members' declarations; the
reconnection is Phase-1 realization; `flat_WF` reuses Phase 8a.

**D-79. Extraction causality is proved by subdividing the original graph, not by `InstAcyclic`.**
Reason: a group with both inputs and outputs has instance edges both ways;
`flat_causal` uses the rank `2·rank` / `2·rank + 1`.  Phase 8a's condition
is recorded as too coarse for extraction.

**D-80. Template realization needs interface-local evidence.**
`Evidence.InterfaceLocal`: a discharged commitment depends only on the
interfaces of the referenced declarations.  Without it a member's
commitment discharged in the whole design could not be carried into the
template, where its dependencies are unresolved port copies.

**D-81. Identity: templates keep original identities; instances are fresh; the group id is never a component id.**
Before packaging nothing is renamed (D-74).  After packaging the flattened
system uses `W + n` and `2W + n`; further instances `3W + n`, ….

**D-82. Nested groups are a relation on the flat group list.**
Rejected: a recursive group type.  Reason: no kernel significance to
represent (`nested_no_semantics`).

## Phase 9a

**D-83. `Ty.list τ` is a kernel data type; the object-language buffer needs it and nothing else.**
Rejected: `latest` (Model A), `count` (B), `coalesce μ` (C), a fixed
tuple (D) as the transported representation — each identifies distinct
windows (`latest_not_lossless`, `count_not_lossless`, `sum_not_lossless`,
`modelD_not_lossless`); every summary bounded to the newest `k` entries
is lossy (`bounded_summary_not_lossless`).  Reason: Phase 5 showed
multiplicity and order observable; a lossless summary is injective and
therefore unbounded.  Claim strength: the list is the smallest general
sequence representation *tested*, not the only possible one.

**D-84. Six list operators, registered through `Prim.ty`: `nil`, `cons`, `length`, `take`, `reverse`, `head`.**
Rejected: list typing/evaluation/domain rules; a general folding
combinator in the kernel.  Reason: the buffer and every tested policy
need only these; typing is primitive application, evaluation is
`applyPrim`, `Clocked` has no list clause (`list_clock_conservative`).
Every earlier theorem is generic in primitives and held unchanged.

**D-85. The buffer is a surface elaboration into five declarations over `delay`/`sync`.**
`log @src := cons src (delay nil log)`, `logD @dst := sync src nil log`,
`seen := length logD`, `cursor := delay 0 seen`,
`window := reverse (take (seen − cursor) logD)`.  Rejected: a buffer
primitive; `Event τ`; a scheduler order; same-tick visibility.  Reason:
`buffer_window_correspondence` (Theorem M) — for every schedule, input,
domain and tick the window evaluates to the Phase-5 window exactly — with
K/L for typing and clocking.  The Phase-5 `buffer_from_log_and_cursor` is
reused.

**D-86. Capacity is validation; overflow policies are explicit; only rejecting the deployment preserves semantics.**
`CapacitySufficient` (decidable for a finite horizon), `requiredCapacity`
(least sufficient, proved), `periodic_capacity_sufficient` (one
destination period suffices for periodic schedules at every horizon).
`dropOldest`/`dropNewest` are functions of the unbounded window: identity
under sufficient capacity (`sufficient_capacity_preserves`), trace-changing
under insufficient capacity (`negE`).  Rejected: implicit overflow in the
kernel.

**D-87. Buffered transport is a Phase-8a binding choice, not a transport kind.**
A sensor component provides both its event and its log; binding the log
through `sync nil` yields the window (`transport_trace`), binding the
event yields `latest` (`latest_transport_loses`).  No new binding kind.

## Phase 9b

**D-88. Products enter the kernel as value composition: `prod`, `pair`, `fst`, `snd`.**
Rejected: Church/function encodings (arrows are not data —
`arrow_not_delayable`; first-class use needs rank 2 — `church_fst_rank`);
tuples as component interfaces or output bundles (Phases 6, 8 unchanged).
Reason: paired state must be delayable (`pair_state_delayable`).

**D-89. The list recursor `fold` is a term former, not a registered operator.**
Rejected: a `fold` primitive (operators never apply closures; a
closure-applying operator would need the evaluation relation inside
`Prim.compute`); per-operation primitives `map`/`any`/`all`/…; bounded
unrolling.  Reason: one eliminator derives every collection operation
(`Stdlib`); evaluation is syntactic unrolling through the environment
(`Ev.foldCons`), so `Ev` stays an ordinary inductive and every earlier
proof extends by one case.  Totality by `fold_total`.

**D-90. `eq` at every data type, with the data proof in the syntax.**
Rejected: equality on quantities only (boolean equality had to be
encoded); a typing side condition (would change the `prim` rule).
Reason: structural equality is defined on all data values (`Value.beq`);
typing already forbids comparing two concepts.  The proof field makes
`eq (arr ..)` unwritable.  *(9b also generalized `lt` to every data type
through a structural order; D-98 reverts that.)*

**D-91. `toList : opt τ → list τ` and `drop` are registered operators.**
Reason: without `toList` an option has no eliminator that does not need a
default value; with it `fold` eliminates options (`optElimF`, `mapOptF`).
`drop` is the dual of `take`, needed by `zip`.

**D-92. Rank-1 polymorphism is definitional: families instantiated by matching; no type variable in the kernel.**
Rejected: kernel type variables (open declaration types would be
meaningless); System F terms (`Λ`, `[τ]`) — their prenex fragment is family
instantiation (`PolyAlternatives`); higher rank — every candidate is rank
≥ 2 with a rank-1 replacement (`applyBoth_rank`, `applyBoth_replacement`);
let-generalization and principal-type search — use sites have closed
argument types, so instantiation is one-way matching (`matchTy_sound`,
`matchTy_complete`).

**D-93. Constraints: the closed vocabulary {Data}; no user-defined classes.**
Rejected: hardcoded per-operator admissibility (subsumed), an open class
system, dictionary passing.  Reason: `eq`, `lt`, `delay`, `sync` are the
only constrained operations and all need exactly `Data`; a designer's
custom order is a comparator argument (`minByF`).  Dimension genericity
is a pattern variable over `Dim` (`PDim.dvar`); no kind system.

**D-94. The equation library is a set of combinators, inlined at use sites.**
`Comb`: no reference, state, transport, `rep` or `mk`.  Proved once:
typing independent of Δ, Θ, G (`HasType.comb_irrelevant`), evaluation
context-free (`lib_eval_context_free` from `Ev.pure`), clocked everywhere
(`lib_clocked`), no construction (`Comb.noConstruct`), and the combined
expansion statement (`lib_expansion`).  Rejected: library functions as
declarations (would be monomorphic and would enter the dependency graph).

**D-95. Sets, intervals, records, predicates, finite quantifiers are surface.**
`x ∈ {…}` is `contains` over a list literal (`oneOf_mem`; duplicates
irrelevant); an interval is a pair with a convention (`inIntervalF`); a
record is a right-nested pair with positional projections (`recTy`,
`projE_typed`); a predicate is `α → bool`; `forall/exists x in xs` are
`all`/`any` (`forall_in_list`, `exists_in_list`).  Rejected: a `Set`
type, a record type, row polymorphism, quantifiers in expressions.

**D-96. Sums are encoded; a kernel `sum` is deferred.**
`enum LampMode { Off, Automatic, Manual(Brightness) }` is a tag paired
with an optional payload; `match` is conditionals on the tag (`exM`).  A
kernel `sum` would need one more eliminator term former; deferred until a
case needs exhaustiveness beyond the encoding.

**D-97. Existentials are not needed: hiding is Phase-8a instantiation.**
Private concepts and identities are freshened per instance; the public
contract is the interface.  The type-theoretic encoding is rank 2
(`existential_rank`).

## Phase 9c

**D-98. Ordering is a quantity comparison; the kernel has no structural order.**
`lt` is `lt (d : Dim)` again (Phase-4 form); `Value.blt` is removed.
Rejected: `lt` at every data type (9b) — `mode1 < mode2`, `None < Some x`
and lexicographic pairs/lists have no behaviour-design meaning and their
order would come from codes, constructor tags or `SemanticId`s
(`lt_rejected`, `min_mode_rejected`); a kernel `Ord` predicate on types
(unnecessary: an ordered concept compares as `lt d` on `rep`).  An
implementation's canonical order for maps/serialization is not a language
capability.

**D-99. The surface capability vocabulary is {Data, Eq, Ord}; Eq ≡ Data today; Ord is by declaration.**
`Poly.Cap`, `Scheme.caps`, `Ty.ordB O Θ`: quantities, and concepts the
designer declared ordered (`OrdDecl`) with a quantity representation.
`Cap.eq_iff_data` records the coincidence; `Cap.ord_data` that Ord ⇒
Data and not conversely.  Rejected: user-defined classes, instance search,
superclasses (no case); deriving order from declaration/constructor order
(enums included).  Diagnostics name the capability and the concept.

**D-100. Ordered library entries take `Ordered` evidence; comparators recover them.**
`min`/`max`/`clamp`/`inRange`/`inInterval` are indexed by `Ordered τ`
(`q d` | `sem s d`, well formed against Θ); `contains`/`oneOf` keep the
`Data` proof; `map`/`fold`/`any`/`all`/`filter` need neither.
`minBy_recovers_min`: the comparator escape hatch loses nothing.
Combinators admit `rep` (needed by ordered concepts); their typing is
independent of Δ and G and reads Θ only through write-once bindings.

## Phase 10

**D-101. Units remain entirely surface; coordinate extraction and quantity construction are elaborated quantity arithmetic.**
`inUnit q u := div q (lit d scale(u))`, `withUnit x u := mul x (lit d scale(u))`,
`n u := withUnit n u`.  Rejected: runtime unit values (no case delays,
syncs, stores or compares a unit), units in `Ty` (`1 m` and `100 cm`
would differ in type), a kernel conversion primitive (`convert` is the
composition: `convert_eq`, `convert_trans`).  Reason: `inUnitE_typed`,
`inUnitE_safe`, `withUnitE_typed`, `withUnitE_is_quantity`,
`unitOps_no_construction`.

**D-102. Unit semantics are stated exactly over an abstract scalar domain; the kernel's `Nat` and production's floats are models.**
`Scalars K` with `Sym` (free abelian group on `2,3,5,127,π`): π is a
generator, `deg = π/180` exact.  The `Nat` registry uses canonical
sub-units and has no radian; round trip 2 holds under divisibility only.
Rejected: pretending π is rational; hiding float approximation.

**D-103. A unit is an identity with a dimension and a scale; spelling is presentation.**
`Unit K = ⟨id, dim, scale⟩`; symbols and display names live in the
registry's presentation columns.  `unitsFor` is sound and complete
relative to the registry.

**D-104. The Formula Composer's formal basis is typed holes with local bidirectional dimension inference — no unification.**
`PExpr`, `check`, `solve` (add/sub propagate; mul `r−d`; div `r+d`, `d−r`);
`solve_sound`, `solve_complete`; candidates from the solved dimension
(`candidates_sound/_complete`).  Two-hole operands are unsolved, not
searched.  Rejected: a general constraint solver; executing partial terms.

**D-105. Preferred display units are presentation, not design.**
`Presentation` beside `Design`; every kernel judgment is unchanged by
construction (`presentation_irrelevant_*`); ordering compares canonical
magnitudes (`ordering_ignores_presentation`).  Design guidance: literal
unit = semantic source (in the formula text); concept preferred unit =
authoring metadata; simulation unit = UI state.

**D-106 (revised in Phase 10b). Affine conversion is complete as coordinate-change semantics; point/delta is optional physical-arithmetic validation.**
`celsius_not_linear`; `affLitE`/`affInUnitE` exact (`K/180` basis);
`delta_is_linear`; `sum_of_points_is_not_a_point` while `sum_well_typed`.
Phase 10b: the chart laws, the groupoid laws and the difference law are
proved without any sort (`Charts.lean`); `AffSort` is orthogonal to
conversion (`sort_orthogonal_to_conversion`).  Rejected: a kernel
temperature type; faking °C with a scale; deferring conversion; `Ty.q d
sort`.  Retained as optional: a validation annotation over operand sorts.

## Phase 10b

**D-107. Unit coordinates are an erasure that preserves the affine coordinate change.**
A chart is `⟨scale, offset⟩` over a field; `coord`/`reconstruct` are
inverse (`chart_left_inverse`, `chart_right_inverse`); the coordinate is a
bare scalar with no chart in it (`coordinate_is_chartless`,
`coordinate_needs_chart`) and the other coordinates are recovered from it
and the charts (`unit_erasure_preserves_conversion_structure`).
Rejected: a runtime unit tag on scalars; units as data.

**D-108. Conversions form a groupoid of affine isomorphisms; differences carry the linear part.**
`convert_is_affine`, `convert_identity`, `convert_compose`,
`convert_inverse` (from the chart laws alone); `difference_map`,
`difference_offset_cancels`, `linear_part_identity`,
`linear_part_compose`.  Rejected terminology: "Celsius-to-Fahrenheit is a
group homomorphism" (`not_additive_of_offset`, `CtoF_not_additive`).

**D-109. The exact scalar domain is a choice-free rational field built in the development.**
`Rational.lean`: `Q` as a quotient of `Int` fractions; laws by `Int` ring
identities; concrete equalities decided by cross-multiplication.
Rejected: core `Rat` (its lemmas depend on `Classical.choice`); `Nat`
(no negatives, no fractions); floating point in the formal model.
Production `f64` gets a toleranced property-test contract, not an
exactness claim.

**D-110. Unit conversion and sensor calibration are one affine-map abstraction.**
`exH` (ADC → mV → calibrated reading), `exI` (encoder count → angle with
home offset) instantiate the same theorems.
