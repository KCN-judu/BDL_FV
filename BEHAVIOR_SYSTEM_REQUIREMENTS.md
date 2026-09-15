# Behavior-System Extension Requirements

*Architectural specification for the production BDL behaviour-system
milestone, derived from the Phase 8a formalization (`BDL/Behavior/`,
`REPORT.md` §8, `BEHAVIOR_NOTE.md`). Every "necessity" cited is a Lean
theorem or counterexample in the repository; every classification follows
the minimality audit.*

Layer vocabulary used below: **kernel semantic** (changes `BDL/Core`),
**surface abstraction** (a designer-facing object that elaborates to
kernel declarations), **elaboration machinery** (meta-level transformation,
no semantic content), **validation rule** (a check over a finished design
or composition), **deployment concern** (target-relative).

Summary of the formal finding: **no kernel semantic construct is required
for behaviour systems.** Every capability below is a surface abstraction,
elaboration machinery, or a validation rule over the existing five
judgments. The compiler's kernel (typing, satisfaction, clocks, causality,
outputs, tick semantics) is unchanged by this milestone.

---

## Capabilities

### 1. Naming and referencing a behaviour

1. *Expressible now?* Partly. A single design's declarations are named and
   referenced (`declRef`, Phase 1). A *behaviour as a unit* has no name.
2. *New construct.* `BehaviorComponent` (a named template) and `Port`
   (a template declaration exposed by identity). References to a
   behaviour's ports are pairs `(instance index, port DeclId)`.
3. *Classification.* Surface abstraction.
4. *Necessity.* Bindings must be by identity, not display name: renaming is
   a refactoring (Phase 2 `semantic_rename_preserves_identity`), and
   Counterexample 3 (`identity_renaming_aliases`) shows name-based
   instantiation aliases instances.
5. *Minimal production change.* A component registry keyed by an internal
   component id; port references carry `(instanceId, portId)`, where
   `portId` is the template-local `DeclId`. Display names remain a surface
   table.
6. *Unchanged.* Typing, satisfaction, dependency analysis, evaluation.

### 2. Abstraction behind an interface

1. *Expressible now?* No. A design exposes all declarations.
2. *New construct.* `BehaviorInterface = {required, provided, params,
   clockParams}` with `Port = (DeclId, DeclInterface, Option ClockId)`.
   `Realizes` checks that the template's ports are declarations with
   exactly the advertised interface and clock, required ports and
   parameters unresolved, parameters data-typed and agnostic.
3. *Classification.* Surface abstraction + validation rule (`Realizes` is a
   decidable check over the template).
4. *Necessity.* Composition well-formedness must be stated on interfaces
   alone for substitutability to hold (`substitute_composeWF` is proved
   from `IfaceRefines`); stating it on bodies would make every
   replacement a re-verification of the whole system.
5. *Minimal production change.* Store, per component, the port list with
   `(id, expectedType, commitments, clock)`; run `Realizes` once per
   template version; cache the verdict.
6. *Unchanged.* Everything inside the template is checked by the existing
   design checker.

### 3. Instantiation with fresh identity

1. *Expressible now?* No. Two copies of a design collide on every id.
2. *New construct.* `Ren.inst C W k κ`: rename every internal `DeclId`,
   internal `SemanticId`, internal `OutputId`, internal `ClockId` to a
   fresh value; substitute clock parameters by κ; leave global concepts
   and external sinks fixed.
3. *Classification.* Elaboration machinery.
4. *Necessity.* Theorem A (`inst_decl_disjoint`, `inst_sem_disjoint`,
   `inst_out_disjoint`, `inst_clock_disjoint`, `inst_sem_not_global`,
   `inst_out_not_global`); Counterexample 3. Renaming preserves every
   kernel judgment: `HasType.rename` (no injectivity needed),
   `Satisfies.rename`, `Clocked.rename`, `Expr.rename_instRefs`.
5. *Minimal production change.* A generative identity supply with three
   properties: fresh ids are injective in `(instance, local id)`,
   decodable back to `(instance, local id)`, and disjoint from global ids.
   The arithmetic `W·(k+1)+n` is one such supply; any other (e.g. tagged
   ids) is acceptable. The renamer must traverse `Ty` (for `sem`), `Prim`
   (for the `τ` inside `ite/none/some/isSome/getD`), `Expr` (`declRef`,
   `mk`, `sync`'s clock), `DeclInterface`, and `OutputSpec`.
6. *Unchanged.* All judgments; the renamer is a pure function outside them.

### 4. Internal vs shared identity (concepts, sinks, clocks)

1. *Expressible now?* No; there is no notion of ownership.
2. *New construct.* Per-template flags `internalSem`, `internalOut`; clocks
   are internal unless listed in `clockParams`.
3. *Classification.* Surface abstraction (a declaration on the template).
4. *Necessity.* `internal_concept_not_shared`: a private concept must not
   be identified across instances; a shared one (`Tilt`) must be. Both
   needs are real and only the designer can say which is which.
5. *Minimal production change.* A visibility flag on concept and sink
   declarations inside a component (`private` / `shared`); default
   `private` for sinks and `shared` for concepts is a reasonable surface
   policy, not a formal requirement.
6. *Unchanged.* Semantic identity mechanism (Phase 2), sink identity
   (Phase 6).

### 5. Explicit binding between instances

1. *Expressible now?* Yes, at the kernel level: a binding *is* a Phase-1
   realization step (`realize`) of the destination port with `declRef src`.
2. *New construct.* `Binding = (src : port | const, dstInst, dst,
   transport : Option init)`; `BindingWF`.
3. *Classification.* Surface abstraction that elaborates to an existing
   refinement step; `BindingWF` is a validation rule.
4. *Necessity.* `binding_satisfies` (Theorem C) shows the realization
   satisfies the port's interface exactly when `BindingWF` holds and the
   evidence is port-sound; Counterexample 4 (`tiltToMotor_binding_rejected`,
   `tiltToMotor_forced_ill_typed`) shows a type-incompatible binding
   produces an ill-typed realization. Commitments: destination ⊆ source.
5. *Minimal production change.* Implement binding as: check
   `BindingWF` (type equality after renaming, commitment inclusion, clock
   compatibility), then call the existing "realize declaration" operation
   with the body `declRef`/`sync`/constant. Enforce at most one binding per
   destination (`dstNodup`) — write-once realization already guarantees
   this if the realize operation refuses a second body.
6. *Unchanged.* Realization, satisfaction, global well-formedness
   (`local_refinement_preserves_global_wf` is reused verbatim).

### 6. Cross-domain binding

1. *Expressible now?* Yes: `sync c init e` (Phase 5).
2. *New construct.* None; `Binding.transport = some init` elaborates to
   `sync (K src) init (declRef src)`.
3. *Classification.* Elaboration machinery.
4. *Necessity.* Counterexample 2 (`clockMismatch_binding_rejected`,
   `clockMismatch_not_wellClocked`): a direct binding across domains is
   not well clocked. `flatten_wellClocked` (Theorem G) shows the
   transported binding is.
5. *Minimal production change.* The binding editor must require an
   initial value when the two ports' (substituted) clocks differ and the
   source is clocked; agnostic sources bind directly.
6. *Unchanged.* `Clocked`, `MEv`, the strictly-before rule.

### 7. Clock parameters

1. *Expressible now?* No; a design's clocks are fixed `ClockId`s.
2. *New construct.* `clockParams : List ClockId` on the interface and the
   assignment `κ` on the instance.
3. *Classification.* Elaboration machinery (substitution).
4. *Necessity.* A reusable component cannot mention system domains
   (`Tilt@fast` in one product is `Tilt@ambient` in another).
   `Clocked.rename` holds for every κ, including a κ that merges two
   parameters — so merging is allowed and needs no check. Rates never
   appear (Phase 5 D-47).
5. *Minimal production change.* Clock parameters are local `ClockId`s
   substituted at instantiation; the instantiation UI asks for one system
   domain per parameter. No frequency information is involved.
6. *Unchanged.* `ClockEnv`, `Clocked`, schedule model.

### 8. Reuse (several instances of one template)

1. *Expressible now?* No (see 3).
2. *New construct.* None beyond instantiation; the *requirement* is on the
   validation layer: `Evidence.Equivariant`.
3. *Classification.* Validation rule (constraint on evidence).
4. *Necessity.* `union_globalWF`: every instance is well formed in the
   system for every index, *given* equivariance. Evidence that inspected
   identities would break reuse.
5. *Minimal production change.* Validation procedures must be written
   against the *template* and must not depend on concrete ids (i.e. they
   must be invariant under renaming). Cache template verdicts; never
   re-run them per instance.
6. *Unchanged.* Kernel; evidence interface (`Evidence`).

### 9. Hierarchical composition

1. *Expressible now?* No.
2. *New construct.* `BehaviorSystem` (flat list of instances + bindings)
   and `toComponent` (packaging a flattened system as a template over
   identities `< flatWidth`).
3. *Classification.* Surface abstraction; packaging is elaboration.
4. *Necessity.* None for a tree constructor: packaging achieves nesting
   (D-72). The proof obligation for a package (`Realizes` of the chosen
   interface) is a decidable side condition (not yet mechanized).
5. *Minimal production change.* Represent nesting as "instantiate a
   package"; a package's width is `W·(N+1)`; the enclosing system's width
   must exceed it. No recursive system datatype is required.
6. *Unchanged.* Everything: a package is a design.

### 10. Semantics-preserving flattening

1. *Expressible now?* The target (`Design`) exists; the map did not.
2. *New construct.* `flatten` = disjoint union + one realize step per
   binding.
3. *Classification.* Elaboration machinery.
4. *Necessity / guarantees.* Theorem D `flatten_WF` (globally well formed,
   concept env well formed, well clocked, causal under `InstAcyclic`,
   `DriveWF`, `SingleDriver`); Theorem H `open_port_stays_open`; Theorem J
   `modular_iff_flat` (single-domain wiring fragment, direct/constant
   bindings). Flattening renames `delay`/`sync` bodies only; it never
   changes the delay or strictly-before rules.
5. *Minimal production change.* The elaborator emits the union then applies
   bindings as realizations; nothing else. Do **not** substitute source
   bodies into destinations (that would break write-once and provenance).
6. *Unchanged.* Evaluation (`Ev`/`MEv`), interpreter, causality checker,
   clock checker — all run on the output unchanged.

### 11. Composition-level causality

1. *Expressible now?* `Causal` on the flattened design, yes; a
   *compositional* check, no.
2. *New construct.* `InstDep` (direct-binding graph) and `InstAcyclic`.
3. *Classification.* Validation rule (a sufficient condition for the
   existing `Causal`).
4. *Necessity.* Counterexample 1 (`feedback_composition_not_causal`): two
   causal components compose into an instantaneous cycle. Theorem F
   `flatten_causal`: instance-level causality + acyclic direct-binding
   graph ⇒ flattened causality.
5. *Minimal production change.* Either run the existing causality checker
   on the flattened design (always correct), or, for incremental
   diagnostics, maintain the instance-level graph of direct bindings and
   report cycles at the binding that closes them, suggesting `sync`.
6. *Unchanged.* `Causal`, `InstDependsOn`, ranks.

### 12. Physical outputs across instances

1. *Expressible now?* `SingleDriver`, `DriveWF` on the flattened design,
   yes.
2. *New construct.* `ExternalSingleDriver` (validation condition on the
   composition) and the internal/external sink partition.
3. *Classification.* Validation rule; deployment concern for external
   sinks.
4. *Necessity.* Counterexample 5 (`twoDrivers_not_singleDriver`): two
   instances of a single-driver template driving one shared sink violate
   single-driver after composition. Theorem I `flatten_singleDriver`.
5. *Minimal production change.* When two instances drive one external
   sink, report at the sink with the Phase-6 message ("this output already
   has a final driver; combine before driving") — the same diagnostic as
   for two declarations in one design.
6. *Unchanged.* `OutputEnv`, `DriveEnv`, `DriveWF`, `SingleDriver`,
   `CompleteOutputs`, physical output semantics.

### 13. Open systems

1. *Expressible now?* Yes: unresolved declarations (Phase 0/1).
2. *New construct.* `OpenPorts`, `Design.Open`, `Design.Executable`
   (structural WF vs executable closed).
3. *Classification.* Validation rule (acceptance levels).
4. *Necessity.* Theorem H: an unbound required port is an ordinary
   unresolved declaration; `ComposeWF` never requires all ports bound.
5. *Minimal production change.* The workspace reports unbound required
   ports as *open*, not as errors; "executable" additionally requires every
   required port bound or declared as a system input, and
   `CompleteOutputs`.
6. *Unchanged.* Acceptance-level machinery.

### 14. Parameters

1. *Expressible now?* Yes, as unresolved data-typed declarations.
2. *New construct.* `params` on the interface; `BindSrc.const`.
3. *Classification.* Elaboration-time typed substitution.
4. *Necessity.* `binding_satisfies` (const case) via
   `HasType.refFree_env_irrelevant`: a closed, delay-free constant typed at
   the port's type is a satisfying realization. No runtime machinery.
5. *Minimal production change.* Parameters are ports with `clock = none`,
   data type, bound to literals at instantiation; the same realize
   operation applies.
6. *Unchanged.* Everything.

### 15. Substitutability / refinement of components

1. *Expressible now?* Interface refinement of single declarations, yes
   (Phase 0/1). Of components, no.
2. *New construct.* `IfaceRefines`, `Substitutable`, `replace`.
3. *Classification.* Validation rule.
4. *Necessity / guarantee.* `substitute_composeWF`: replacing an instance
   by an interface-refining component (same required/provided/parameter
   ports with equal types and clocks, stronger provided commitments,
   weaker required commitments, possibly extra open required ports, same
   identity partition and concept bindings, no new external drives)
   preserves `ComposeWF`. No behavioural equivalence is claimed.
5. *Minimal production change.* The component registry compares versions
   by `IfaceRefines`; a refining version can be swapped in without
   re-checking bindings; a non-refining one is an edit (Phase 1
   refinement-vs-edit discipline applies).
6. *Unchanged.* Kernel.

### 16. Hardware feasibility of composed systems

1. *Expressible now?* Yes: Phase 7 runs on any design, including
   `flatten S`.
2. *New construct.* None.
3. *Classification.* Deployment concern.
4. *Necessity.* Sinks of the flattened design are ordinary `OutputId`s;
   requirements derive from device kinds as before.
5. *Minimal production change.* None; run the solver on the flattened
   design's sinks. Private sinks of instances multiply requirements
   (two lights need two PWM lines), which is the correct behaviour.
6. *Unchanged.* `BDL/Validation/Hardware`.

---

## Constraints and implications for the production implementation

* **Do not modify the kernel.** Nothing in this milestone requires a change
  to types, typing, satisfaction, clocks, causality, outputs, or the tick
  semantics. Any proposal that does must produce a counterexample the
  surface layer cannot handle.
* **Identity supply.** Provide fresh ids per instance for declarations,
  private concepts, private sinks, and internal clocks; keep global ids
  below the system width (or in a disjoint namespace). Never derive
  instance ids from names.
* **Renamer coverage.** The renamer must reach `sem` inside types, the `τ`
  inside `Prim.ite/none/some/isSome/getD`, `mk`'s concept, `sync`'s clock,
  `OutputSpec`, and `DeclInterface`. Omitting the `Prim` case silently
  breaks typing of renamed bodies.
* **Binding = realize.** Implement binding through the existing
  realization operation, with `BindingWF` as its precondition. Destination
  ports are bound at most once. Never inline source bodies.
* **Transport bindings** require a clocked source and an explicit initial
  value; agnostic sources bind directly.
* **Evidence discipline.** Validation procedures must be renaming-invariant
  (equivariant) and must let references and transports inherit public
  commitments (port-sound). Procedures that inspect concrete ids or
  re-derive commitments from bodies violate reuse.
* **Global conditions at composition time.** Two checks are not local to
  any component: acyclicity of the direct-binding graph (or simply the
  causality checker on the flattened design), and at most one driver per
  external sink.
* **Hierarchy is packaging.** A subsystem is flattened and instantiated as
  a template; widths nest multiplicatively. No recursive system type.
* **Open systems are valid.** Unbound required ports are open declarations;
  "executable" is the separate, stronger level.
* **Semantics.** Flattened evaluation is the reference semantics. The
  modular semantics (per-instance evaluation with consistent port inputs)
  is proved to agree on the single-domain wiring fragment with direct and
  constant bindings; production tooling may evaluate modularly for
  diagnostics but must not claim agreement beyond that fragment until
  Theorem J is extended to `MEv` with `sync` bindings and to higher-order
  bodies.
* **Not established.** The `Realizes` obligation for packaged systems;
  port-level (finer) inter-instance causality; existence of the modular
  solution constructively; any behavioural equivalence between a component
  and a refinement of it.

---

## Minimal extension set

### REQUIRED

* `BehaviorInterface` / `Port` (surface): required, provided, parameter
  ports by template `DeclId` with public interface and clock; clock
  parameters.
* `BehaviorComponent` + `Realizes` (surface + validation): template design
  over local ids with an internal/global partition of concepts and sinks;
  decidable realization check.
* Instantiation with fresh identity (elaboration): the renamer over
  `Ty`/`Prim`/`Expr`/`DeclInterface`/`OutputSpec`; clock-parameter
  substitution; a fresh-id supply that is injective, decodable, and
  disjoint from globals.
* `Binding` elaborated as a Phase-1 realization step (surface +
  elaboration) with `BindingWF` (validation): type equality, commitment
  inclusion, clock compatibility or explicit `sync` with initial value;
  constant bindings for parameters.
* `flatten` (elaboration): disjoint union + realize per binding.
* `ComposeWF` (validation): instance validity and width fit; shared-concept
  and external-sink agreement; `BindingWF` for every binding; destinations
  bound at most once; `ExternalSingleDriver`.
* Evidence constraints (validation): equivariance and port-soundness, in
  addition to Phase-1 monotonicity.
* Open-system acceptance (validation): unbound required ports are open,
  not invalid; executable = closed + complete.

### OPTIONAL

* `InstAcyclic` as an incremental, binding-local causality diagnostic
  (the flattened `Causal` check is always sufficient and is required).
* `IfaceRefines`-based component versioning and substitution
  (`substitute_composeWF`), for designer–engineer hand-off.
* Modular (per-instance) evaluation for diagnostics, within the proved
  fragment.
* A port-level inter-instance dependency graph (finer than `InstAcyclic`).

### DERIVABLE / SHOULD NOT BE PRIMITIVE

* A kernel term for components, instances, or bindings — derivable:
  everything elaborates to declarations and realization steps (D-64).
* A component-level typing or clock judgment — derivable: `HasType.rename`,
  `Clocked.rename` and the flattened design's judgments suffice (D-64,
  D-70).
* A recursive/hierarchical system datatype — derivable by packaging
  (`toComponent`, D-72).
* Component ports as physical outputs — must not be primitive: sinks are
  resources, ports are relationships (D-65, Phase 6).
* Runtime parameters — derivable: elaboration-time typed substitution of
  closed constants (§14).
* Frequency-based clock compatibility — must not exist: clock identity is
  nominal; parameters are substituted, never matched by rate (D-70).
* Name-based instance identity — must not exist (Counterexample 3).
* Body substitution at binding — must not exist: binding is by reference
  (write-once, provenance).
