# MINIMALITY — construct-by-construct status

Legend for the table: **K** kernel, **S** surface (desugars), **V**
validation layer, **R** remove.  `?` = pending the named phase.

Terminology follows the post-Phase-1 declaration ontology (REPORT §M): the
kernel object is a `DesignDecl` (id × interface × optional realization);
"hole" is a surface metaphor only.

| Construct | Kernel | Surface | Validation | Remove | Reason |
|---|---|---|---|---|---|
| `DeclId` (stable declaration identity) | yes — as an ordinary declaration key, **not** because persistent identity is novel | — | — | no | references resolve against it (probe 3); Phase 1 showed it is exactly a name |
| display `name` | no | yes | no | — | renaming is a refactoring over the id (D-14) |
| `DesignDecl` = id × interface × `Option` realization (one record for unresolved and realized) | yes | — | — | no | environment order needs one object across states (`EnvRefines_update`); `realization = none` is the whole content of "unresolved" |
| "hole" as a kernel notion | no | yes (metaphor for `realization = none`) | — | **yes** | D-15 |
| `DeclInterface.expectedType` frozen under refinement | yes | — | — | no | probe 4: retyping breaks every client |
| `DeclInterface.commitments`, monotone, **public, part of the interface** | yes (as interface data) | — | discharge only | no | probe 5: dropping a commitment silently breaks dependents |
| `InterfaceRefines` preorder | yes | — | — | no | `InterfaceRefines_iff_semantic`: complete for abstract evidence |
| write-once realization | yes | — | — | no | D-07: detaching is non-monotone for evidence |
| re-verification on `strengthen` | yes | — | — | no | Phase 0 Theorem 4 counterexample |
| `declRef` in terms | yes | — | — | no | the whole of Phase 1 |
| `DeclEnv` + `update` at own id | yes | — | — | no | `EnvRefines_update` |
| typing reads `tyView` (expected type) only | yes | — | — | no | sufficient (theorem) and necessary (probe 4) for client stability |
| refinement vs edit distinction | yes (documented; only refinement is formalized) | — | — | no | D-16; probes 3–5 are edits, not refinements |
| general edit relation / invalidation tracking | ? | — | ? | — | pending; Phase 7 |
| `Evidence` / `DischargedBy` | no | no | yes | no | never decided by the kernel |
| `Evidence.Monotone` (stability of refinement-surviving evidence) | constraint imposed by kernel on V | — | yes | no | probe 6 |
| environment-sensitive / recheck-required evidence | — | — | ? | — | pending (Phase 7); documented in `Satisfaction.lean` |
| realization-dependency acyclicity (structural) | timeless fragment only | — | no | no | unfolding undefined on cycles (`Unfolds.not_of_cyclic`); superseded as execution criterion by `Causal` (Phase 4) |
| Phase-0 `Artifact` ref list | — | — | — | **yes** | subsumed by `declRef` (D-13) |
| several candidate definitions, one `active` (§3.2) | ? | likely | — | ? | pending: probably surface over write-once realization; detaching is an edit (D-16) |
| interface-level references (commitments mentioning declarations) | ? | — | ? | — | pending; needed for a full dependency graph |
| `SemanticId` (internal concept identity) | yes | — | — | no | Phase 2: distinct from `DeclId` (Model C) and from names (Counterexample C) |
| nominal `Ty.sem SemanticId` | yes | — | — | no | Phase 2: `semantic_identity_mismatch_rejected`; smallest among tested designs (D-19) |
| interface `semanticRole` field | no | no | no | **yes** (for the tested design) | Phase 2 Model B: must be frozen like the type; direct-wire checker η-evaded (D-19) |
| separate semantic-compatibility judgment — tested weak form | no | no | no | **yes** | formally rejected: `bweak_evaded_by_eta`, Counterexample D |
| separate semantic-compatibility judgment — general compositional-analysis family | — | — | — | **not universally ruled out** | tested strong formulation redundant with nominal typing (argued, not proved) |
| explicit semantic mapping | no | yes; represented as an ordinary declared arrow `sem a → sem b` | — | no | a design relationship, not a conversion (D-22) |
| concept as ordinary `DesignDecl` | no | no | no | **yes** | formally rejected: two category errors |
| stratified `ConceptDecl` (distinct sort, own identity) | not required in Phase 2 | may reappear in Phase 3 | may carry representation metadata | no | not rejected; reduces the Phase-2 requirement to an independent `SemanticId` |
| semantic concept declaration `decl Tilt` | no | yes → allocates a `SemanticId` | — | no | Phase 2; representation binding pending Phase 3 |
| concept display-name table | no | yes | no | — | rename is a surface refactoring (`semantic_rename_preserves_identity`) |
| `RepresentationBinding` witness (`ConceptEnv Θ`, `Θ s = some R`, sem-free, write-once) | yes | `decl Tilt represented by …` | — | no | Phase 3: D-27, D-29; monotone to bind, edit to rebind |
| `rep` (representation observation) | yes, unrestricted | — | — | no | safe everywhere (`provenance`, Model B); needed for any formula |
| `mk` (semantic construction) | yes, **granted only** | — | — | no | Model A bypass (D-26); licensed by the realized declaration's signature (D-28) |
| unrestricted symmetric `mk`/`rep` | no | no | no | **yes** | formally rejected: `unrestricted_representation_binding_bypasses_semantic_identity` |
| observation-only binding (no `mk`) | no | — | — | **yes** | formally unable to realize mappings by formula (`modelB_cannot_realize_mapping`) |
| construction grant `Grant.of` signature | yes | invisible (derived from the signature) | — | no | `constructs_granted`, `hidden_crossing_rejected_under_grant` |
| separate realization typing judgment | no — same judgment, indexed by grant | — | — | — | D-29: `HasType Θ Δ G`; client code at `Grant.none`, bodies at `Grant.of` |
| `Q[d]` = `Ty.q Dim` | yes | — | — | no | `dimension_mismatch_rejected`; baseline is its erasure (D-31) |
| dimension algebra | yes, in `Prim.ty` only | — | — | no | no dimension-specific typing rule needed |
| dimensions as metadata / validation | — | — | not formalized | — | engineering preference; not universally ruled out (§3.5) |
| units | no | yes → scaled dimensioned literal | — | no | `unit_scaling_preserves_dimension` (D-32); affine units pending |
| semantic–dimension association | in `Θ` (not in `SemanticId`, not in `Ty.sem`, not in `DeclInterface`) | — | — | — | `same_dimension_does_not_imply_same_semantic_identity` (D-33) |
| `Sem[n,d]` two-index constructor | no | no | no | **yes** | replaced by `Ty.sem s` + `Θ s = some (q d)` |
| `delay init e` (data-typed, top level) | **yes** | — | — | no | Phase 4: the only state primitive (D-34, D-35) |
| tick-indexed evaluation `Ev` | **yes** (semantics) | — | — | no | Phase 4: `Ev.det`, `reactive_total` |
| `Signal τ` as a type | no | (notation) | — | **yes** | Phase 4: identity on types under `Ev` (D-36) |
| `Event τ` as a primitive | no | yes → `opt τ` streams | — | **yes** (single domain) | Phase 4: `event_encoding_equivalent`; multiplicity → Phase 5 |
| `previous` | no | yes → `delay init x` / `delay none (some x)` | — | no | Phase 4 |
| `hold` / `count` / `since` / `once` / `every` / `rise` | no | yes → self-delayed declaration shapes | — | no | Phase 4: `*_trace` |
| `after` / `for` / `while` / `until` | no | yes → comparisons over `since`/`once`/activation | — | no | Phase 4 (composed, not separately executed) |
| `StateHandler` (activation, entry, reset-on-entry local state) | no | yes → gated self-delayed declarations | — | no | Phase 4 tested behaviour only (`scoped_counter_trace`); nesting/policies pending Phases 5–6 |
| temporal dependency information (`instRefs`, `strictRefs`) | **yes** | — | — | no | Phase 4: needed to state `Causal` and the negative theorem |
| instantaneous-acyclicity condition `Causal` | **yes** (well-formedness) | diagnostic | — | no | Phase 4 (D-37); replaces structural acyclicity |
| state initialization (`init` on every `delay`) | **yes** | shown | no | no | Phase 4 (D-38): semantic, not validation |
| state identity | no — structural | — | — | **yes** | Phase 4 (D-39) |
| explicit machine state / `Step` | pending | — | — | — | Phase 8 (D-42) |
| `ClockId` (nominal domain identity) | **yes** | declared `domain d` | — | no | Phase 5: A, B, E |
| numeric rate / period | no | annotation | **yes** | — | Phase 5 (D-47): induces a schedule; never in `Clocked`/`MEv` |
| clock-indexed type (`Signal[c,τ]`) | no | — | — | **yes** | Phase 5: forces polymorphism (`clocked_type_forces_polymorphism`) |
| declaration clock metadata (`ClockEnv Κ`) | **yes** (interface-level, frozen) | — | — | no | Phase 5 (D-44, D-46) |
| separate domain judgment `Clocked` | **yes** | diagnostic | — | no | Phase 5: rejects the direct wire; typing cannot |
| `sync src init e` (transport) | **yes** — the one temporal read | — | — | no | Phase 5 (D-45); `delay` = `sync own` |
| `hold` / `latest` | no | yes → `sync` | — | no | Phase 5 |
| `sample` | no | yes → `sync` at the destination's activation | — | no | Phase 5 |
| `buffer` / event queue | no | yes → five declarations over `sync` of a log + `delay` of a cursor + list data | capacity | no | Phase 5 (D-48); Phase 9a (D-85): `buffer_window_correspondence` |
| `drop` | no | yes → head of the window | — | no | Phase 5 |
| `coalesce μ` | no | yes → fold of the window | — | no | Phase 5 |
| transport initialization (`init` on `sync`) | **yes** | shown | no | no | Phase 5: deterministic first activation |
| scheduler / staging rule | no — strictly-before makes order irrelevant | — | — | **yes** | Phase 5: `scheduling_order_observable` shows why the alternative needs one |
| `Ty.list` and list operators (`nil`/`cons`/`length`/`take`/`reverse`/`head`) | **yes** (data type + registered operators) | — | — | no | Phase 9a (D-83, D-84): `bounded_summary_not_lossless`; no new typing/evaluation/domain rule |
| `Event τ` as a type | no | — | — | **yes** | Phase 9a: an event is a data-typed declaration in a domain; its lossless view is the window |
| `latest` / `count` / `coalesce μ` as the transported representation | no | yes → computation over `window` | — | as transport: **yes** | Phase 9a Models A–C: `latest_not_lossless`, `count_not_lossless`, `sum_not_lossless` |
| fixed-size event tuple | no | — | — | **yes** | Phase 9a Model D: `modelD_not_lossless` |
| buffer capacity | no | annotation | **yes** (`CapacitySufficient`, `requiredCapacity`, periodic bound) | no | Phase 9a (D-86) |
| overflow policy (`dropOldest`/`dropNewest`) | no | explicit computation over the window | reject-deployment preserves semantics | no | Phase 9a (D-86): `sufficient_capacity_preserves`, `negE` |
| `Ty.prod` / `pair` / `fst` / `snd` | **yes** (value composition only) | tuples, records | — | no | Phase 9b (D-88): `arrow_not_delayable`, `pair_state_delayable` |
| `fold` (list recursor, term former) | **yes** | `map`/`any`/`all`/`contains`/`filter`/… are definitions | — | no | Phase 9b (D-89): `fold_total`; `any_spec`, `map_spec` |
| `eq` at every data type (proof field) | **yes** | `==`, `contains`, `oneOf` | — | no | Phase 9b (D-90) |
| `lt d` on quantities | **yes** (Phase 4 form, restored in 9c) | `<`, `min`, `max`, `clamp`, `inRange` | — | structural order on data: **yes** (removed) | Phase 9c (D-98): `lt_rejected`, `lt_only_on_quantities` |
| Data capability | kernel evidence: the `eq` proof field; `delay`/`sync` premise | scheme variable `.data` | — | no | Phase 9c (D-99); claim: proved coextensive with Eq on this grammar (`Cap.eq_iff_data`) |
| Eq capability | no — coincides with Data | scheme variable `.eq` (diagnostic name) | — | no | Phase 9c (D-99); claim: extensional coincidence, not a definition |
| Ord capability | no — quantities, and declared-ordered concepts via `rep` + `lt d` | scheme variable `.ord`; `Ty.ordB O Θ`; `Stdlib.Ordered` | — | order on modes/pairs/lists/options/bools: **yes** | Phase 9c (D-98, D-99): `lt_rejected`, `min_mode_rejected`, `Cap.ord_not_data_converse` |
| user-defined typeclasses / instance search | no | — | — | **yes** | Phase 9c (D-99): no behaviour-design case; claim: rejected among tested models |
| explicit comparator arguments (`minBy`, `maxBy`) | no | yes — the escape hatch | — | no | Phase 9c (D-100): `minBy_recovers_min` (proved) |
| `drop`, `toList` | **yes** (registered operators) | option elimination, `zip` | — | no | Phase 9b (D-91) |
| rank-1 parametric polymorphism | no — families of monomorphic terms | generic definitions instantiated by matching | — | no | Phase 9b (D-92): `matchTy_sound`/`_complete`; `instances_are_monomorphic` |
| type variables / `∀` in kernel types; `Λ`/`[τ]` in terms | no | — | — | **yes** | Phase 9b (D-92): prenex = instantiation; higher rank unused (`applyBoth_rank`) |
| capability constraints | no | closed {Data, Eq, Ord} on scheme variables (9c) | — | user classes: **yes** | Phase 9b/9c (D-93, D-99): `Scheme.instantiate_sound`, `minByF` |
| definitional library (`min`…`zip`) | no | combinators inlined at use sites | — | no | Phase 9b (D-94): `lib_expansion`, `lib_eval_context_free` |
| `fn` helper declarations | no | closed lambdas, inlined | — | no | Phase 9b (D-94) |
| finite-set literal `x ∈ {…}` / `Set` type | no | `contains` over a list literal | — | `Set` type: **yes** | Phase 9b (D-95): `oneOf_mem`, `oneOf_dup_irrelevant` |
| intervals / ranges | no | pair + `inRange`/`clamp` | — | no | Phase 9b (D-95): `inRange_spec`, `clamp_spec` |
| records | no | nested pairs, positional projection | — | record type / row polymorphism: **yes** | Phase 9b (D-95): `projE_typed`, `records_are_pairs` |
| `Predicate α` | no | `α → bool` | — | **yes** as a type | Phase 9b (D-95) |
| finite `forall`/`exists x in xs` | no | `all`/`any` folds | — | general quantifiers in expressions: **yes** | Phase 9b (D-95): `forall_in_list`, `exists_in_list` |
| unbounded logical quantification, symbolic obligations | no | — | **future commitment layer** | — | Phase 9b: not built |
| enumerations / sum types | pending (deferred) | tag × optional payload | — | — | Phase 9b (D-96): `exM` |
| existential types | no | — | — | **yes** | Phase 9b (D-97): Phase-8a instantiation hides |
| GADTs, dependent types, impredicativity, effect systems | no | — | — | **yes** | Phase 9b: no behaviour-design case |
| `OutputId` (sink resource identity) | **yes** | device names | — | no | Phase 6 (D-50): `type_keyed_binding_collides` |
| output binding (drive edge `β`, `DriveWF`) | **yes** | "connect to actuator" | — | no | Phase 6 (D-51): type and clock equality only |
| single-driver global invariant | **yes** | diagnostic | — | no | Phase 6 (D-52): `multiple_direct_drivers_rejected` |
| exactly-one executable invariant (`CompleteOutputs`) | **yes** (acceptance level) | diagnostic | — | no | Phase 6: `executable_design_requires_complete_outputs` |
| action values / requests | no | — | — | **yes** | Phase 6 (D-54): relocate the conflict |
| effect rows | no | — | — | **yes** | Phase 6 (D-54): duplicate `β` or false-positive |
| output capabilities / ownership | no | — | — | **yes** | Phase 6: ownership uniqueness *is* `SingleDriver`; no linear types needed |
| runtime arbitration | no | — | — | **yes** | Phase 6 (D-53): `hidden_arbitration_observable` |
| priority policy | no | yes → `ite` in the single driver | — | no | Phase 6: `explicit_priority_single_driver` |
| merge policy (two contributors, two event sources) | no | yes → ordinary combination declaration | — | no | Phase 6: `explicit_target_composition_accepted` |
| target values | no — ordinary declarations | — | — | — | Phase 6: nothing special about a target |
| device-specific command types | no — another `SemanticId` + explicit mapping, or a representation sink | — | — | — | Phase 6: `representation_sink_needs_explicit_rep` |
| output clock metadata (`OutputSpec.clock`) | **yes** (in `Ω`) | shown | — | no | Phase 6: `output_binding_respects_clock_domain` |
| StateHandler output policies | no | yes → state-local target choice in one driver | — | **yes** (as a mechanism) | Phase 6: `statehandler_output_cases` |
| `ResourceId` / `Resource` (caps + per-capability units) | no | — | **yes** (validation) | no | Phase 7 (D-58) |
| `Capability` vocabulary | no | device descriptions | **yes** | no | Phase 7: opaque to the solver |
| `RequirementId` / `Requirement` | no | generated from device kinds | **yes** | no | Phase 7 (D-59) |
| `Hardware` (target table + sharing policy) | no | — | **yes** | no | Phase 7 (D-57) |
| `Assignment` | no | IDE result | **yes** (derived artifact) | no | Phase 7 (D-60) |
| exclusivity | no | — | **yes** | no | Counterexample D |
| shareability (per capability) | no | — | **yes** | no | Counterexample E |
| grouped peripheral requirements (`UnitRel.same`) | no | — | **yes** | no | `grouped_peripheral_same_unit` |
| secondary-resource footprints (units: timers) | no | — | **yes** | no | `timers_matter` |
| fixed assignment (manual pin) | no | designer choice | **yes** | no | Counterexample F |
| generic CSP constraints (unary + binary) | no | — | **yes** | no | `solve_complete` |
| SMT integration | no | — | — | not needed for tested scope | D-60 |
| numeric electrical constraints | no | — | later validation | — | D-63 |
| unsat-core explanation | no | IDE | first dead end kept; minimal core pending | — | `diagnose` |
| physical limits (range, torque, thermal, travel, PWM values, bus, deadlines) | no | — | later validation | — | D-63 |
| range / latency / rate / feasibility obligations | no | — | yes | — | Phase 7 (expected: V) |
| elaboration Surface → Core; reusable stateful components by instantiation | — | — | — | — | Phase 8 |
| five-phase tick (Sample/Activate/Evaluate/Resolve/Commit) | ? | — | — | ? | Phase 8 — to be derived, not copied |
| `BehaviorInterface` / `Port` | no | yes (composition metadata) | checked by `ComposeWF` | no | Phase 8a (D-65): a port is a template declaration's public interface |
| `BehaviorComponent` + `Realizes` | no | yes (template) | — | no | Phase 8a (D-64): a design over local ids + a predicate over existing judgments |
| instantiation (`Ren.inst`, `fresh`/`decode`) | no — elaboration | yes | — | no | Phase 8a (D-66): Theorem A; encoding is a device |
| internal vs global concepts/sinks | no | yes (flags on the template) | — | no | Counterexample 3 |
| `Binding` (port / const / via `sync`) | no | yes → Phase-1 `realize` step | `BindingWF` | no | Phase 8a (D-67): `binding_satisfies` |
| `BehaviorSystem` + `flatten` | no | yes | — | no | output is an ordinary `Design` (`flatten_WF`) |
| `ComposeWF` | no | — | **yes** (structural) | no | interfaces only; `dstNodup`, `ExternalSingleDriver` |
| `InstAcyclic` | no | — | **yes** | no | sufficient for existing `Causal` (`flatten_causal`); Counterexample 1 |
| clock parameters | no — substitution | yes | — | no | `Clocked.rename` for any κ |
| `Evidence.Equivariant`, `Evidence.PortSound` | constraints imposed on V | — | yes | no | D-71 |
| hierarchical tree constructor | no | no | — | **yes** | D-72: packaging (`toComponent`) suffices |
| component-level typing judgment | no | no | — | **yes** | D-64 |
| modular semantics `instΔ`/`Consistent` | no — derived | — | — | — | Theorem J: agrees with flattened `Ev` on the wiring fragment |
| `BehaviorGroup` / membership / `GroupedDesign` | no | authoring metadata | — | no | Phase 8b (D-74): Theorems A–G by `rfl` |
| group / ungroup / move / merge / split | no | semantic no-op | — | no | Phase 8b (D-75) |
| collapse / expand | no | UI/layout only | — | — | not modelled |
| aggregate input/output sockets | no | derived projection (`externalInputs`/`externalOutputs`) | — | **yes** as declarations | Phase 8b (D-76); Counterexample 6 |
| nested groups | no | relation on the flat list | — | **yes** as a recursive type | D-82 |
| boundary inference (`crossIn`/`crossOut`/`privateMembers`/`clocksOf`) | no | analysis/elaboration | — | no | Phase 8b (D-77); Counterexamples 1–3 |
| `restrict` / `template` / `Extract` | no | surface elaboration → Phase-8a system | — | no | Phase 8b (D-78); `flat_WF`, `orig_iff_flat` |
| `Evidence.InterfaceLocal` | constraint imposed on V | — | yes | no | D-80 |
| tuple-return / `MultiOutputMapping` | no | no | — | **yes** | Counterexample 5 |
| physical sink as semantic port | no | no | — | **yes** | Counterexample 4; `drive_stays_with_member` |

## Feature entries (accepted constructs)

### FEATURE: stable declaration identity (`DeclId`)
- KERNEL STATUS: keep — as an ordinary declaration key
- SURFACE STATUS: shown as a renameable display name; may be presented as a "hole" while unresolved
- VALIDATION STATUS: n/a
- WHY IT EXISTS: `declRef` must resolve to the same declaration before and after refinement/realization
- WHAT BREAKS WITHOUT IT: probe 3a — dangling reference; probe 3b — realization invisible to clients, design never executable
- CAN IT BE DESUGARED: no; but it is *equivalent* to an ordinary declaration name (REPORT §1.5) — this is not a novel abstraction
- OBSERVABLE DIFFERENCE: `A` becomes ill-typed, or never unfolds
- LEAN THEOREM / COUNTEREXAMPLE: `EnvRefines_update`; `probe3a_breaks_typing`, `probe3b_stuck`

### FEATURE: frozen expected type
- KERNEL STATUS: keep
- SURFACE STATUS: shown in the signature
- VALIDATION STATUS: n/a
- WHY IT EXISTS: clients are typed against it, and only against it
- WHAT BREAKS WITHOUT IT: every client mentioning the declaration
- CAN IT BE DESUGARED: no
- OBSERVABLE DIFFERENCE: type error at unchanged client
- LEAN THEOREM / COUNTEREXAMPLE: `HasType.mono_env`; `probe4_breaks_typing`, `probe4_id_alone_insufficient`, `retype_kills_ref`

### FEATURE: monotone public commitments in the interface
- KERNEL STATUS: keep as interface data (discharge is V)
- SURFACE STATUS: "declared properties" on the block
- VALIDATION STATUS: discharge mechanisms live here; each commitment induces an obligation
- WHY IT EXISTS: compositional discharge of client commitments rests on dependency commitments
- WHAT BREAKS WITHOUT IT: probe 5 — client commitment silently invalidated; typing does not notice
- CAN IT BE DESUGARED: no (it is data, not behaviour)
- OBSERVABLE DIFFERENCE: none in types; `GlobalWF` fails
- LEAN THEOREM / COUNTEREXAMPLE: `DeclRefines.commitments_subset`; `probe5_typing_kept` + `probe5_breaks_commitment`

### FEATURE: evidence stability (`Evidence.Monotone`)
- KERNEL STATUS: constraint the kernel imposes on V for refinement-surviving evidence
- SURFACE STATUS: invisible
- VALIDATION STATUS: every discharge mechanism whose evidence is meant to survive refinement must satisfy it; environment-sensitive evidence is a pending separate category
- WHY IT EXISTS: without it valid refinements destroy existing evidence
- WHAT BREAKS WITHOUT IT: `local_refinement_preserves_global_wf`
- CAN IT BE DESUGARED: no
- OBSERVABLE DIFFERENCE: a realization of `B` makes `A` ill-formed
- LEAN THEOREM / COUNTEREXAMPLE: `local_refinement_preserves_global_wf`; `probe6_breaks`, `badEv_not_mono`; positive instance `compEv_mono`

### FEATURE: refinement vs edit
- KERNEL STATUS: refinement formalized (`DeclLeq`, `DeclRefines`, `EnvRefines`); edit documented only
- SURFACE STATUS: both appear as "editing the block"; the tool must distinguish them
- VALIDATION STATUS: edits require rechecking transitive dependents
- WHY IT EXISTS: preservation theorems hold for refinement only
- WHAT BREAKS WITHOUT IT: probes 3–5 would be misdescribed as refinement failures instead of edits
- CAN IT BE DESUGARED: no
- OBSERVABLE DIFFERENCE: which operations may skip revalidation
- LEAN THEOREM / COUNTEREXAMPLE: `local_refinement_preserves_global_typing/wf` (refinement); `probe3a/4/5` (edits)

### FEATURE: realization-dependency acyclicity
- KERNEL STATUS: keep (well-formedness beyond typing); to be refined when delay exists
- SURFACE STATUS: diagnostic
- VALIDATION STATUS: no
- WHY IT EXISTS: the pure fragment has no fixpoints; unfolding is undefined on cycles
- WHAT BREAKS WITHOUT IT: well-typed designs with no semantics
- CAN IT BE DESUGARED: no
- OBSERVABLE DIFFERENCE: `S := S` types but never unfolds
- LEAN THEOREM / COUNTEREXAMPLE: `Unfolds.not_of_cyclic`, `Unfolds.exists_of_acyclic`; `self_no_unfolding`, `mut_no_unfolding`

### FEATURE: nominal semantic type (`Ty.sem SemanticId`)
- KERNEL STATUS: keep (one constructor; no intro/elim in the pure fragment)
- SURFACE STATUS: shown by display name; `decl Tilt` allocates the id
- VALIDATION STATUS: n/a — semantic mismatch is a type error, not an obligation
- WHY IT EXISTS: representation-compatible concepts must be non-interchangeable by default
- WHAT BREAKS WITHOUT IT: Counterexample A — the baseline accepts `motorTarget := tiltSensor`
- CAN IT BE DESUGARED: not by any tested alternative (B-weak and C-unstratified fail formally; B-strong tested formulation is redundant; broader analyses not ruled out)
- OBSERVABLE DIFFERENCE: the direct wire is rejected; the declared semantic mapping is accepted
- LEAN THEOREM / COUNTEREXAMPLE: `semantic_identity_mismatch_rejected`, `explicit_semantic_mapping_accepted`, `HasType.erase`, `baseline_is_erased_modelA`

### FEATURE: internal semantic identity (`SemanticId`)
- KERNEL STATUS: keep
- SURFACE STATUS: never shown; the name table maps it to a display name
- VALIDATION STATUS: n/a
- WHY IT EXISTS: identity must survive renaming and must not be a declaration id
- WHAT BREAKS WITHOUT IT: Counterexample C (rename destroys clients); Model C as ordinary `DesignDecl` (concept usable as a value)
- CAN IT BE DESUGARED: no
- OBSERVABLE DIFFERENCE: renaming `Tilt → DeviceTilt` changes nothing in the kernel
- LEAN THEOREM / COUNTEREXAMPLE: `semantic_rename_preserves_identity`, `rename_under_name_identity_breaks_client`, `conceptC_usable_as_value`

### FEATURE: representation-binding witness (`ConceptEnv`, `Θ s = some R`)
- KERNEL STATUS: keep (write-once, sem-free)
- SURFACE STATUS: `decl Tilt represented by Q[Angle]`
- VALIDATION STATUS: n/a
- WHY IT EXISTS: `rep`/`mk` need to know the representation; binding is deferred like a realization
- WHAT BREAKS WITHOUT IT: no formula can touch a semantic value
- CAN IT BE DESUGARED: no; and it must not be a `DeclInterface` field or a `Ty.sem` index (D-29, D-33)
- OBSERVABLE DIFFERENCE: unbound concepts still wire; `rep`/`mk` become typable once bound; rebinding breaks realizations
- LEAN THEOREM / COUNTEREXAMPLE: `HasType.mono_concept`, `GlobalWF.of_conceptRefines`, `unbound_concept_still_wires`, `representation_change_is_edit_not_refinement`, `binding_to_semantic_type_is_hidden_mapping`

### FEATURE: `rep` (observation, unrestricted)
- KERNEL STATUS: keep
- SURFACE STATUS: implicit inside formulas
- VALIDATION STATUS: n/a
- WHY IT EXISTS: formulas compute on representations
- WHAT BREAKS WITHOUT IT: no formula can read a semantic input
- CAN IT BE DESUGARED: no
- OBSERVABLE DIFFERENCE: none for isolation — observation never creates identity
- LEAN THEOREM / COUNTEREXAMPLE: `observation_is_available`, `provenance` (safe under `.none`)

### FEATURE: `mk` under `Grant.of` signature (construction, licensed)
- KERNEL STATUS: keep
- SURFACE STATUS: implicit — the elaborator inserts `mk` for a mapping whose codomain is semantic (paper §7.2)
- VALIDATION STATUS: n/a
- WHY IT EXISTS: the only way a formula can produce a semantic output
- WHAT BREAKS WITHOUT IT: Model B — mappings unrealizable by formula
- WHAT BREAKS WITHOUT THE GRANT: Model A — implicit cross-identity paths
- CAN IT BE DESUGARED: no
- OBSERVABLE DIFFERENCE: `mkMotor (repTilt x)` is ill-typed in client code and inside `Tilt → Brightness`; legal only inside a declaration announcing `MotorAngle`
- LEAN THEOREM / COUNTEREXAMPLE: `representation_binding_does_not_enable_hidden_semantic_mapping`, `explicit_semantic_mapping_can_use_representation_formula`, `hidden_crossing_rejected_under_grant`, `HasType.constructs_granted`, `grant_provenance`

### FEATURE: quantity type `q d` with algebra in `Prim.ty`
- KERNEL STATUS: keep
- SURFACE STATUS: shown with units
- VALIDATION STATUS: n/a
- WHY IT EXISTS: dimensionally invalid computation must be rejected
- WHAT BREAKS WITHOUT IT: Counterexample B — `length + time` accepted
- CAN IT BE DESUGARED: not by any tested alternative (erasure is the baseline; metadata/validation argued redundant, not ruled out)
- OBSERVABLE DIFFERENCE: `length + time` rejected; `length / time` typed at the computed dimension
- LEAN THEOREM / COUNTEREXAMPLE: `dimension_mismatch_rejected`, `dimensional_addition_requires_equal_dimensions`, `HasType.eraseDim`, `counterexampleB_baseline_accepts_length_plus_time`

### FEATURE: units as elaboration
- KERNEL STATUS: no
- SURFACE STATUS: keep — literal `n u` elaborates to `prim (lit u.dim (n·u.scale))`
- VALIDATION STATUS: n/a
- WHY IT EXISTS: designers write `5 cm`
- WHAT BREAKS WITHOUT IT: nothing in the kernel
- CAN IT BE DESUGARED: yes — that is the point
- OBSERVABLE DIFFERENCE: a unit change changes the value, never the type
- LEAN THEOREM / COUNTEREXAMPLE: `unit_scaling_preserves_dimension`, `unit_change_is_value_not_type`

### FEATURE: `delay init e`
- KERNEL STATUS: keep — the only temporal primitive; data-typed; empty context
- SURFACE STATUS: appears as `previous`, `hold`, `count`, … (all derived)
- VALIDATION STATUS: n/a
- WHY IT EXISTS: the only way a tick can see an earlier tick
- WHAT BREAKS WITHOUT IT: no temporal behaviour at all; with unrestricted form (under lambda / at arrow type): totality proof fails (closures across ticks)
- CAN IT BE DESUGARED: no
- OBSERVABLE DIFFERENCE: `delayed_loop_runs` vs `algebraic_loop_no_value`
- LEAN THEOREM / COUNTEREXAMPLE: `HasType.delay`, `Ev.delayZero`/`delaySucc`, `fundamental`, `temporal_change_is_edit`

### FEATURE: tick-indexed evaluation `Ev`
- KERNEL STATUS: keep — the semantics of the single-domain fragment
- SURFACE STATUS: invisible
- VALIDATION STATUS: n/a
- WHY IT EXISTS: `Unfolds` has no meaning for stateful designs
- WHAT BREAKS WITHOUT IT: no notion of tick-to-tick behaviour, causality, or determinism
- CAN IT BE DESUGARED: no; `Unfolds` is its optimization on wiring designs (`unfolds_preserves_eval`)
- OBSERVABLE DIFFERENCE: the traces
- LEAN THEOREM / COUNTEREXAMPLE: `Ev.det`, `reactive_total`, `Ev.not_of_strictCyclic`, `Ev.tag_provenance`

### FEATURE: causality (`Causal` on `InstDependsOn`)
- KERNEL STATUS: keep (well-formedness beyond typing)
- SURFACE STATUS: diagnostic naming the instantaneous cycle
- VALIDATION STATUS: no
- WHY IT EXISTS: execution exists exactly on causal designs
- WHAT BREAKS WITHOUT IT: well-typed designs with no value (`Δalg`, `Δmixed`)
- CAN IT BE DESUGARED: no
- OBSERVABLE DIFFERENCE: which cycles run
- LEAN THEOREM / COUNTEREXAMPLE: `reactive_total`, `Ev.not_of_strictCyclic`, `Causal_iff_acyclic_of_delayFree`; gap `lamloop_evaluates`

### FEATURE: explicit initialization
- KERNEL STATUS: keep (part of `delay`)
- SURFACE STATUS: shown
- VALIDATION STATUS: no
- WHY IT EXISTS: a unique first tick
- WHAT BREAKS WITHOUT IT: `first_tick_undefined_without_init`, `first_tick_nondeterministic_without_init`
- CAN IT BE DESUGARED: `previous : τ → opt τ` is the reverse desugaring, not a replacement
- OBSERVABLE DIFFERENCE: tick 0
- LEAN THEOREM / COUNTEREXAMPLE: as above

### FEATURE: nominal clock identity (`ClockId`, `ClockEnv`)
- KERNEL STATUS: keep (interface-level, frozen; `none` = agnostic)
- SURFACE STATUS: `domain d` declarations; shown on ports
- VALIDATION STATUS: rates attach here as metadata
- WHY IT EXISTS: without it the cross-rate wire is ambiguous (A) and equal rates cannot distinguish domains (B)
- WHAT BREAKS WITHOUT IT: `unpolicied_wire_ambiguous`, `equal_rate_not_same_domain`
- CAN IT BE DESUGARED: no; inference would break signature-first (D-44)
- OBSERVABLE DIFFERENCE: which references are legal; what `sync` reads (`phase_matters`)
- LEAN THEOREM / COUNTEREXAMPLE: `cross_domain_direct_wire_rejected`, `clock_change_invalidates_clients`

### FEATURE: domain judgment `Clocked`
- KERNEL STATUS: keep (separate from typing; `Ty`, `tyView` unchanged)
- SURFACE STATUS: diagnostic naming the two domains
- VALIDATION STATUS: n/a
- WHY IT EXISTS: typing is blind to domains (`both_well_typed`); something static must reject the direct wire
- WHAT BREAKS WITHOUT IT: ambiguous semantics accepted
- CAN IT BE DESUGARED: not into typing without clocked types (rejected)
- OBSERVABLE DIFFERENCE: the direct wire vs `sync`
- LEAN THEOREM / COUNTEREXAMPLE: `cross_domain_direct_wire_rejected`, `explicit_transport_accepted`

### FEATURE: `sync src init e`
- KERNEL STATUS: keep — the single temporal read; `delay` is its own-domain instance
- SURFACE STATUS: `hold`, `latest`, `sample`, `delay`, `previous` …
- VALIDATION STATUS: capacity of derived buffers; value age
- WHY IT EXISTS: the only way a domain sees another; strictly-before keeps scheduler order out of the semantics
- WHAT BREAKS WITHOUT IT: no cross-domain flow; with the same-tick alternative: `scheduling_order_observable`
- CAN IT BE DESUGARED: no (it subsumes `delay`, not the reverse)
- OBSERVABLE DIFFERENCE: `transport_trace`, `delay_is_domain_relative`
- LEAN THEOREM / COUNTEREXAMPLE: `delay_is_sync_own`, `single_domain_embedding`, `MEv.det`, `multi_domain_total`, `sync_preserves_semantic_identity`

### FEATURE: physical sink identity (`OutputId`, `OutputEnv`)
- KERNEL STATUS: keep (resource identity; accepted type + clock declared)
- SURFACE STATUS: device names
- VALIDATION STATUS: physical limits attach here (Phase 7)
- WHY IT EXISTS: same type does not identify a sink
- WHAT BREAKS WITHOUT IT: `type_keyed_binding_collides`
- CAN IT BE DESUGARED: no; `SemanticId`/`DeclId` conflate concept/relationship with resource
- OBSERVABLE DIFFERENCE: which device moves
- LEAN THEOREM / COUNTEREXAMPLE: D, `two_drivers_two_outputs`

### FEATURE: drive edge (`DriveEnv β`, `DriveWF`)
- KERNEL STATUS: keep (write-once per declaration; type and clock equality)
- SURFACE STATUS: the wire into the actuator
- VALIDATION STATUS: n/a
- WHY IT EXISTS: values do not move hardware; the edge is the only physical effect
- WHAT BREAKS WITHOUT IT: no physical semantics; with coercing/synchronizing bindings: E, G
- CAN IT BE DESUGARED: no
- OBSERVABLE DIFFERENCE: `PhysicalOutput`
- LEAN THEOREM / COUNTEREXAMPLE: `output_binding_preserves_semantic_identity_and_dimension`, `output_binding_respects_clock_domain`, `first_output_binding_is_monotone`

### FEATURE: single-driver / completeness
- KERNEL STATUS: keep (global well-formedness; completeness at the executable level)
- SURFACE STATUS: diagnostic naming the two drivers
- VALIDATION STATUS: no
- WHY IT EXISTS: without it the physical output is not a function of the tick
- WHAT BREAKS WITHOUT IT: `two_drivers_two_outputs`; with hidden arbitration: C
- CAN IT BE DESUGARED: not into typing (`two_direct_drivers_locally_fine`)
- OBSERVABLE DIFFERENCE: determinism of the physical output
- LEAN THEOREM / COUNTEREXAMPLE: `multiple_direct_drivers_rejected`, `single_driver_output_deterministic`, `executable_design_requires_complete_outputs`

### FEATURE: hardware target table (`Hardware`, `Resource`)
- LAYER: validation (never kernel)
- WHY IT EXISTS: feasibility is a property of Design × Target
- WHAT BREAKS WITHOUT IT: nothing in the semantics; deployment cannot be checked
- CAN IT BE DESUGARED: no; and it must not enter `Ty` (D-57)
- VALIDATION DIFFERENCE: SAT/UNSAT per board (`seven_pwm_unsat_on_nano` vs `seven_pwm_sat_on_big`)
- LEAN THEOREM / COUNTEREXAMPLE: A, B, `hardware_extension_preserves_satisfiability`

### FEATURE: requirements with fixed resource and unit relation
- LAYER: validation; generated from Phase-6 sinks through device kinds
- WHY IT EXISTS: what a design needs, independent of any board
- WHAT BREAKS WITHOUT UNITS: `timers_matter`; WITHOUT FIXED: manual routing impossible (F)
- CAN IT BE DESUGARED: the pipeline `OutputId → DeviceKind → Requirements` is the desugaring
- VALIDATION DIFFERENCE: C, D, E, H
- LEAN THEOREM / COUNTEREXAMPLE: as named

### FEATURE: list data (`Ty.list`, six operators)
- LAYER: kernel (data type + registered operators)
- WHY IT EXISTS: a lossless cross-domain window is unbounded sequence data (`bounded_summary_not_lossless`)
- WHAT BREAKS WITHOUT IT: the Phase-5 buffer cannot be written in the object language; only lossy transport (`opt_loses_multiplicity_under_sync`)
- CAN IT BE DESUGARED: no; every summary of bounded size is lossy
- VALIDATION DIFFERENCE: none — no typing, evaluation, or domain rule added (`list_clock_conservative`)
- LEAN THEOREM / COUNTEREXAMPLE: `list_data`, `reactive_total_with_lists`, `multi_domain_total_with_lists`, `latest_not_lossless`, `count_not_lossless`

### FEATURE: buffered transport (`BDL.Buffer.decls`)
- LAYER: surface elaboration (five declarations over `delay`/`sync`/list operators)
- WHY IT EXISTS: order and multiplicity of cross-domain events are observable
- WHAT BREAKS WITHOUT IT: nothing in the kernel; the designer writes the five declarations by hand
- CAN IT BE DESUGARED: it *is* the desugaring; `buffer_window_correspondence` proves it equals the Phase-5 window
- VALIDATION DIFFERENCE: capacity (`CapacitySufficient`); overflow is explicit and only reject-deployment preserves semantics
- LEAN THEOREM / COUNTEREXAMPLE: `buffer_elaboration_well_typed`, `buffer_elaboration_well_clocked`, `buffer_window_correspondence`, `buffer_lossless`, `sufficient_capacity_preserves`, `negE`

### FEATURE: products (`prod`, `pair`, `fst`, `snd`)
- LAYER: kernel (value composition only)
- WHY IT EXISTS: paired state and structured intermediate values must be data
- WHAT BREAKS WITHOUT IT: a function encoding is not data and cannot be delayed or transported (`arrow_not_delayable`)
- CAN IT BE DESUGARED: no (rank-2 for first-class Church pairs: `church_fst_rank`)
- VALIDATION DIFFERENCE: none
- LEAN THEOREM / COUNTEREXAMPLE: `prod_data`, `pair_state_delayable`, `pair_projections_keep_concepts`

### FEATURE: the list recursor `fold`
- LAYER: kernel (term former)
- WHY IT EXISTS: the only eliminator for lists (and, through `toList`, options) in a language without recursion
- WHAT BREAKS WITHOUT IT: `map`, `any`, `all`, `contains`, `filter`, `zip` each become primitives, or are unwritable
- CAN IT BE DESUGARED: no; everything else is desugared *to* it
- VALIDATION DIFFERENCE: none (a bounded window is still validation, 9a)
- LEAN THEOREM / COUNTEREXAMPLE: `fold_total`, `any_spec`, `all_spec`, `map_spec`, `forall_in_list`

### FEATURE: rank-1 definitional polymorphism
- LAYER: surface/elaborator (families + matching)
- WHY IT EXISTS: one definition of `min`/`map`/`any` for all data types
- WHAT BREAKS WITHOUT IT: per-type duplication in the library (Model B)
- CAN IT BE DESUGARED: it *is* the desugaring; the kernel sees monomorphic instances (`instances_are_monomorphic`)
- VALIDATION DIFFERENCE: none
- LEAN THEOREM / COUNTEREXAMPLE: `matchTy_sound`, `matchTy_complete`, `generic_preserves_identity`, `lib_expansion`

### FEATURE: capability vocabulary {Data, Eq, Ord} (Phase 9c)
- LAYER: surface (scheme variables); kernel evidence only for Data (the `eq` proof field, the `delay`/`sync` premise)
- WHY IT EXISTS: ordering is not a property of data; equality is
- WHAT BREAKS WITHOUT THE SPLIT: `mode1 < mode2`, `None < Some x`, lexicographic pairs/lists become language capabilities
- CAN IT BE DESUGARED: Ord on a concept desugars to `lt d` on `rep`; Eq is Data; no class machinery
- VALIDATION DIFFERENCE: none
- LEAN THEOREM / COUNTEREXAMPLE: `Cap.eq_iff_data`, `Cap.ord_data`, `Cap.ord_not_data_converse`, `lt_rejected`, `eq_accepted`, `min_mode_rejected`, `minBy_recovers_min`

### FEATURE: exhaustive solver with soundness and completeness
- LAYER: validation
- WHY IT EXISTS: decidable feasibility with a concrete mapping or a conflict
- WHAT BREAKS WITHOUT COMPLETENESS: an UNSAT answer would not be a proof of infeasibility
- CAN IT BE DESUGARED: n/a
- VALIDATION DIFFERENCE: `motor_control_assignment`, `seven_pwm_explanation`
- LEAN THEOREM / COUNTEREXAMPLE: `solve_sound`, `solve_complete`, `satisfiable_iff_solve`
