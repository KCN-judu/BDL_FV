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
| general edit relation / invalidation tracking | ? | — | ? | — | pending; needed once edits must be tracked (Phase 11 or earlier if Phase 2 forces it) |
| `Evidence` / `DischargedBy` | no | no | yes | no | never decided by the kernel |
| `Evidence.Monotone` (stability of refinement-surviving evidence) | constraint imposed by kernel on V | — | yes | no | probe 6 |
| environment-sensitive / recheck-required evidence | — | — | ? | — | pending (Phase 11); documented in `Satisfaction.lean` |
| realization-dependency acyclicity | yes (well-formedness) | — | no | no | unfolding undefined on cycles (`Unfolds.not_of_cyclic`); revisit with delay (Phase 5/8) |
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
| `Event` vs `Signal (Option τ)` | ? | ? | no | ? | Phase 4 |
| `delay`/`previous`/`hold`/`count`/`since` | ? | ? | — | ? | Phase 5 |
| `for`/`after`/`while`/`until`/`once`/`every` | ? | likely | — | ? | Phase 5 |
| clock domains (none / inferred / nominal) | ? | ? | ? | ? | Phase 6 |
| cross-domain `hold`, event sync policies | ? | ? | ? | ? | Phase 7 |
| causality / delay boundaries | ? | — | — | — | Phase 8 |
| `StateHandler` | ? | likely | no | ? | Phase 9 |
| effect rows | ? | ? | ? | ? | Phase 10 |
| actuator arbitration | ? | ? | ? | — | Phase 10 |
| range / latency / rate / feasibility obligations | no | — | yes | — | Phase 11 (expected: V) |
| elaboration Surface → Core | — | — | — | — | Phase 12 |
| five-phase tick (Sample/Activate/Evaluate/Resolve/Commit) | ? | — | — | ? | Phase 13 |

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
