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
| semantic types `Sem[n,d]` | ? | ? | ? | ? | Phase 2 |
| dimensions `Q[d]` | ? | ? | ? | ? | Phase 3 |
| units | ? | ? | ? | ? | Phase 3 |
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
