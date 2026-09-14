# MINIMALITY — construct-by-construct status

Legend for the table: **K** kernel, **S** surface (desugars), **V**
validation layer, **R** remove.  `?` = pending the named phase.

| Construct | Kernel | Surface | Validation | Remove | Reason |
|---|---|---|---|---|---|
| `HoleId` (persistent identity) | yes | — | — | no | it is a declaration name; needed as the key references resolve against (probe 3) |
| display `name` | no | yes | no | — | renaming is a refactoring over the id (D-14) |
| `DesignHole` = id × spec × realization (one record for unresolved and realized) | yes | — | — | no | environment order needs one entity across states (`EnvRefines_update`) |
| `Spec.expectedType` frozen under refinement | yes | — | — | no | probe 4: retyping breaks every client |
| `Spec.obligations`, monotone, **part of the signature** | yes (as interface data) | — | discharge only | no | probe 5: dropping an obligation silently breaks dependents' commitments |
| `Refines` preorder | yes | — | — | no | `Refines_iff_semantic`: complete for abstract evidence |
| write-once realization | yes | — | — | no | D-07: detaching is non-monotone for evidence |
| re-verification on `strengthen` | yes | — | — | no | Phase 0 Theorem 4 counterexample |
| `holeRef` in terms | yes | — | — | no | the whole of Phase 1 |
| `HoleEnv` + `update` at own id | yes | — | — | no | `EnvRefines_update` |
| typing reads `tyView` only | yes | — | — | no | sufficient (theorem) and necessary (probe 4) for client stability |
| `Evidence` / `DischargedBy` | no | no | yes | no | never decided by the kernel |
| `Evidence.Monotone` (positivity) | constraint imposed by kernel on V | — | yes | no | probe 6 |
| realization-dependency acyclicity | yes (well-formedness) | — | no | no | unfolding undefined on cycles (`Unfolds.not_of_cyclic`); revisit with delay (Phase 5/8) |
| Phase-0 `Artifact` ref list | — | — | — | **yes** | subsumed by `holeRef` (D-13) |
| several candidate definitions, one `active` (§3.2) | ? | likely | — | ? | pending: probably surface over write-once realization; detaching needs re-validation of dependents |
| spec-level references (obligations mentioning holes) | ? | — | ? | — | pending; needed for a full dependency graph |
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

### FEATURE: persistent hole identity (`HoleId`)
- KERNEL STATUS: keep (as a declaration name)
- SURFACE STATUS: shown as a renameable display name
- VALIDATION STATUS: n/a
- WHY IT EXISTS: references (`holeRef`) must resolve to the same entity before and after refinement/realization
- WHAT BREAKS WITHOUT IT: probe 3a — dangling reference; probe 3b — realization invisible to clients, design never executable
- CAN IT BE DESUGARED: no; but it is *equivalent* to an ordinary declaration name (REPORT §1.5)
- OBSERVABLE DIFFERENCE: `A` becomes ill-typed, or never unfolds
- LEAN THEOREM / COUNTEREXAMPLE: `EnvRefines_update`; `probe3a_breaks_typing`, `probe3b_stuck`

### FEATURE: frozen expected type
- KERNEL STATUS: keep
- SURFACE STATUS: shown in the signature
- VALIDATION STATUS: n/a
- WHY IT EXISTS: clients are typed against it
- WHAT BREAKS WITHOUT IT: every client mentioning the hole
- CAN IT BE DESUGARED: no
- OBSERVABLE DIFFERENCE: type error at unchanged client
- LEAN THEOREM / COUNTEREXAMPLE: `HasType.mono_env`; `probe4_breaks_typing`, `probe4_id_alone_insufficient`, `retype_kills_ref`

### FEATURE: monotone obligation set in the signature
- KERNEL STATUS: keep as interface data (discharge is V)
- SURFACE STATUS: "declared properties" on the block
- VALIDATION STATUS: discharge mechanisms live here
- WHY IT EXISTS: compositional discharge of client obligations rests on dependency commitments
- WHAT BREAKS WITHOUT IT: probe 5 — client commitment silently invalidated; typing does not notice
- CAN IT BE DESUGARED: no (it is data, not behaviour)
- OBSERVABLE DIFFERENCE: none in types; `GlobalWF` fails
- LEAN THEOREM / COUNTEREXAMPLE: `HoleRefines.obligations_subset`; `probe5_typing_kept` + `probe5_breaks_commitment`

### FEATURE: evidence positivity (`Evidence.Monotone`)
- KERNEL STATUS: constraint the kernel imposes on V
- SURFACE STATUS: invisible
- VALIDATION STATUS: every discharge mechanism must satisfy it
- WHY IT EXISTS: without it valid refinements destroy existing evidence
- WHAT BREAKS WITHOUT IT: `local_refinement_preserves_global_wf`
- CAN IT BE DESUGARED: no
- OBSERVABLE DIFFERENCE: a realization of `B` makes `A` ill-formed
- LEAN THEOREM / COUNTEREXAMPLE: `local_refinement_preserves_global_wf`; `probe6_breaks`, `badEv_not_mono`; positive instance `compEv_mono`

### FEATURE: realization-dependency acyclicity
- KERNEL STATUS: keep (well-formedness beyond typing); to be refined when delay exists
- SURFACE STATUS: diagnostic
- VALIDATION STATUS: no
- WHY IT EXISTS: the pure fragment has no fixpoints; unfolding is undefined on cycles
- WHAT BREAKS WITHOUT IT: well-typed designs with no semantics
- CAN IT BE DESUGARED: no
- OBSERVABLE DIFFERENCE: `S := S` types but never unfolds
- LEAN THEOREM / COUNTEREXAMPLE: `Unfolds.not_of_cyclic`, `Unfolds.exists_of_acyclic`; `self_no_unfolding`, `mut_no_unfolding`
