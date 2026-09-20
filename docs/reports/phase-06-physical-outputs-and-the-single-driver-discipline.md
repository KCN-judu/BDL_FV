---
kind: report
phase: 6
area: core
date: 2026-09-15
status: current
---

# Phase 6 — Physical outputs and the single-driver discipline

## 6.1 The model

A declaration computes a value; it does not move hardware. Physical effect
happens only through an explicit **drive edge** from a declaration to a
**physical sink**. The smallest model that survived:

- `OutputId` — nominal resource identity of a sink;
- `OutputEnv Ω : OutputId → Option OutputSpec`,
  `OutputSpec = (accepts : Ty, clock : ClockId)`;
- `DriveEnv β : DeclId → Option OutputId` — the drive edges, a per-declaration
  projection like `Κ`, write-once;
- `DriveWF Ω Κ Δ β` — a drive edge is well formed iff the driver's type
  **equals** the sink's accepted type and the driver's clock is the sink's;
- `SingleDriver β` — at most one driver per sink;
- `CompleteOutputs β req` — every required sink is driven.

Nothing was added to `Ty`, `HasType`, `Clocked`, `MEv`, or the grant discipline.
No effect rows, no action values, no arbitration.

## 6.2 Results (claim strength in brackets)

| Result                                                                                                                                                                                                                                               | Lean                                                                              | Strength                                                  |
| ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------- | --------------------------------------------------------- |
| **Counterexample A / `multiple_direct_drivers_rejected`**: two drivers of one sink — globally well typed, well-clocked, causal, each edge individually well formed — fail only `SingleDriver`. Local typing is insufficient; the invariant is global | `two_direct_drivers_locally_fine`, `multiple_direct_drivers_rejected`             | formally proved                                           |
| semantically, two drivers make the output _not a function_: `base = 10` and `corr = 40` are both physical outputs at the same tick                                                                                                                   | `two_drivers_two_outputs`                                                         | formally proved                                           |
| **`single_driver_completed_design_deterministic`**: with one driver the physical output is a partial function of the tick                                                                                                                            | `single_driver_output_deterministic`                                              | formally proved                                           |
| **Counterexample B / `explicit_target_composition_accepted`**: `base + corr → final → motor` passes everything; the contributors are dependencies, not drivers                                                                                       | `explicit_target_composition_accepted`, `contributors_are_not_drivers`            | formally proved                                           |
| **Counterexample C**: first/last/max over the same value graph give three physical outputs — arbitration policy is design information                                                                                                                | `hidden_arbitration_observable`                                                   | formally rejected by counterexample (for hidden policies) |
| explicit priority as an ordinary conditional in a single driver; blend and max likewise                                                                                                                                                              | `explicit_priority_single_driver`, `blend_and_max_are_ordinary_targets`           | formally proved (typing + execution)                      |
| **Counterexample D / `output_identity_distinct_from_semantic_identity`**: two servos accept the same type; a type-keyed binding collides, nominal `OutputId` does not                                                                                | `type_keyed_binding_collides`                                                     | formally proved                                           |
| **Counterexample E / `output_binding_preserves_semantic_identity`, `…_dimension`**: `Tilt`, bare `q Angle`, `q Length` cannot drive the `MotorAngle` sink; only a declaration already typed `MotorAngle` (constructed under its own grant) can       | `output_binding_preserves_semantic_identity_and_dimension`                        | formally proved                                           |
| a sink that accepts a _representation_ is legitimate and needs an explicit `rep` declaration first: semantic target vs hardware representation stays visible                                                                                         | `representation_sink_needs_explicit_rep`                                          | formally proved                                           |
| **Counterexample G / `output_binding_respects_clock_domain`**: a fast driver cannot drive a slow sink; a slow driver reading a fast value must `sync` it first; the binding never synchronizes                                                       | `output_binding_respects_clock_domain`                                            | formally proved                                           |
| **`first_output_binding_is_monotone`**: binding an unbound declaration to an undriven sink is a refinement (preserves `SingleDriver`)                                                                                                                | `first_output_binding_is_monotone`                                                | formally proved                                           |
| a second binding to a driven sink is _invalid_                                                                                                                                                                                                       | `second_binding_invalid`                                                          | formally proved                                           |
| **Counterexample F**: retargeting a sink's accepted type, renaming the sink, or detaching the edge invalidates an unchanged design                                                                                                                   | `rebinding_invalidates_design`                                                    | formally proved                                           |
| **`partial_design_allows_unbound_output`** / **`executable_design_requires_complete_outputs`**                                                                                                                                                       | as named                                                                          | formally proved                                           |
| **`effect_rows_add_no_new_rejection`**: single-driver is _exactly_ disjointness of direct effect rows; propagated rows flag a valid design (a display that reads the driver)                                                                         | `single_driver_iff_direct_rows_disjoint`, `propagated_effect_rows_false_positive` | equivalence by proof; false positive by counterexample    |
| action values relocate the conflict into the collector, which must then be a policy (= C)                                                                                                                                                            | `action_values_relocate_conflict`                                                 | formally proved (toy)                                     |
| StateHandler remainder: event-latched activation with exit-wins, state-local output choice, nested choice — all ordinary declarations with one driver                                                                                                | `statehandler_output_cases`                                                       | formally proved by execution on the tested cases          |

## 6.3 Output identity (§5, §20)

| Candidate                    | Verdict                                                                                                                       |
| ---------------------------- | ----------------------------------------------------------------------------------------------------------------------------- |
| A — by type                  | rejected: `type_keyed_binding_collides` (two servos, one type)                                                                |
| B — `SemanticId`             | rejected: one concept feeds several devices; conflates concept and hardware                                                   |
| C — `DeclId`                 | rejected: two declarations that both mean the steering motor become two "sinks", and Counterexample A cannot even be _stated_ |
| D — nominal `OutputId`       | **kept**: the only one under which both A and D are expressible                                                               |
| E — external deployment only | rejected: completeness and single-driver are design-time acceptance conditions (paper §7.6 "executable")                      |

What `OutputId` names: a logical actuator channel / device command endpoint — a
_resource_. "Desired steering angle" is a value (`MotorAngle`); "the steering
motor" is a sink. The kernel keeps them in different sorts.

## 6.4 Where the binding lives (§7, §26)

Per-declaration projection `β` + a global predicate — the same shape as clocks
(Phase 5) and representations (Phase 3). It participates in _no_ typing rule. It
must be knowable before realization (a sink can be declared and left undriven),
and client validity does not depend on it — only completeness does.
Single-driver joins commitment validity, causality and clock consistency as the
fourth global property beyond STLC typing.

## 6.5 Semantic target vs hardware representation (§14)

The sink's `accepts` is ordinary `Ty`. A sink accepting `MotorAngle` takes a
declaration typed `MotorAngle` — which had to construct it under its own grant.
A sink accepting `q Angle` (a raw servo) needs an explicit `rep`-typed
declaration in between. A device-command concept (`PWMCommand`) would be another
`SemanticId` reached by an explicit mapping. The kernel does not distinguish
these; the deployment declares, and the path is visible either way.

## 6.6 Refinement vs edit (§27)

| Operation                           | Kind                                               | Witness                            |
| ----------------------------------- | -------------------------------------------------- | ---------------------------------- |
| unbound → bound once, sink undriven | refinement                                         | `first_output_binding_is_monotone` |
| bind to an already-driven sink      | **invalid**                                        | `second_binding_invalid`           |
| output A → output B                 | edit (A becomes undriven; completeness may break)  | `rebinding_invalidates_design` (c) |
| detach binding                      | edit                                               | `rebinding_invalidates_design` (c) |
| replace driver                      | edit (write-once per declaration)                  | FVD-0016                           |
| rename `OutputId`                   | edit of `Ω` and `β` together; a stale edge dangles | `rebinding_invalidates_design` (b) |
| retarget a sink's accepted type     | edit                                               | `rebinding_invalidates_design` (a) |

The drive edge has the Phase-0/1 write-once shape (`DriveRefines`), with one
extra global side condition — the sink must be undriven — which is exactly the
single-driver invariant.

## 6.7 Answers to §38

| Question                                    | Answer                                                                                                                                                                                                  |
| ------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 1. What is a physical output?               | A nominal sink `OutputId` with an accepted `Ty` and a `ClockId` (`OutputSpec` in `Ω`).                                                                                                                  |
| 2. Independent nominal identity?            | Yes (Counterexample D; `SemanticId`/`DeclId` conflate).                                                                                                                                                 |
| 3. How is a value bound?                    | A drive edge `β d = some o`, well formed iff types equal and clocks equal.                                                                                                                              |
| 4. Typing, global WF, or deployment?        | Global well-formedness (`DriveWF`, `SingleDriver`); `Ω` is deployment-declared data. Not typing.                                                                                                        |
| 5. Single-driver formally?                  | `∀ d₁ d₂ o, β d₁ = some o → β d₂ = some o → d₁ = d₂`.                                                                                                                                                   |
| 6. Partial designs with unbound outputs?    | Yes (`partial_design_allows_unbound_output`).                                                                                                                                                           |
| 7. Executable condition?                    | `CompleteOutputs β req` on top of `PartialOutputWF` (plus Phases 4–5: causal, well-clocked, realized).                                                                                                  |
| 8. Multiple direct drivers rejected?        | Yes, globally; and semantically the output is not a function without it.                                                                                                                                |
| 9. Multiple contributors still possible?    | Yes — as ordinary computation upstream of one edge (Counterexample B).                                                                                                                                  |
| 10. Effect rows necessary?                  | Not in the tested formulation: direct rows duplicate `β`, propagated rows false-positive.                                                                                                               |
| 11. Runtime arbitration necessary?          | No in the tested architecture: hidden policies are observable (C) and composition is expressible explicitly.                                                                                            |
| 12. Priority/selection?                     | `ite`, `max`, blend, clamp — ordinary declarations of the target type.                                                                                                                                  |
| 13. Preserves semantic identity/provenance? | Yes: the binding is a type equality; the driver's `MotorAngle` came from its own grant (E).                                                                                                             |
| 14. Preserves dimensions?                   | Yes, same mechanism (E).                                                                                                                                                                                |
| 15. Clocks and sync?                        | Driver clock must equal sink clock; synchronization happens explicitly upstream (G).                                                                                                                    |
| 16. Refinement vs edit?                     | §6.6.                                                                                                                                                                                                   |
| 17. StateHandler cases eliminable?          | Event-latched activation with exit-wins, state-local output choice, nested choice with output — tested and elaborated. Not tested: per-handler action _policies_ (they no longer exist as a mechanism). |
| 18. Phase-7 validation?                     | Range/travel/torque/thermal/current limits, PWM/bus compatibility, deadlines, saturation safety, collisions.                                                                                            |

## 6.8 Critical remarks

- The whole phase is one global predicate over a projection. That is the point:
  the paper's "resolve" phase, effect rows, and arbitration policies all
  dissolved once the design principle became _one final driver, all composition
  explicit_. Nothing here is a new PL mechanism; the contribution is negative
  (C, the effect-row toys) and structural (the invariant is global, like the
  three before it).
- `SingleDriver` on `DriveEnv : DeclId → Option OutputId` is not trivially true
  — that is why `β` is keyed by declaration and not by sink. Keying by sink
  would make uniqueness definitional and hide Counterexample A.
- The StateHandler evidence is now three tested behaviours across Phases 4
  and 6. "StateHandler is surface syntax" remains a claim about tested cases;
  nesting with _independent_ clocks and handler-scoped clocks were not tested.

## 6.9 The Phase-6 result (§41)

> The smallest mechanism is: a nominal sink identity with a declared accepted
> type and clock (`Ω`), a write-once drive edge per declaration (`β`), a
> well-formedness condition that is plain type and clock _equality_, and one
> global invariant — at most one driver per sink — with completeness added only
> for executable designs. Every combination of behaviours is an ordinary
> declaration upstream of the single edge; hidden arbitration is observable and
> unnecessary; effect rows and action values either duplicate the edge or
> relocate the conflict.

Among tested designs.
