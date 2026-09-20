---
kind: report
phase: 7
area: validation
date: 2026-09-15
status: current
---

# Phase 7 — Hardware constraint validation and resource allocation

## 7.1 The model

A **validation layer** (`BDL/Validation/Hardware.lean`), outside the kernel:
nothing in it touches `Ty`, `HasType`, `MEv`, or the drive edges.

| Concept     | Formal object                                                                                                                                                                                                                                                  |
| ----------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| resource    | `Resource = (id : ResourceId, caps : List Capability, units : List (Capability × Nat))` — a pin, with its capabilities and, per capability, the _unit_ backing it (a timer, a peripheral controller)                                                           |
| target      | `Hardware = (resources, shareable : List Capability)` — a finite table plus a capability-specific sharing policy (buses shareable, everything else exclusive)                                                                                                  |
| capability  | `Capability` — a shared vocabulary between board tables and device descriptions; the solver treats it as an opaque decidable type                                                                                                                              |
| requirement | `Requirement = (id : RequirementId, cap, fixed : Option ResourceId, group : Option (Nat × UnitRel))` — one capability need, optionally a manual pin, optionally a _same-unit_ or _distinct-unit_ relation to other requirements                                |
| assignment  | `Assignment = List (Requirement × ResourceId)`                                                                                                                                                                                                                 |
| validity    | `PartialValid H A`: every entry `ReqOK` (capability supported, manual choice respected) and every pair `Compatible` (same resource ⇒ same shareable capability; same group ⇒ units equal / distinct). `ValidFor H R A`: partial-valid and covering exactly `R` |
| feasibility | `HardwareSatisfiable H R := ∃ A, ValidFor H R A`                                                                                                                                                                                                               |

Every constraint is unary or binary, so validity is prefix-closed, so an
exhaustive DFS that prunes on unary and pairwise-with-prefix checks is complete
as well as sound.

## 7.2 Results (claim strength in brackets)

| Result                                                                                                                                                                                                                                            | Lean                                                             | Strength                                                          |
| ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------- | ----------------------------------------------------------------- |
| **`solve_sound`**, **`solve_complete`**, hence feasibility of a finite instance is _decidable_ (`satisfiable_iff_solve`, `Decidable` instance)                                                                                                    | as named                                                         | formally proved                                                   |
| `valid_assignment_implies_capabilities_satisfied`, `partial_assignment_accepted` (prefix of a valid assignment), `complete_assignment_covers_requirements`                                                                                        | as named                                                         | formally proved                                                   |
| **`hardware_extension_preserves_satisfiability`**: `H₁.Extends H₂` (same resources with ⊇ capabilities, same units, ⊇ sharing) preserves every valid assignment; `nano.Extends big`                                                               | `hardware_extension_preserves_validity`, `nano_extends_big`      | formally proved                                                   |
| **Motor-control example** (four H-bridge channels + I2C IMU): SAT on the Nano, with the produced mapping `M1 → D3/D0, M2 → D5/D1, M3 → D6/D2, M4 → D9/D4, IMU → A4/A5`                                                                            | `motor_control_sat_on_nano`, `motor_control_assignment`          | formally proved by execution                                      |
| **Counterexample A / `semantic_validity_does_not_imply_hardware_satisfiable`**: seven independent PWM actuators pass `GlobalWF`, `WellClocked`, `Causal`, `DriveWF`, `SingleDriver`, `CompleteOutputs` — and are UNSAT on the Nano (six PWM pins) | `seven_pwm_design_semantically_valid`, `seven_pwm_unsat_on_nano` | formally proved                                                   |
| **Counterexample B / `hardware_satisfiability_is_target_relative`, `board_swap_preserves_design_semantics`**: the same `reqs7` is SAT on the larger board; the solver's type never mentions `Δ`                                                   | `seven_pwm_sat_on_big`                                           | formally proved                                                   |
| **Counterexample C**: two interrupt lines + six PWM lines — every capability _count_ is met (2 = 2, 6 = 6) and D3 is needed twice                                                                                                                 | `capability_counts_suffice`, `multifunction_overlap_unsat`       | formally proved                                                   |
| **Counterexample D / `exclusive_resources_not_double_allocated`**: two PWM requirements pinned to D3                                                                                                                                              | `exclusive_cannot_share`                                         | formally proved                                                   |
| **Counterexample E / `shared_bus_allocation_accepted`**: two I2C sensors both on A4/A5 — allocation is not `allDifferent`                                                                                                                         | `shared_bus_allocation_accepted`                                 | formally proved                                                   |
| **Counterexample F / `fixed_assignment_respected`**: encoder + PWM is SAT; pinning the PWM to D3 by hand makes it UNSAT; a consistent manual choice is honoured                                                                                   | `fixed_pin_turns_unsat`, `fixed_assignment_respected`            | formally proved                                                   |
| **Counterexample G**: removing D3 invalidates the motor assignment and makes the encoder UNSAT                                                                                                                                                    | `resource_removal_invalidates`                                   | formally proved                                                   |
| **Counterexample H**: strengthening D4's line from DigitalOut to PWM invalidates it                                                                                                                                                               | `requirement_strengthening_invalidates`                          | formally proved                                                   |
| **timers**: four PWM lines on independent timers — six PWM pins but three timers — UNSAT; SAT without the independence constraint; SAT on the larger board                                                                                        | `timers_matter`                                                  | formally proved                                                   |
| grouped peripheral: TX/RX on one UART unit, with TX fixed, the solver keeps RX on the same unit                                                                                                                                                   | `grouped_peripheral_same_unit`                                   | formally proved                                                   |
| explanation: the seven-PWM dead end names the seventh actuator and, for each PWM pin, the actuator blocking it; an unsupported fixed request is reported as such                                                                                  | `seven_pwm_explanation`, `no_capable_resource_explanation`       | formally proved by execution (first dead end, not a minimal core) |
| **feasibility is environment-sensitive**: six actuators SAT, the seventh — a monotone design extension — UNSAT                                                                                                                                    | `feasibility_not_monotone_under_extension`                       | formally proved                                                   |

## 7.3 The pipeline from Phase 6

    OutputId  →  DeviceKind  →  requirements  →  solve  →  assignment

`DeviceKind.requirements o` generates a sink's needs (`hBridgeChannel` ⇒ PWM +
DigitalOut; `i2cSensor` ⇒ SDA + SCL in one _same-unit_ group;
`quadratureEncoder` ⇒ two interrupts). `OutputId` never enumerates pins;
swapping the board is re-solving the same requirements (Counterexample B).
Device descriptions are a small closed vocabulary here; a reusable component
library is Phase-8 surface material.

## 7.4 What the alternatives cost or lack

| Alternative                                | Verdict                                                                                                                                                                |
| ------------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| exclusive-only allocation (`allDifferent`) | rejected: Counterexample E needs sharing                                                                                                                               |
| capability counts as feasibility           | rejected: Counterexample C                                                                                                                                             |
| pin capability without units               | rejected for independent PWM frequencies: `timers_matter`; sufficient for the plain motor example                                                                      |
| protocol-specific solver branches          | not needed: I2C/SPI/UART pin sets and units are board facts in the table; grouping is the generic `UnitRel.same`                                                       |
| `Ty.pwm` / `Ty.pin`                        | not needed: `MotorAngle` is `MotorAngle` on any board (§35) — nothing in the kernel changed                                                                            |
| pins as `OutputId`                         | rejected: a sink may need several resources (`hBridgeChannel`), and swapping boards must not change the design                                                         |
| `RequirementId = DeclId` / `OutputId`      | rejected: one sink generates several requirements; two identical PWM needs must be distinct variables                                                                  |
| SMT                                        | not needed for the tested scope: every constraint is unary or binary and the exhaustive solver is proved complete; `decide` runs the seven-PWM UNSAT search in seconds |
| minimal unsat core                         | deferred: `diagnose` reports the first dead end of a greedy prefix (Model B/C of §30), meaningful only when `solve` returned `none`                                    |

## 7.5 Invalidation and evidence

| Change                                                     | Effect on an existing valid assignment                                         |
| ---------------------------------------------------------- | ------------------------------------------------------------------------------ |
| add a resource / capability / sharing (`Hardware.Extends`) | preserved (`hardware_extension_preserves_validity`)                            |
| remove a resource                                          | may invalidate (G)                                                             |
| add a requirement                                          | old entries stay `PartialValid`; completeness for the new `R` may fail (A, §9) |
| strengthen a requirement                                   | may invalidate (H)                                                             |
| fix a pin                                                  | may turn SAT into UNSAT (F)                                                    |
| switch target                                              | re-solve; the design is untouched (B)                                          |

So "deployable on target T" is evidence about `Design × T` that is **not**
`Evidence.Monotone` in the Phase-1 sense: a monotone design refinement (adding a
declaration and its sink) can falsify it
(`feasibility_not_monotone_under_extension`). Phase 1's distinction is now
concrete: _stable logical evidence_ (commitments discharged compositionally,
which survive `EnvRefines`) versus _deployment-sensitive evidence_ (hardware
feasibility, which must be re-solved). The two are kept in different layers and
never merged.

## 7.6 Answers to §47

| Question                                   | Answer                                                                                                                     |
| ------------------------------------------ | -------------------------------------------------------------------------------------------------------------------------- |
| 1. Hardware resource?                      | `Resource`: nominal id, capabilities, per-capability unit.                                                                 |
| 2. Capability?                             | An element of the shared vocabulary `Capability`; opaque to the solver.                                                    |
| 3. Design-side requirement?                | `Requirement`: one capability, optional fixed resource, optional unit relation.                                            |
| 4. `RequirementId` independent?            | Yes: one sink ⇒ several requirements; two identical needs are two variables.                                               |
| 5. Assignment?                             | `List (Requirement × ResourceId)`.                                                                                         |
| 6. Valid?                                  | `ReqOK` per entry, `Compatible` per pair, coverage for completeness.                                                       |
| 7. Unassigned in partial designs?          | Yes (`PartialValid`, `partial_assignment_accepted`).                                                                       |
| 8. Complete deployment?                    | `ValidFor H R A` (covers `R`).                                                                                             |
| 9. Target-relative?                        | Yes (B).                                                                                                                   |
| 10. SAT on one board, UNSAT on another?    | Yes: `seven_pwm_unsat_on_nano`, `seven_pwm_sat_on_big`.                                                                    |
| 11. Exclusive vs shared?                   | Per-capability sharing policy in `Hardware.shareable`; sharing only among equal shareable capabilities.                    |
| 12. Grouped peripherals?                   | Independent requirements + `UnitRel.same`; board units carry the pairing.                                                  |
| 13. Pin capability alone sufficient?       | For the plain motor example yes; for independent PWM frequencies no — units (timers) are needed (`timers_matter`).         |
| 14. Solver sound?                          | Yes.                                                                                                                       |
| 15. Complete?                              | Yes, for the finite modeled fragment (`solve_complete`).                                                                   |
| 16. Manual pins?                           | `Requirement.fixed`, an added unary constraint; mixed manual/automatic supported (`fixed_assignment_respected`).           |
| 17. What invalidates?                      | §7.5.                                                                                                                      |
| 18. Extension preserves?                   | Yes (`hardware_extension_preserves_satisfiability`).                                                                       |
| 19. Stable vs hardware-sensitive evidence? | §7.5.                                                                                                                      |
| 20. Outside this phase?                    | Voltage, current, thermal, memory, CPU load, deadlines, bus bandwidth, torque, travel, power budget, PWM frequency values. |

## 7.7 Critical remarks

- The tested Nano pin/peripheral allocation problem is captured by a finite CSP
  with unary and binary constraints; that is a statement about this scope, not
  about embedded allocation in general. Numeric constraints (frequency
  compatibility, current budgets) would need summation constraints that are not
  binary; the architecture leaves room (a `Compatible`-like predicate over sets)
  but nothing here establishes it.
- `diagnose` is deliberately weak: a first dead end under greedy placement. It
  is honest about being _a_ conflict, not _the_ conflict.
- Units are one integer per capability per resource. That models "which timer"
  and "which UART" but not timer _modes_; PWM frequency stays a later validation
  property, as the brief allows.

## 7.8 The Phase-7 result (§50)

> The smallest declarative model is: resources with capabilities and
> per-capability units, a per-capability sharing policy, requirements with one
> capability plus optional fixed resource and unit relation, and validity as
> unary support plus pairwise compatibility. On it, an exhaustive solver is
> proved sound and complete, feasibility is decidable, hardware extension
> preserves assignments, and the BDL design is never an input to the solver — so
> a design is authored once, a board is chosen later, and the result is either a
> concrete pin/peripheral mapping or a structured conflict.

Among tested designs, for the discrete pin/peripheral scope.
