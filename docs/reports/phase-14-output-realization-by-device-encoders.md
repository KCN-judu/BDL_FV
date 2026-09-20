---
kind: report
phase: 14
area: surface
date: 2026-09-20
status: current
---

# Phase 14 — Output realization by device encoders

Question (the output-side dual of Phase 13; production ISS-0016's other half and
the `output adapter` of `docs/spec/runtime-semantics.md`): how can a
behaviour-level output stay independent of whether the machine realizes it
through PWM, GPIO, I²C, UART or another mechanism — and what is the smallest
correct construction in which the behaviour fixes the concept, deployment
chooses the raw command and the encoder, validation admits the choice, lowering
inserts the encoder, and only the backend performs the effect? Answer: the
logical output of Phase 6 already is that boundary; realization is a _lowering_
that adds one pure encoder declaration and one machine sink and changes nothing
the behaviour can observe; the machine boundary is a relation on commands, not a
term. Files: `BDL/Surface/OutputRealization.lean`,
`BDL/Experiments/OutputRealizationExamples.lean`; note:
[output-realization-by-device-encoders](../notes/output-realization-by-device-encoders.md).

## 14.1 The model

Nothing entered `Core`. Over the Phase-6 objects `OutputId`,
`OutputSpec = ⟨accepts, clock⟩`, `DriveEnv`, `DriveWF`, `SingleDriver`,
`CompleteOutputs`, `PhysicalOutput`:

- `Encoder = ⟨rep, raw, encode, transfer, rep_semFree, rep_data, raw_semFree, raw_data, encode_pure, computes⟩`
  — the device's command encoding: a **pure** term `encode : rep -> raw`
  (`Encoder.WF Θ := HasType Θ ∅ Grant.none [] encode (arr rep raw)`), its
  transfer function on values, and
  `computes : ∀ v, TyVal rep v → Transduces encode v (transfer v)`. Both `rep`
  and `raw` are sem-free data: an encoder observes a representation and produces
  a command; it never handles a concept value.
- `EFits Θ accepts E`: at `sem c`, `Θ c = some E.rep`; at a data type, the type
  is `E.rep`. Decidable.
- `Realization = ⟨o, d, p, e, E⟩`: the logical output `o` and its driver `d`
  (pre-existing), a fresh machine sink `p`, a fresh encoder declaration `e`.
- **Model B — the specification, on the unchanged design.**
  `RawCommand S Δ I Ω β R t w`
  `:= ∃ spec v, Ω o = some spec ∧ PhysicalOutput … o t v ∧ w = transfer (unwrapAt spec.accepts v)`
  — the command _specified_ for realization `R` at tick `t`. The machine sink
  `p` does not occur in it: the definition says what the command is, not who
  receives it; that the lowered design's `p` carries exactly it is the theorem
  `lower_correspondence`. This is the machine boundary. No BDL term, no
  evaluation rule, no effect.
- **Model C — the lowering.**
  `lowerΔ Δ R spec = Δ[e ↦ ⟨raw, []⟩ realized by encoderBody]` with
  `encoderBody (sem c) = app encode (rep (declRef d))` and
  `encoderBody τ = app encode (declRef d)`; `lowerΩ = Ω[p ↦ ⟨raw, spec.clock⟩]`;
  `lowerβ = β.bind e p`; `lowerΚ = Κ[e ↦ spec.clock]`. `o`, `d`, `β d = o` and
  every other declaration are untouched.
- `WF Θ Δ Ω β Κ R spec`: `Ω o = some spec`, `β d = some o`,
  `tyView d = some spec.accepts`, `Κ d = some spec.clock` (the last two are what
  `DriveWF` gives: `WF.of_driveWF`), `e` and `p` fresh, `EFits`, `Encoder.WF`.
- `OutputTyped`: the logical output carries wrapped representation values —
  derived from Phase 5's totality in `output_value_typed`.
- `DeviceOutputProfile = ⟨E, requirements⟩` and
  `Admissible Θ accepts H P := P.E.WF Θ ∧ EFits Θ accepts P.E ∧ (solve H P.requirements).isSome`
  — typing, fit and allocation, three judgments that never see each other
  (decidable; `Encoder.WF` is decided by `infer`). The strictly weaker
  `FitsAndAllocates := EFits ∧ solvable` is kept under that name only to state
  the gap (`admissible_needs_wf`): the hardening pass found the first
  `Admissible` omitted the typing (FVD-0139 supersedes FVD-0137).

## 14.2 Models tried

| Model                                                                      | What it does                           | Verdict                                                                                                                                                                                                                                                                                      |
| -------------------------------------------------------------------------- | -------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **A** — retarget `o.accepts := raw`, drive `e -> o`                        | mutates the logical output's interface | _tested design failure_: `retarget_breaks_driveWF` — the existing edge `d -> o` fails `DriveWF` (the driver is typed at the concept), so `β` must be rewritten too; the abstract output's meaning is lost; Phase 6 already calls it an edit (`rebinding_invalidates_design`); executed `exI` |
| **B** — keep `o`, `β d = o`; specify the machine command as a relation     | `RawCommand`                           | **kept as the specification**: the design is literally unchanged; the boundary is honest (a relation, not an effectful term)                                                                                                                                                                 |
| **C** — lower to a fresh encoder declaration and a fresh raw sink, `o ↦ p` | `lowerΔ`/`lowerΩ`/`lowerβ`/`lowerΚ`    | **kept as the lowering**: expressible in the existing kernel; `lower_correspondence` proves it implements B                                                                                                                                                                                  |
| a pure `R -> ()` as the physical sink                                      | an effectful consumer as a term        | _tested design failure_ (Phase 12 `consumers_indistinguishable`): the term cannot name a receiver; nothing here needs it                                                                                                                                                                     |
| device kind in `OutputSpec`                                                | `⟨accepts, clock, deviceKind⟩`         | rejected without a theorem: `exH` realizes one `oLight` by PWM and by I²C with the same behaviour trace; a kind in the spec would make that two designs. Design rule FVD-0131                                                                                                                |
| the encoder constructing a concept                                         | `λx. mk Other x` as an encoder         | _tested design failure_: refused under `Grant.none` (`exEFG`); `encoder_constructs_nothing`, `encoder_decl_no_grant` (a sem-free data type grants nothing)                                                                                                                                   |
| "closed and well-typed" as the encoder condition                           | typing without purity                  | _tested design failure_: `(λk. λn. k) (delay 0 1)` is typed at `q₀ -> q₀` and encodes 7 as 0 at tick 0 and 1 at tick 1 (`exEFG`) — Phase 13's `exD` shape                                                                                                                                    |
| an implicit clock crossing (the encoder in another domain)                 | `ΚBad`                                 | _tested design failure_: `DriveWF` and `WellClocked` both fail (`exI`); the crossing must be an explicit `sync` upstream, as Phase 6 Counterexample G already says                                                                                                                           |
| many logical outputs → one machine command as a primitive                  | `lowerMany`                            | not built: the H-bridge case is a structured raw command from one concept (`exD_hbridge`); RGB is three per-tick commands the backend batches, or one `Color` concept upstream. Recorded as FVD-0136 with the open item FVI-0022                                                             |

## 14.3 Theorems

| Claim                                                                                                                                          | Theorem                                                                                               | Hypotheses                                                                                                                   |
| ---------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------- |
| the nominality boundary: a well-formed encoder constructs no concept; the encoder declaration has no grant                                     | `encoder_constructs_nothing`, `encoder_decl_no_grant`, `grant_of_semFree_data`                        | `Encoder.WF`; `raw` sem-free data                                                                                            |
| typing in the empty design excludes `declRef`                                                                                                  | `refFree_of_empty_typed`, `Encoder.WF_refFree`                                                        | —                                                                                                                            |
| the raw command is a function of the tick                                                                                                      | `RawCommand.det`                                                                                      | `SingleDriver β`                                                                                                             |
| **behaviour preservation**: the environment is literally unchanged off `e`                                                                     | `behavior_unchanged`                                                                                  | — (definitional)                                                                                                             |
| every pre-existing term evaluates identically, same input                                                                                      | `lower_transparent`, `lower_decl_transparent`                                                         | `NoMention Δ e`; inputs avoid `e`; `e ∉ refs`; `ρ` avoids `e`                                                                |
| every logical output carries the same value                                                                                                    | `lower_physicalOutput_unchanged`                                                                      | `WF`, `DriveWF`, the above                                                                                                   |
| refinement: one declaration added, drive edges extended, `Ω` extended                                                                          | `lower_envRefines`, `lower_singleDriver` (`DriveRefines`), `lower_outputEnv_extends`                  | `WF`, `DriveWF`, `SingleDriver`                                                                                              |
| the new edge is well formed and single-driver is preserved (Phase 6's first binding)                                                           | `lower_driveWF`, `lower_singleDriver`                                                                 | `WF`, `DriveWF`, `SingleDriver`                                                                                              |
| completeness for `p :: req`                                                                                                                    | `lower_completeOutputs`                                                                               | `WF`, `DriveWF`, `CompleteOutputs β req`                                                                                     |
| the encoder declaration is typed at `raw` under its own (empty) grant                                                                          | `encoderBody_typed`                                                                                   | `WF`                                                                                                                         |
| global well-formedness                                                                                                                         | `lower_wf`                                                                                            | `ev.Monotone`, `GlobalWF Δ`, `WF`                                                                                            |
| causality: one edge `e -> d`, `e` on top                                                                                                       | `lower_causal`                                                                                        | `WF`, `NoMention`, `Causal Δ`                                                                                                |
| clocks: `e` in the output's clock, no device clock                                                                                             | `lower_wellClocked`                                                                                   | `WF`, `NoMention`, `WellClocked Κ Δ`                                                                                         |
| **correspondence**: `PhysicalOutput Δ' p t w ↔ RawCommand Δ R t w` — raw trace = transfer ∘ abstract trace, tick by tick in the output's clock | `lower_correspondence`, `encoder_value`                                                               | `WF`, `DriveWF`, `SingleDriver`, `NoMention`, inputs avoid `e`, `OutputTyped`                                                |
| the abstract value is a typed representation value                                                                                             | `output_value_typed`                                                                                  | `Θ.WF`, `Causal`, `GlobalWF`, typed inputs (`Red`), `WF`, `SingleDriver`                                                     |
| **platform independence, formal side**: two realizations of one design give the same `MEv` evaluation of every term mentioning neither encoder | `two_realizations_same_behavior`                                                                      | both `e` fresh (`NoMention`), inputs whose closures avoid both, `ρ` avoids both — nothing about a compiler, backend or board |
| independent realizations commute exactly                                                                                                       | `lower_comm`, `DeclEnv.update_comm`                                                                   | distinct `e`, distinct `p`                                                                                                   |
| Model A refuted                                                                                                                                | `retarget_breaks_driveWF`                                                                             | `β d = some o`, `tyView d = sem c`, `raw` sem-free                                                                           |
| the encoder's canonical type is `() -> raw`; the machine sink accepts `raw` in the output's clock                                              | `lowered_interfaces`                                                                                  | —                                                                                                                            |
| validation: admissibility is typing + fit + a solvable board; it gives a valid assignment; the typing cannot be dropped                        | `admissible_satisfiable`, `admissible_needs_wf`, `Admissible.toFitsAndAllocates`, `Admissible.enc_wf` | `Admissible`                                                                                                                 |

Executed (`OutputRealizationExamples.lean`): `exA_gpio`, `exB_pwm`,
`exB_quantized` (40 % and 41 % → duty 6; the realization still passes
`driveWFCheck`), `exC_servo` (90° → 1500 µs), `exD_hbridge` (`(true, 30)` →
`(60, true)`), `exEFG` (fits, misfits, the constructing encoder, the impure
encoder), `exH` (one light by PWM and by I²C: identical behaviour trace,
different command types and traces), `exH_structure` (the structural theorems
instantiated), `exH_admissible` (both profiles admissible on the Nano; the PWM
profile not admissible for the relay), `exJ` (an encoder that fits and allocates
but whose term is `λn. true`, not `Q0 -> Q0`, is not admissible),
`exI`/`exI_theorem` (Model A and the implicit clock crossing).

Seventy-four theorem-like declarations (51 + 23); every one on
`propext`/`Quot.sound`; no `Classical.choice`; no `sorry`.

## 14.4 Claim audit

- _proved_: everything in §14.3.
- _executed_: the examples of §14.3's last paragraph.
- _tested design failure_: Models A, the effectful sink (by Phase 12), the
  constructing encoder, the impure encoder, the implicit clock crossing.
- _definitional_: `behavior_unchanged` (an `update` off its key); `RawCommand`
  as the machine boundary; `Admissible` as a conjunction.
- _not established_: codegen refinement (the generated `Outputs` struct and the
  future adapter call against `RawCommand`); stateful output adapters (slew-rate
  limiting, dithering, batching, hysteresis); a device clock different from the
  output clock; atomic multi-value frames; commitments on outputs (production
  authors none) — FVI-0022.
- _design decision_ (supported by examples and minimality reasoning, not a
  theorem): the singleton realization as primitive (FVD-0136); the logical
  output as _the_ platform-independence boundary (FVD-0131) — the theorem behind
  it, `two_realizations_same_behavior`, is the formal-evaluation statement above
  and nothing more.
- _design recommendation_: the production shape in the note §5.

Terminology: Phase 6 called `OutputId` a _physical sink_. After this phase the
accurate reading is a **logical output** — semantic intent at the behaviour
boundary, terminal (no feedback), _physically realized_ by a deployment-chosen
machine sink. The Lean names are unchanged; FVD-0050 carries a dated amendment.

## 14.5 Verdicts

| Construct                                                                    | Verdict                                                                                                  | Decision                       |
| ---------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------- | ------------------------------ |
| logical output (`OutputId`, `OutputSpec`), `DriveWF`, `SingleDriver`         | KEEP IN KERNEL — unchanged, and they are the platform-independence boundary                              | FVD-0131                       |
| device kind in `OutputSpec`                                                  | REMOVE (never add)                                                                                       | FVD-0131                       |
| output encoder / device profile (`Encoder`, `DeviceOutputProfile`)           | KEEP IN DEPLOYMENT CONSTRUCTION (catalogue data; a lowering)                                             | FVD-0132                       |
| the lowering `lowerΔ`/`lowerΩ`/`lowerβ`/`lowerΚ` (Model C)                   | KEEP IN DEPLOYMENT CONSTRUCTION                                                                          | FVD-0132                       |
| `RawCommand` (Model B)                                                       | MOVE TO MACHINE/BACKEND — the specification of the boundary                                              | FVD-0134                       |
| effectful `R -> ()`, `Expr.write`, effect rows                               | REMOVE                                                                                                   | FVD-0134                       |
| encoder purity and `Grant.none`                                              | KEEP IN DEPLOYMENT CONSTRUCTION (as the profile condition)                                               | FVD-0133                       |
| hardware requirements of a device; admissibility = typing + fit + allocation | MOVE TO VALIDATION (`Admissible`, `FitsAndAllocates` only to state the gap)                              | FVD-0139 (supersedes FVD-0137) |
| injectivity / round-trip of the encoding                                     | REMOVE — not required; quantization admitted                                                             | FVD-0135                       |
| many-to-one output lowering                                                  | DEFER — singleton primitive by decision; combine upstream or batch per tick; atomic frames stay FVI-0022 | FVD-0136                       |
| device clock ≠ output clock, PWM carrier as a `ClockId`                      | DEFER — explicit `sync`; the carrier is device configuration                                             | FVD-0138                       |
| stateful output adapters                                                     | DEFER (FVI-0022)                                                                                         | —                              |

## 14.6 Hardening pass (2026-09-20)

The same day, after the phase closed: `Admissible` gained the encoder's typing
(FVD-0139 supersedes FVD-0137; `exJ`, `admissible_needs_wf`); the prose around
`RawCommand` was corrected so that the specification (the command for `R`) and
the lowered machine sink (`lower_correspondence`) are not conflated; the scope
of `two_realizations_same_behavior` is stated exactly; FVD-0136 carries an
amendment stating it is a decision, with the atomic-frame counter-pressure case
in FVI-0022; the terminology _logical output / machine sink_ is applied to the
current pages, with `PhysicalOutput` kept as the historical name of the value a
logical output carries. No theorem statement of §14.3 changed except
`admissible_satisfiable`, which now also yields the typing.
