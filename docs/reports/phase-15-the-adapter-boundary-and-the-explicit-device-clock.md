---
kind: report
phase: 15
area: surface
date: 2026-09-20
status: current
---

# Phase 15 — The adapter boundary and the explicit device clock

Question (FVI-0022 after the audit of the open items; production's first
embedded platform adapter, ADR-0037): what is the smallest honest formal
boundary beyond `RawCommand` now that a production adapter exists — and does
the explicit device-clock variant that Phase 14 deferred survive the
preservation theorems? Answer: one boundary — the raw command read by an
explicit *policy* into an abstract sink operation, with the physical line as a
fold over the operations — and yes: a realization lowered through Phase 5's
`sync` into a device domain preserves the behaviour, well-formedness,
causality (with no new instantaneous edge), clocks and single-driver, and
corresponds to the command sampled strictly before. Files:
`BDL/Surface/Adapter.lean`, `BDL/Surface/DeviceClock.lean`,
`BDL/Experiments/AdapterExamples.lean`; note:
[the-adapter-boundary-and-the-device-clock](../notes/the-adapter-boundary-and-the-device-clock.md).

The phase began with the audit of every active open item against Phases 8a–14
and production `6be778b` (the triage table is in
[issues/README.md](../issues/README.md) and each record's _Audit_ section):
eleven items were resolved, deferred or merged, FVI-0022 was split into five
questions (FVI-0023 … FVI-0027), FVI-0011 was narrowed and its explanation half
split off (FVI-0028), and FVI-0022's first two questions were selected because
production's adapter had removed their dependency.

## 15.1 The model

Nothing entered `Core`.

- **`Policy`** — `accept : Value → Option Value`: the adapter's reading of a
  raw command; `none` is a refusal. `Policy.total` (apply as is), `duty8`
  (production's policy on the kernel's naturals: `0 ..= 255` applied, else
  refused; production rounds a finite `f64` first — outside the model),
  `clamp8` (for comparison; production refused it), `level`.
- **`Op`** — `set m | refused | held`: production's `AdapterOp` as data. No
  term, no evaluation rule, no effect.
- **`AdapterOp S Δ I Ω β R spec P t op`** — the operation on realization
  `R`'s sink at global tick `t`, over the *unchanged* design: `held` when
  `S spec.clock t = false`; `set m` when the clock is active,
  `RawCommand … t w` and `P.accept w = some m`; `refused` when
  `P.accept w = none`.
- **`Line … start t m`** — the value the physical line carries after tick
  `t`: `start` until a command is accepted; the last accepted value
  thereafter; a refusal or an inactive tick changes nothing. The only state at
  the boundary; it lives in the adapter.
- **The explicit device clock** (`DeviceClock.lean`): `InitRep` (a pure
  closed representation value), `syncBody accepts encode c init d` =
  `encode (sync c init (rep d))` (or `encode (sync c init d)` at a data
  output), `lowerSyncΔ` / `lowerSyncΩ` / `lowerSyncΚ` placing `e` and `p` in
  the device domain `dc`, `SampledCommand` (the command at the last
  activation of the output's clock strictly before `t`, or the initial
  representation's transfer).

## 15.2 Models tried

| Model                                                                  | Verdict                                                                                                                                                                                                                                                                                                       |
| ---------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| the policy inside the encoder (reject-and-hold as encoder state)       | rejected: the hold depends on history, the encoder is a function of the current value (FVD-0133); the hold is a fold over operations (`Line`), below the raw command — _definitional_                                                                                                                       |
| an effect in the kernel for the adapter                                | rejected again: `AdapterOp` is a relation on commands; nothing in `Core` (FVD-0134 stands)                                                                                                                                                                                                                    |
| the PWM carrier as a `ClockId`                                         | rejected (FVD-0138 stands): configuration; the device domain of `lowerSync` is a BDL domain the deployment chooses, not the carrier                                                                                                                                                                              |
| an implicit device-clock crossing                                      | already refuted (Phase 14 `exI`); the explicit `sync` variant is the one that survives                                                                                                                                                                                                                       |
| a `StatefulEncoder` primitive                                          | not added: no non-encodability witness. Slew-rate limiting is behaviour state upstream (`exE_slew`: a `delay` declaration ramps the brightness, the same pure encoder produces the ramped raw trace); hysteresis and smoothing likewise; debouncing is Source-side (FVI-0020); dithering is below the tick (backend); batching is the backend's per-tick commit (FVI-0025) |
| `lowerMany` for atomic frames                                          | not built: per-tick batching (two `AdapterOp`s in one tick) or an upstream product concept represent the cases known; the criterion under which both fail has no witness (FVI-0026)                                                                                                                             |
| production's `f64` rounding inside the kernel                          | rejected: the kernel's raw values are naturals; the policy is modelled mathematically (`duty8`), the rounding is recorded as production's (FVI-0023)                                                                                                                                                             |

## 15.3 Theorems

| Claim                                                                                                                                    | Theorem                                                                                                         | Hypotheses                                                                                |
| ---------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------- |
| the operation is a function of the tick                                                                                                  | `AdapterOp.det`                                                                                                 | `SingleDriver β`                                                                          |
| the raw command does not depend on the policy — no policy, no refusal reaches the behaviour                                              | `adapter_downstream`                                                                                            | — (definitional)                                                                          |
| **the operation is determined by the lowered design's machine sink** — `lower_correspondence` carried one step further, both directions | `adapter_of_sink`, `sink_of_adapter`                                                                            | Phase 14's `WF`, `DriveWF`, `SingleDriver`, `NoMention`, avoiding inputs, `OutputTyped`; the tick active |
| two policies over one realization read one command trace                                                                                 | `two_policies_same_commands`                                                                                    | `RawCommand` at an active tick                                                            |
| the line is a function of the tick; a refusal or an inactive tick holds it; an accepted command is its value; it never carries a refused command | `Line.det`, `line_holds_on_refusal`, `line_holds_when_inactive`, `line_last_accepted`, `line_value_accepted` | `SingleDriver β`                                                                          |
| **device clock**: the behaviour is literally unchanged off `e`                                                                           | `lowerSync_transparent`, `lowerSync_decl_transparent`                                                           | `NoMention`, inputs avoid `e`                                                             |
| refinement, single-driver, well-formed edges in the device domain, completeness                                                          | `lowerSync_envRefines`, `lowerSync_singleDriver`, `lowerSync_driveWF`                                           | `WF`, `DriveWF`, `SingleDriver`                                                           |
| the transported body is typed at `raw` under the empty grant                                                                             | `syncBody_typed`, `lowerSync_wf`                                                                                | `WF`, `InitRep.WF` at `rep`, monotone evidence, `GlobalWF Δ`                              |
| **no new instantaneous edge**: the abstract rank serves unchanged                                                                        | `lowerSync_causal`, `syncBody_instRefs`                                                                         | `Causal Δ`                                                                                |
| well clocked with `e` in the device domain and the transported operand in the output's clock                                            | `lowerSync_wellClocked`                                                                                         | `WF`, `NoMention`, `WellClocked`                                                          |
| **sampled correspondence**: the device-clocked sink carries the command specified at the last activation of the output's clock strictly before, or the initial representation's transfer | `lowerSync_correspondence`                                                                          | Phase 14's hypotheses + `TyVal rep i.value`                                               |

Executed (`AdapterExamples.lean`): `exA_policies`, `exA_set` (duty 102 set,
line 102), `exB_refusal` (duty 306 refused under `duty8`, line holds 0; set 255
under `clamp8`; set 306 under `total`), `exC_held` (inactive tick holds),
`exD_device_clock` (device domain on odd ticks, output clock on even: the sink
carries 102 at tick 1 and 107 at tick 3, `prevAct` naming 0 and 2),
`exD_initial` (before the first activation: the initial representation, duty
0), `exD_structure` (the structural theorems instantiated), `exE_slew` (the
ramp `10, 20, 30, 40` in the design and `25, 51, 76, 102` at the sink).

Forty-four theorem-like declarations (10 + 24 + 10); every one on
`propext`/`Quot.sound`; no `Classical.choice`; no `sorry`.

## 15.4 Claim audit

- _proved_: everything in §15.3.
- _executed_: the examples.
- _definitional_: `adapter_downstream`; the line as a fold.
- _tested design failure_: the policy inside the encoder (by FVD-0133's
  purity), the implicit crossing (Phase 14).
- _design decision_: the classification of the stateful cases (FVI-0025); the
  singleton stays primitive (FVD-0136).
- _not established_: anything below the operation — production's `f64`
  rounding, the HAL, the register, the electrical world (FVI-0023); a device
  that acknowledges; which initial representation a device should hold
  (FVI-0024); a witness for a stateful realization (FVI-0025); the
  atomic-frame criterion (FVI-0026); commitments (FVI-0027). The generated
  Rust's agreement with `AdapterOp` is production-tested
  (`host_adapter_operations_correspond_to_the_commands`), never proved.

## 15.5 Verdicts

| Construct                                                    | Verdict                                                             | Decision |
| ------------------------------------------------------------ | ------------------------------------------------------------------- | -------- |
| boundary policy, sink operation, line (`Policy`, `Op`, `AdapterOp`, `Line`) | MOVE TO MACHINE/BACKEND — modelled as relations, outside the behaviour | FVD-0140 |
| reject-and-hold as encoder state                             | REMOVE                                                              | FVD-0140 |
| the explicit device clock (`lowerSync`)                      | KEEP IN DEPLOYMENT CONSTRUCTION                                     | FVD-0141 |
| the carrier / bus frequency as a `ClockId`                   | REMOVE (FVD-0138 stands)                                            | FVD-0141 |
| a stateful realization primitive                             | REMOVE for now — no witness; behaviour state upstream, backend state below | FVD-0142 |
| production's `f64` rounding in the kernel                    | REMOVE — recorded as production's                                   | FVD-0140 |
