---
kind: report
phase: 16
area: surface
date: 2026-09-20
status: current
---

# Phase 16 — Communication as state, catalogue profiles, and the deployment-only `assign`

Question (the architectural hypothesis behind a realistic product — a host
submitting motion work over TCP, motors reporting over CAN, jobs queued and
cancelled, telemetry): does BDL need communication artifacts — a `Message`,
`Event`, `Packet`, `Stream` or `Channel` primitive — or is _semantic state and
its evolution_ enough, with communication appearing only at the physical
boundary as provision and realization? And, if profiles for those boundaries are
supplied by packages, what does a package contribute and what does `assign` do?
Answer: **the hypothesis survives every case tested** — repeated commands,
ordering, several occurrences in one tick, cancellation, acknowledgement,
freshness, timeout, fault latching, a bounded queue, semantic versus transport
identity, cross-clock delivery, a paired axis with a prepare/prepare/commit
protocol — each encoded with the existing kernel and executed; no
non-encodability witness was found, so no primitive is added. A package profile
is a value satisfying the contract Phases 13 and 14 already state, its origin is
data the semantics never reads, and `assign` _is_ the lowering (`lowerΔ`) or the
provision (`provision`) with a catalogue entry: it edits deployment, never
behaviour. Files: `BDL/Surface/Assignment.lean`,
`BDL/Experiments/CommunicationExamples.lean`; note:
[communication-as-state](../notes/communication-as-state.md).

The phase is an audit first: nothing was added to the model until an encoding
attempt had been made with what exists. The kernel is unchanged.

## 16.1 What exists and was reused

The formal machinery the audit ran on, by name:

- `Ty`: `bool | nat | q d | opt | list | prod | sem` — no event, message or
  stream type (FVD-0036, FVD-0048, FVD-0085 already rejected `Event τ` three
  times, with proofs about multiplicity).
- `delay init e` / `sync src init e` (Phases 4–5), `fold` and the library
  (`filterF`, `mapF`, `mapOptF`, `appendF`, `containsF`, Phase 9b).
- The Phase-9a window: `BDL.Buffer.decls` — five declarations whose `window` is
  the source's occurrences since the destination's previous activation, in order
  and with multiplicity (`buffer_window_correspondence`); capacity as a
  validation obligation (Phase 9a, `Validation/Capacity.lean`).
- Source provision (Phase 13): `Channel`, `DeviceProfile`, `Provision`,
  `provision`, `induced`, `provision_transparent`, `input_congr`.
- Output realization (Phase 14): `Encoder`, `Realization`, `RawCommand`,
  `lowerΔ`, `lower_transparent`, `two_realizations_same_behavior`, `Admissible`.
- The adapter boundary (Phase 15): `Policy`, `AdapterOp`,
  `two_policies_same_commands`; the device clock `lowerSync`.
- Hardware feasibility (Phase 7): `solve`, `HardwareSatisfiable`.

## 16.2 The state-encoding audit, executed

Two designs of ordinary declarations, one domain, in
`CommunicationExamples.lean` — the auto_typer stress case reduced to what is
semantically at stake, with no vendor frame bytes and no JSON:

- **Q, the work queue** (`queueDecls`): inputs `submit : list Job` (the jobs
  that arrived this tick, oldest first; `Job = (JobId, delta)` is a pair),
  `cancel : opt JobId`, `done : bool`; state `queue : list Job` (FIFO, bounded
  by `cap = 2` through `take`), `desired : Position` (advanced by a job's delta
  when it starts — a job starts when the head's identity changes),
  `overflow : bool` (a refused submission, observable), and a `dedup` variant
  that filters arrivals by the ids already queued.
- **M, the motion state** (`motionDecls`): inputs `fb : opt (pos × vel × fault)`
  (a sample, or none this tick), `target`, `reset`, `ackNow`; state `age` (ticks
  since the last sample), `fresh := age < 3`, `timedOut := age ≥ 6`,
  `lastPos`/`lastVel` (held), `err`, `inTol`, `settled` (consecutive fresh
  in-tolerance samples), `doneM := settled ≥ 2`, `fault` (latched until
  `reset`), `acked` (held until the target changes).
- **The composed controller** `ΔQM`: Q with `done := delay false doneM`, M with
  `target := desired` — one design, proved globally well formed, causal (no
  cycle: `done` reads the previous tick) and well clocked (`ΔQM_typed`,
  `ΔQM_causal`, `ΔQM_clocked`).

Every case below is a theorem proved by `decide` on the proved-sound interpreter
(`evalF` / `mevalF`):

| Case                        | Theorem                       | What it shows                                                                                                                                                                                       |
| --------------------------- | ----------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| multiplicity                | `exA_multiplicity`            | `Move(+10); Move(+10)` and `Move(+10)` are queues of two and one; after the first completes the desired position is `20` against `10`                                                               |
| ordering                    | `exB_ordering`                | `A; B` and `B; A` reach the same final target (40) through different desired trajectories (10 then 40; 30 then 40)                                                                                  |
| same-tick multiplicity      | `exC_same_tick`               | `[A, B]`, `[B, A]`, `[A]` in one tick are three queues; nothing is lost — the batch is a list                                                                                                       |
| cancellation by semantic id | `exD_cancellation`            | a queued job is removed; the active job is removed and nothing starts; an unknown id cancels nothing; the next job starts                                                                           |
| bounded queue               | `exE_bounded`                 | with `cap = 2` the third job is refused and `overflow` is true for that tick                                                                                                                        |
| semantic identity           | `exF_identity`                | a retried submission with the same `JobId` is one job under `dedup` and two under the plain design — the design decides, because the id is state                                                    |
| freshness, timeout          | `exG_freshness`               | `age` counts silence; `fresh` ends at three ticks, `timedOut` begins at six; `settled` counts on the held value while fresh and resets when stale, so `doneM` stops when freshness does             |
| repeated samples            | `exH_settling`                | one in-tolerance sample does not complete, two consecutive do; velocity counts (`(10, 3)` resets)                                                                                                   |
| fault latching              | `exI_fault_latch`             | one faulty sample latches `fault` through the following ticks; `reset` clears it                                                                                                                    |
| acknowledgement             | `exJ_ack`                     | an ack holds until the target changes, then lapses until the next                                                                                                                                   |
| the composed controller     | `exQM_composed`               | job 1 starts (desired 10); two settled samples complete it; the queue pops, job 2 starts (desired 15) and is not yet settled                                                                        |
| cross-clock delivery        | `exK_cross_clock`             | host submissions in a fast domain reach the controller's slow domain through the Phase-9a window, flattened (`flattenF`): `[A, B]` at the controller's tick 3; `[B, C]` at tick 6 after A completes |
| transport identity          | `exL_theorem`, `exL_executed` | the same submissions framed as `(sequence number, batch)` and as per-job `(frame id, job)` are one Source trace (`SameTrace`); `two_providers_same_behavior` applies; queues and desired coincide   |
| the paired axis             | `exN_pair`, `exN_two_motors`  | `DesiredPos` realized once with the pair command `(p, p)`: the sink carries `(10, 10)` then `(40, 40)`; two identity realizations on two sinks agree (`paired_commands_of_one_value`)               |
| builtin vs packaged         | `exP_origin`                  | the same profile under `builtin` and `package 7` lowers to one design                                                                                                                               |
| contract vs feasibility     | `exQ_contract_not_feasible`   | the pair profile satisfies the contract for `DesiredPos`, is feasible on the Nano and admissible; on a one-pin board it satisfies the same contract, is not feasible, and is not admissible         |

**Where the thesis was attacked and what it cost.** Two attacks found no
counterexample but did find work:

- _Occurrences to a slower device._ The output-side lowering into a device
  domain (`lowerSync`, Phase 15) samples the last command; two commands
  specified between two device activations reach the device as one. This is not
  a primitive gap — the Phase-9a window mirrored into the lowering (a log in the
  output's clock, transported, a cursor in the device domain, a `list raw` sink)
  is a construction over existing primitives — but the construction is not
  built; recorded in FVI-0024.
- _Occurrences below the tick._ Two raw sources delivering inside one base tick
  have no order in the model unless the adapter merges them into one raw
  reading; a transport retry that the adapter delivers twice is two semantic
  occurrences. Both are obligations on the provider — what "one delivered item
  per semantic occurrence, in arrival order, bounded per tick" must mean — not
  on the language; recorded as FVI-0029.

Not executed, and not needed as a primitive: priority ordering (an insertion by
`fold`, a library definition in the Phase-9b sense); telemetry (a logical output
at a slow clock, realized like any other).

## 16.3 The model added

`BDL/Surface/Assignment.lean` — nothing in `Core`:

- **Catalogue entries** — `Origin` (`builtin | package PackageId`),
  `InputEntry ⟨origin, DeviceProfile⟩` (Phase 13),
  `OutputEntry ⟨origin, DeviceOutputProfile⟩` (Phase 14), `Catalogue`. The
  origin is display data.
- **Contracts** — `OutputContract Θ accepts P := P.E.WF Θ ∧ EFits Θ accepts P.E`
  (semantic admissibility; no board),
  `Feasible H P := (solve H P.requirements).isSome` (deployment feasibility; no
  type), `InputContract Θ τ ch := ch.WF Θ ∧ Fits Θ τ ch` — exactly what
  `Provision.WF` asks per target (`WF.contract`, `WF.one_of_contract`).
- **`assign`** —
  `OutputEntry.realization en o d p e := ⟨o, d, p, e, en.profile.E⟩`,
  `assignOutput Δ en o d p e spec := lowerΔ Δ (en.realization …) spec`;
  `assignSource Δ en i r s clock := (en.profile.channels[i]?).map (provision Δ ∘ Provision.one r s clock)`.
- **Realizability** — `Realizable Θ H C accepts` (some entry admissible),
  `Provisionable Θ C τ` (some channel satisfies the contract).
- **Same semantic trace** — `SameTrace Δ P₁ P₂ I₁ I₂`: the induced inputs agree
  at every declaration other than the two raw ones, at every global tick.

## 16.4 Theorems

| Claim                                                                                                                                                                 | Theorem                                                          | Hypotheses                                                                      |
| --------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------- | ------------------------------------------------------------------------------- |
| admissibility is the contract and feasibility, neither seeing the other                                                                                               | `admissible_iff`                                                 | —                                                                               |
| a well-formed provision's targets satisfy the input contract; the contract suffices for the singleton                                                                 | `WF.contract`, `WF.one_of_contract`                              | `Provision.WF`; freshness and type shape                                        |
| **the origin is not read**: one profile, one realization, one lowered design, one raw command relation, one adapter operation relation                                | `OutputEntry.realization_of_profile`, `assign_indistinguishable` | `en₁.profile = en₂.profile`                                                     |
| the same on the input side                                                                                                                                            | `assignSource_origin_irrelevant`                                 | `en₁.profile = en₂.profile`                                                     |
| **`assign` does not edit behaviour**: the design is literally unchanged off the fresh encoder; every pre-existing term evaluates alike                                | `assignOutput_behavior_unchanged`, `assignOutput_transparent`    | `NoMention`, inputs avoiding `e` (Phase 14's)                                   |
| the assigned design is accepted by the unchanged judgments (well formed, causal, well clocked, drive-well-formed, single-driver)                                      | `assignOutput_checked`                                           | Phase 14's `WF`, `GlobalWF`, `Causal`, `WellClocked`, `DriveWF`, `SingleDriver` |
| the input-side assignment is Phase 13's transparency                                                                                                                  | `assignSource_transparent`                                       | `Provision.WF`, `NoMention`, `RawInput`                                         |
| a larger catalogue realizes and provisions more                                                                                                                       | `realizable_mono`, `provisionable_mono`                          | entry inclusion                                                                 |
| the induced input avoids every identity                                                                                                                               | `induced_avoids`                                                 | `Provision.WF`, `RawInput`                                                      |
| under the same trace the abstract design evaluates alike under either induced input                                                                                   | `induced_congr`                                                  | two `input_congr` steps                                                         |
| **Source-side non-interference**: two providers with the same semantic trace evaluate every term mentioning neither raw declaration alike; every logical output alike | `two_providers_same_behavior`, `two_providers_same_outputs`      | `Provision.WF` ×2, `NoMention` ×2, `RawInput` ×2, `SameTrace`                   |
| **two realizations of one output specify two transfers of one value**                                                                                                 | `paired_commands_of_one_value`                                   | `SingleDriver β`, `R₁.o = R₂.o`                                                 |

The **replacement-invariance criterion** — _if a carrier is replaced while the
product-observable semantic trace stays the same, behaviour stays the same_ — is
the conjunction of three theorems, one per boundary: Source side
`two_providers_same_behavior` (new), output side
`two_realizations_same_behavior` (Phase 14), adapter side
`two_policies_same_commands` (Phase 15). "Same semantic trace" is made precise
by `SameTrace` on the input side and by "one design, two lowerings" on the
output side; across clocks it is agreement at every global tick, which is
stronger than agreement at the reading domain's activations — a refinement not
needed by any case here.

Sixty-four theorem-like declarations (18 + 46); every one on
`propext`/`Quot.sound`; no `Classical.choice`; no `sorry`. The whole
development: 1 363 across 62 files; `lake build` 65 jobs, clean.

## 16.5 Models tried

| Model                                                                         | Verdict                                                                                                                                                                                                                                                                                                                                       |
| ----------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Event τ` / `Message τ` / `Stream τ` / `Channel τ` as a type                  | not added: no case in §16.2 needed one; an occurrence is `opt` at the tick (FVD-0036), a batch is a `list`, occurrences across clocks are the window (FVD-0085) — the fourth rejection, on a product-scale case                                                                                                                               |
| a queue primitive                                                             | rejected: `queue` is `take cap (filter … (append (drop-on-done prev) arrivals))`, five library applications over one `delay`; bounded by the design as ADR-0027 asks                                                                                                                                                                          |
| a transaction / atomic-frame primitive for prepare–prepare–commit             | rejected: one logical output with a pair command (`exN_pair`), or two realizations that agree tick by tick (`paired_commands_of_one_value`); the frame order is the backend's per-tick commit below `AdapterOp` (FVD-0140) — _definitional_ for the paired axis; FVI-0026's criterion (several independently meaningful outputs) is untouched |
| transport identity in the Source's type (`(seq, payload)` as the Source)      | rejected: the channel discards it and the theorem says nothing downstream can tell (`exL_theorem`); a transport identity that the product _does_ observe is, by that fact, semantic and belongs in the state (`exF_identity` — the design chooses)                                                                                            |
| freshness as a Source-side transducer property (FVI-0020's "freshness")       | moved: freshness is behaviour state (`age`, `exG_freshness`) — the design says what stale means; a transducer cannot                                                                                                                                                                                                                          |
| a `Package` type with versions, names, registries in the judgments            | rejected: the judgments take a profile; the origin is a field no theorem reads (`assign_indistinguishable`); versions and registries are engineering                                                                                                                                                                                          |
| one `Admissible` predicate mixing contract and board                          | kept as the conjunction (`admissible_iff`), with the two halves named so that a package check cannot collapse them (`exQ`)                                                                                                                                                                                                                    |
| `Feasible` including backend support (a target family that refuses a profile) | not modelled: production's `adapter.profile_unsupported` is a second feasibility half beside allocation; a `Backend.supports` predicate would be data, not semantics — noted for production, not built                                                                                                                                        |

## 16.6 Claim audit

- _proved_: everything in §16.4.
- _executed_: every row of §16.2.
- _definitional_: `assignOutput = lowerΔ`, `assignSource = provision`; the
  origin unread.
- _tested design failure_: none new — the earlier refutations (`Event` loses
  multiplicity under `sync`, FVD-0048; Model A, Phase 14) stand.
- _design decision_: the paired axis is one logical output by design intent
  (FVD-0148), not an instance of FVI-0026.
- _not established_: the occurrence-preserving crossing to a slower device
  (FVI-0024, amended); the provider's occurrence contract (FVI-0029); a
  backend-support half of feasibility; priority ordering and telemetry
  (unexecuted, not in doubt); anything below the raw reading or the adapter
  operation (FVI-0020, FVI-0023). The executed designs run on the specification
  interpreter, which memoizes nothing; the composed controller is executed for
  five ticks for that reason and for no other.

## 16.7 Verdicts

| Construct                                                                          | Verdict                                                                        | Decision |
| ---------------------------------------------------------------------------------- | ------------------------------------------------------------------------------ | -------- |
| `Event` / `Message` / `Packet` / `Stream` / `Channel` as a type; a queue primitive | REMOVE — communication history is state over the existing kernel               | FVD-0143 |
| the replacement-invariance criterion                                               | KEEP AS THEOREMS — three non-interference theorems, one per boundary           | FVD-0144 |
| catalogue entries, origins (`Catalogue`, `Origin`)                                 | KEEP IN DEPLOYMENT DATA — a profile satisfying the contract; the origin unread | FVD-0145 |
| `assign` (`assignOutput`, `assignSource`)                                          | KEEP IN DEPLOYMENT CONSTRUCTION — it is the lowering / the provision           | FVD-0146 |
| semantic admissibility vs feasibility (`OutputContract`, `Feasible`)               | KEEP SEPARATE — `Admissible` is their conjunction                              | FVD-0147 |
| a transaction primitive for a paired axis                                          | REMOVE — one output, one pair command; commit order below the operation        | FVD-0148 |
| package management (versions, registries, signatures)                              | OUT OF SCOPE — engineering                                                     | FVD-0145 |
