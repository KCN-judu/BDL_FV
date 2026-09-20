---
kind: report
phase: 18
area: surface
date: 2026-09-20
status: current
---

# Phase 18 — The Source-side boundary: provider state, the device clock, initialization, commitments, `computes`, out-of-type readings

Question (what FVI-0020 still held after Phase 17): can the remaining
Source-side concerns — a transducer that needs memory, a device that samples in
its own domain, a Source read before its first sample, a commitment a provider
is asked to discharge, the `computes` obligation, a physical reading that is not
a value of the raw type — be represented as deployment-side constructions over
the existing kernel, without deployment adding product behaviour? Answer: **yes,
each of them, and each is proved**, on one lemma: the behaviour sees a Source
through its value trace and through nothing else (`MEv.congr_at`). A stateful
transducer is a Mealy machine that may sit below the raw reading or above it
with the same Source trace (`provider_state_movable`), so its placement is a
question of visibility, not of meaning, and a state that reads a design value
cannot be a provider's at all. The Source-side device clock is an explicit
`sync` of the raw reading with an explicit initial value (`provisionSync`) or
Phase 9a's window over it (`provisionWindow`) — no hidden clock, no fabricated
reading. A commitment is discharged by a provider at one of three evidence
levels that differ in who establishes the assumption on the reading
(`discharge_static`, `discharge_checked`, `discharge_trusted`), the trusted
level's assumption being a visible hypothesis. `computes` is proof-carrying,
derivable from the term (`Channel.ofTerm`) and decidable at a finite raw type
(`computes_of_bool`). An out-of-type reading is refused by a checking provider
and crosses as `none` or a flag, never as a value (`checkedProvide`,
`checked_typed`). Nothing entered `Core`. Files:
`BDL/Surface/SourceBoundary.lean`,
`BDL/Experiments/SourceBoundaryExamples.lean`; note:
[the-source-side-boundary](../notes/the-source-side-boundary.md).

## 18.1 The lemma

`MEv.congr_at s`: if `Δ₂` keeps every realization of `Δ₁` other than `s`'s,
reads every other input of `Δ₁` alike, and gives `s` the same value at every
tick in every domain, then every evaluation in `Δ₁` holds in `Δ₂` — for every
term, every environment, every domain. Nothing is said about how `s` gets its
value on either side: an input, a transducer over a device, a machine, a
transport. Every result below is this lemma with the two value traces computed.

## 18.2 Part A — provider state

`Machine σ raw raw'`: a pure BDL step term `σ × raw → σ × raw'`, the same
function on values (`stepF`), a pure closed initial state, the coherence
`computes` and the typing `preserves`; `run` threads the state over a physical
stream, `out` is the delivered stream. `machineBody M m r` is the machine as one
declaration with `delay` over the reading `r`; `Machine.ofTerm` builds a machine
from its term alone.

| Claim                                                                                                                                                                            | Theorem                                       |
| -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------- |
| the upstream declaration computes the machine's run, tick by tick, in the single domain                                                                                          | `machine_upstream`                            |
| the Source provisioned from the provider running the machine below the reading carries `wrap (transfer (M.out x t))`; realized from the machine upstream, the same               | `below_source_trace`, `upstream_source_trace` |
| **every evaluation of the provisioned design holds in the upstream design** — the provider's state is unobservable except through its trace, and the trace is available upstream | `provider_state_movable`                      |
| two providers running different machines over different streams with one output stream induce one semantic trace (hence one behaviour, Phase 16)                                 | `stateful_providers_same_trace`               |
| provider state is a function of the physical stream alone                                                                                                                        | `Machine.run_congr` (examples)                |

**The boundary criterion.** Since either placement gives the same trace, the
placement is decided by _visibility_, not by semantics: state whose parameter
the product fixes, whose reset the product commands, or whose reading the
product shows belongs upstream, where the design and the simulation exhibit it;
state that only interprets a device's signal may sit in the provider. Two facts
sharpen it. A provider's state is a function of the raw stream alone
(`Machine.run_congr`); a state that reads a design value — the fault latch that
reads `reset`, the settling count that reads `target` — is not expressible below
the reading, because a channel term mentions no declaration
(`exA_latch_reads_design`, from `Channel.tr_pure`). And a parameter that changes
the semantic trace for one physical stream is a product decision if the
product's specification fixes it: the debounce threshold (`exA_debounce_param`:
threshold 2 rises at tick 4, threshold 1 at tick 1) and the hysteresis
thresholds (`exA_hysteresis_param`) are shown to be in the trace. The cases
classified: **debouncing** — provider when the threshold is the device's contact
bounce, upstream when it is the product's press time; **quadrature decoding** —
the edge is a function of two consecutive phase readings, provider;
**accumulation and homing** — read `reset`, upstream (`exA_quadrature`);
**filtering** — the filter's constant is in the trace, so upstream when the lag
is the product's (the executed `filter` machine sits either side, `exA_filter`);
**hysteresis for signal interpretation** — provider; **semantic hysteresis** (a
thermostat's band) — upstream.

## 18.3 Part B — the Source-side device clock and initialization

`provisionSync Δ r s pc i ch`: `r` unresolved in the provider's domain `pc`,
`s := realizeWith τ tr (sync pc init r)` in its own domain — the input dual of
Phase 15's `lowerSync`. `sampled S pc i I' r t` names the reading: the raw value
at the last activation of `pc` strictly before `t`, or the initial value.
`inducedSync` is the abstract input it induces.

| Claim                                                                                                                                                                                                  | Theorem                                                                                                                    |
| ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | -------------------------------------------------------------------------------------------------------------------------- |
| the Source carries the wrapped transfer of the sampled reading — sampling and initial value explicit                                                                                                   | `provisionSync_target`, `sampled_mev`                                                                                      |
| the abstract design under the induced input and the sampled provision evaluate every term alike                                                                                                        | `provisionSync_transparent`                                                                                                |
| no new instantaneous edge; well clocked with the reading in `pc` and the Source's body in its own domain; a refinement; globally well formed with the target typed                                     | `provisionSync_causal`, `provisionSync_wellClocked`, `syncRealizeAt_typed`, `provisionSync_envRefines`, `provisionSync_wf` |
| **the occurrence-like crossing**: the Source over Phase 9a's window of the raw reading carries the transfer of the batches at the provider's activations since the Source domain's previous activation | `provisionWindow_target` (over `buffer_window_correspondence`, unchanged)                                                  |

**Initialization.** The initial value is the crossing's explicit `InitRep`
(Phase 15's object, reused): a profile-supplied raw value
(`InitPolicy.supplied`; `exB_sampled`: 250 at tick 0, the tick-0 reading at
ticks 1–2, the tick-2 reading at tick 3), or `none` at an optional raw type so
the Source reads _unavailable_ until the first sample and the design says so
(`InitPolicy.unavailable`; `exB_unavailable`). Activation gated on the first
sample is not a construction — a schedule is not a function of an input — and is
the optional form. No reading is ever fabricated. `exB_window_edges`: encoder
edges in a fast provider domain reach a Source domain on every third tick as
`[0, 1, 1]`, accumulated to 2 then 4 — none lost.

## 18.4 Part C — commitment discharge

`RangeSoundUnder ev R r A`: the evidence accepts a value-range fact under an
assumption `A` on the raw reading — `ev Δ e p` holds whenever every value `e`
takes, under every input whose reading at `r` satisfies `A` at every tick, has
`R p`. `discharge_under` discharges the provisioned target's commitment `p` when
the transfer of every reading satisfying `A` has the property. The three levels
are three choices of `A` and of who establishes it:

| Level       | `A`                                 | Established by                                              | Theorem             |
| ----------- | ----------------------------------- | ----------------------------------------------------------- | ------------------- |
| **static**  | `TyVal raw`                         | the transducer alone (the saturating ADC never exceeds 450) | `discharge_static`  |
| **checked** | `ok v = true`, `ok` implying typing | the checking provider, by construction (`checked_items_ok`) | `discharge_checked` |
| **trusted** | `TyVal raw v ∧ range v`             | nobody here — a hypothesis of the evidence, visible         | `discharge_trusted` |

Executed on one property (`AtMost450`) with the canonical sound evidence
`rangeEvidence`: `exC_static` (the saturating transducer), `exC_trusted` (the
identity channel under an assumed device range), `exC_checked` (the identity
channel behind a validating provider), `exC_provider_checks` (1000 and a boolean
refused, 300 and 450 kept). A profile declaration alone is not evidence: at the
trusted level it is exactly an assumption the theorem names.

## 18.5 Part D — `computes`

The Phase-13 field `computes : ∀ v, TyVal raw v → Transduces tr v (transfer v)`
is proof-carrying. It is **derivable**: `Channel.ofTerm` defines the transfer
function as the term's evaluation and proves `computes` from the interpreter's
totality on typed inputs (`gpioOfTerm`, `exD_ofTerm`). It is **decidable at a
finite raw type**: `computesBool` evaluates the term at `true` and `false` and
compares with the supplied function (`Value.beq_sound`), and a passed check is
the obligation (`computes_of_bool`; `exD_bool`: the identity passes, the
negation fails). At an infinite raw type a separately supplied transfer function
is a _claim_ about the term, testable on samples and provable per term — not a
formal open question. In production the transducer is compiled from the term, so
the datasheet function is the term's own evaluation and nothing separate is
trusted beyond the compiler.

## 18.6 Part E — out-of-type readings

`checkedProvide C ok seen ds` refuses every delivery whose payload fails `ok`
before Phase 17's deduplication and bound, and flags whether any was refused.
`checked_items_ok`, `checked_typed` (when `ok` implies typing, every item is a
`raw` — a malformed reading cannot enter), `checked_refused_iff` (the flag is
exact). A refused reading crosses as `none` at an optional Source or as a flag
beside it — a value the design reads (`exE_checked`: a boolean and 1000 refused
at tick 1, the Source `none`, `available` false); an internal diagnostic the
product never observes stays in the backend. No exception semantics; the
classification: a malformed frame, a NaN, an invalid code, an out-of-range count
are **provider refusals**; a profile whose raw type does not fit is **deployment
invalidity** (`Fits`, static); a value the design must react to is **semantic
state** (`opt`, a flag).

## 18.7 The profile, the assignment, the witnesses

`ProviderProfile ⟨entry, init, contract, assumedRange⟩` — the Phase-16 entry
with what this phase adds; `assignSource_profile_only`: the assignment reads the
Phase-13 profile and nothing else (`assignSource_origin_irrelevant` carried
over). `exF_two_providers`: the Phase-16 motion state fed by a batch provider
sampled through `chLatest` and by a scalar provider through the identity channel
has one `fb`, `settled` and `doneM` trace.

64 theorem-like declarations added (40 + 24); every one on
`propext`/`Quot.sound`; no `sorry`; the whole development 1 545 across 68 files;
`lake build` 71 jobs, clean, no warnings.

## 18.8 Models tried

| Model                                                    | Verdict                                                                                                                                                                                                                                     |
| -------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| a stateful channel term (memory in `tr`)                 | rejected again (FVD-0123 stands): the same value would transduce differently at two ticks; a machine below the reading is the provider's, above it the design's — `provider_state_movable` shows nothing is gained by memory in the channel |
| classifying provider state by implementation convenience | rejected: the criterion is visibility, with two formal facts (a provider cannot read the design; a parameter in the trace is the product's if the spec fixes it)                                                                            |
| a hidden provider clock                                  | rejected: `pc` is a `ClockId` the deployment names; `provisionSync_wellClocked` needs it                                                                                                                                                    |
| activation gated on the first sample                     | not a construction (schedules do not read inputs); the optional form is                                                                                                                                                                     |
| a default reading fabricated by the model                | rejected: `InitRep` is explicit, supplied or `none`                                                                                                                                                                                         |
| a second occurrence crossing on the input side           | rejected: `provisionWindow` is Phase 9a's window over the raw reading, one theorem                                                                                                                                                          |
| a profile range as evidence by declaration               | rejected: at the trusted level it is the assumption `A`, a hypothesis; the static and checked levels establish `A`                                                                                                                          |
| a proof language for `computes`                          | rejected: the field is a proof; `ofTerm` derives it, `computesBool` decides it at a finite type                                                                                                                                             |
| exception semantics for malformed readings               | rejected: refusal below the boundary, `none` or a flag above it                                                                                                                                                                             |
| a new kernel construct for any of the above              | none needed; no non-encodability witness                                                                                                                                                                                                    |

## 18.9 Claim audit

- _proved_: §18.1–18.6's theorems.
- _executed_: the examples of each part, the motion state under two providers.
- _definitional_: the three evidence levels as three assumptions; the
  state/visibility criterion's two facts.
- _design decision_: the classification of the five stateful cases (FVD-0154);
  the two initial policies (FVD-0155).
- _not established_: which bound or range a physical device needs (a deployment
  assumption, as in Phase 17); a `computes` check at an infinite raw type (a
  test, not a theorem); anything below the raw reading.

## 18.10 Verdicts

| Construct                                                           | Verdict                                                                                      | Decision |
| ------------------------------------------------------------------- | -------------------------------------------------------------------------------------------- | -------- |
| provider state as a Mealy machine below the reading                 | KEEP IN DEPLOYMENT (the provider's) — movable upstream at no semantic cost                   | FVD-0154 |
| memory in the channel term; a stateful primitive                    | REMOVE                                                                                       | FVD-0154 |
| the Source-side device clock (`provisionSync`, `provisionWindow`)   | KEEP IN DEPLOYMENT CONSTRUCTION — an explicit `sync` / window with an explicit initial value | FVD-0155 |
| a hidden provider clock; a fabricated initial reading               | REMOVE                                                                                       | FVD-0155 |
| commitment discharge at three evidence levels                       | KEEP AS THEOREMS — the assumption is the level                                               | FVD-0156 |
| a profile range as evidence by declaration                          | REMOVE                                                                                       | FVD-0156 |
| `computes` proof-carrying, derived from the term, decided at `bool` | KEEP                                                                                         | FVD-0157 |
| the checking provider; refusal as `none` / a flag                   | KEEP IN DEPLOYMENT; the flag is semantic state                                               | FVD-0158 |
| exception semantics                                                 | REMOVE                                                                                       | FVD-0158 |
