---
kind: note
phase: 18
area: surface
date: 2026-09-20
status: current
---

# The Source-side boundary: provider state, the device clock, initialization, commitments, readings

For production and for a reader who will not open the Lean: what a Source
device may keep as state, when it samples, what a Source reads before the
device's first value, what a profile may promise about its values and at what
strength, and what becomes of a reading that is not a value. It summarises the
[Phase 18 report](../reports/phase-18-the-source-side-boundary-provider-state-device-clock-commitments-and-readings.md),
`BDL/Surface/SourceBoundary.lean` and the decisions FVD-0154 … FVD-0158.

## 1. One lemma

The behaviour sees a Source through its value trace and through nothing else
(`MEv.congr_at`): two designs that agree on every realization except at one
declaration, where the values agree at every tick, evaluate every term alike.
Every answer below is this lemma with two traces computed.

## 2. Provider state

A stateful transducer — a debouncer, a quadrature decoder, a filter — is a
Mealy machine whose step is a pure BDL term. It may run **below** the raw
reading (the provider delivers its output) or **above** it (one declaration
with `delay` over the physical reading, the Source realized from its output),
and the Source's trace is the same either way (`provider_state_movable`).
Placement is therefore not a semantic question. It is decided by
**visibility**: state whose parameter the product fixes, whose reset the
product commands or whose reading the product shows belongs upstream, where
the design and the simulation exhibit it; state that only interprets a
device's signal may sit in the provider. Two facts make the line sharp: a
provider cannot read the design — its state is a function of the raw stream
alone, and a channel term mentions no declaration, so the fault latch that
reads `reset` or the settling count that reads `target` cannot be a
provider's; and a parameter that changes the trace on the same physical stream
(the debounce threshold, a hysteresis band, a filter constant) is the product's
whenever the product's specification fixes it. Nothing can be hidden by the
placement, because the trace is what the behaviour reads; two providers with
one output stream give one behaviour (`stateful_providers_same_trace`).

| Case                                  | Placement                                                       |
| ------------------------------------- | --------------------------------------------------------------- |
| debouncing (contact bounce)           | provider; upstream when the threshold is the product's press time |
| quadrature decoding                   | provider (an edge from two consecutive phase readings)          |
| position accumulation, homing         | upstream (reads `reset`)                                        |
| sensor filtering                      | upstream when the lag is the product's; otherwise provider      |
| hysteresis for signal interpretation  | provider                                                        |
| semantic hysteresis (a thermostat)    | upstream                                                        |
| settling count, fault latch, timeout  | upstream — they read design values                              |

## 3. The device clock and the first value

A Source device that samples in its own domain `pc` is an explicit `sync` of
the raw reading into the Source's domain (`provisionSync`) — the input dual of
the output side's device clock: the Source carries the transfer of the reading
at the last activation of `pc` strictly before, or of the **initial value**
(`provisionSync_target`); the abstract design is unchanged
(`provisionSync_transparent`); no new instantaneous edge; well clocked with
the reading in `pc`; globally well formed. A Source whose every occurrence
matters — encoder edges, queued commands — crosses by Phase 9a's window over
the raw reading (`provisionWindow_target`): no second crossing, nothing lost.
The initial value is explicit and is one of two policies a profile declares:
a **supplied** raw value (the Source reads it until the first sample) or
**unavailable** (`none` at an optional raw type; the design reads that the
sensor has not spoken). A reading is never fabricated; activation gated on the
first sample is not a construction and is the optional form.

## 4. What a profile may promise, and at what strength

A Source's commitment (a temperature at most 450) is discharged by the
provisioned realization when every value it takes, under readings satisfying
an assumption `A`, has the property. The three evidence levels are three
assumptions and three ways of establishing them:

- **static** — `A` is typing at the raw type; the transducer alone guarantees
  the property (a saturating ADC);
- **checked** — `A` is a validation `ok` the provider applies to every
  delivery before deduplication and the bound; established by construction;
- **trusted** — `A` is a range the profile asserts of the device; nobody
  establishes it here, and the theorem carries it as a visible hypothesis.

A profile declaration alone is not evidence: at the trusted level it is exactly
the assumption named. The `computes` obligation — that the profile's transfer
function is what its term computes — is a proof in the model, derivable when
the function *is* the term's evaluation (`Channel.ofTerm`), decidable at a
finite raw type (`computesBool`); a separately supplied function at an
infinite type is a claim to test, and production compiles the term, so nothing
separate is trusted beyond the compiler.

## 5. Readings that are not values

A malformed frame, a NaN, an invalid code, a count outside the declared range
never become a semantic value: the checking provider refuses the delivery
(`checkedProvide`) and every item it delivers is typed by construction
(`checked_typed`). The refusal crosses as `none` at an optional Source or as
a flag beside it — semantic state the design reads (`available`), if the
product must react — or stays a backend diagnostic if it must not. No
exception semantics. A profile whose raw type does not fit the Source is
deployment invalidity, decided statically.

## 6. The profile and the assignment

A package-provided Source profile may carry the transducer, an internal
machine, the initial policy, the delivery contract, an assumed range and
requirements (`ProviderProfile`); the assignment reads the Phase-13 profile
and nothing else (`assignSource_profile_only`), so `assign` stays
deployment-only and a provider replaced under the same trace changes nothing.

## 7. Production guidance

The Source realization slice found in flight in the production tree (a
catalogue crate, `DeviceKind::DigitalInput`, `DeviceBinding.source` /
`provider`, `InputProfileId`) should carry, per input profile (_design
recommendation_): the delivery contract (`sampled` or `batch { cap }`, Phase
17) and, from this phase, the **initial policy** (`supplied <raw>` or
`unavailable`, the latter forcing an optional Source type), the **validation**
`ok` applied by the adapter with the refusal surfaced as `none` or a flag, the
**evidence level** of each declared range (`static` from the transducer,
`checked` by the adapter, `trusted` by the vendor — shown as such on the Deploy
page, never collapsed), and, when the device samples in its own domain, the
**provider clock** as a deployment `ClockId` with the `sync` lowered as the
output side lowers its device clock. Provider-internal state (a debouncer's
counter) is the adapter's when the profile declares it and the product does
not name its parameter; otherwise the designer writes it. Nothing here is
implemented; the correspondence page records Phase 18 as _not consumed_.
