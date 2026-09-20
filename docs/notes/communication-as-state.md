---
kind: note
phase: 16
area: surface
date: 2026-09-20
status: current
---

# Communication as state, catalogue profiles, and `assign`

For production and for a reader who will not open the Lean: why BDL models the
evolution of product meaning and not the transport of bits, what a device
package may contribute, and what a deployment `assign` is. It summarises the
[Phase 16 report](../reports/phase-16-communication-as-state-catalogue-profiles-and-the-deployment-only-assign.md),
`BDL/Surface/Assignment.lean`, `BDL/Experiments/CommunicationExamples.lean` and
the decisions FVD-0143 … FVD-0148.

## 1. The question and the answer

A realistic product — a host submitting motion work over TCP, motors reporting
position, velocity and faults over CAN, jobs queued and cancelled, telemetry —
looks like a system of messages. The question was whether BDL needs a `Message`,
`Event`, `Packet`, `Stream` or `Channel` primitive to describe it, or whether
_semantic state and its evolution_ is enough, with communication appearing only
at the physical boundary:

```text
physical / protocol observation
    → Source provision (a raw reading, a pure transducer)
    → BDL semantic state → behaviour → semantic desired state
    → output realization (a pure encoder, a raw command) → adapter
    → physical / protocol action
```

The answer is that the hypothesis survives every case tested, with the existing
kernel and no new primitive. The burden of proof was on the primitive: each case
was encoded and executed first, and a primitive would have been added only
against a concrete case the encoding could not represent without changing
observable behaviour. None was found.

## 2. What was encoded

Two designs of ordinary declarations (`CommunicationExamples.lean`), composed
into one controller:

- the **work queue**: `submit : list Job` (the jobs that arrived this tick,
  oldest first; a job is the pair `(JobId, delta)`), `cancel : opt JobId`,
  `done : bool`; state `queue : list Job` — FIFO, bounded by `take cap` —,
  `desired : Position`, `overflow : bool`;
- the **motion state**: `fb : opt (pos × vel × fault)` (a sample or none),
  `target`, `reset`, `ackNow`; state `age` (ticks since the last sample),
  `fresh`, `timedOut`, held `lastPos`/`lastVel`, `settled` (consecutive fresh
  in-tolerance samples), `doneM := settled ≥ 2`, a latched `fault`, `acked`.

And what each product-observable communication fact became:

| Communication fact                    | State                                                                 | Executed           |
| ------------------------------------- | --------------------------------------------------------------------- | ------------------ |
| two identical commands vs one         | two entries in `queue`; `desired` 20 vs 10 after the first completes  | `exA_multiplicity` |
| `A; B` vs `B; A`                      | `queue` order; `desired` 10 then 40 vs 30 then 40                     | `exB_ordering`     |
| several commands in one tick          | `submit` is a list; `[A, B]`, `[B, A]`, `[A]` are three queues        | `exC_same_tick`    |
| cancellation                          | `filter` by semantic `JobId`; the next job starts                     | `exD_cancellation` |
| a full queue                          | `take cap`; the refusal `overflow` is a boolean the product observes  | `exE_bounded`      |
| a retried submission with the same id | one job if the design deduplicates by id, two if it does not          | `exF_identity`     |
| freshness, timeout                    | `age`, `fresh := age < 3`, `timedOut := age ≥ 6`                      | `exG_freshness`    |
| completion after repeated samples     | `settled` counts fresh in-tolerance samples; `doneM := settled ≥ 2`   | `exH_settling`     |
| a fault that must be acknowledged     | `fault := (delay fault ∨ sampleFault) ∧ ¬reset`                       | `exI_fault_latch`  |
| an acknowledgement                    | `acked`, held until the target changes                                | `exJ_ack`          |
| the whole controller                  | queue drives `target`; `done := delay doneM`                          | `exQM_composed`    |
| commands from a faster host clock     | the Phase-9a window, flattened — nothing lost, in order               | `exK_cross_clock`  |
| a TCP sequence number, a per-frame id | discarded by the channel; **unobservable** (theorem)                  | `exL_theorem`      |
| two motors as one axis                | one output, one pair command `(p, p)`; or two realizations that agree | `exN_pair`         |

The design decides what a message _means_: the same retried submission is one
job or two depending on whether the design deduplicates by `JobId`
(`exF_identity`) — and that is the point. Identity that affects product
behaviour is in the state; identity that does not is discarded by the provider's
channel, and a theorem says nothing downstream can tell.

## 3. What is proved

All on `propext`/`Quot.sound`; names in `BDL/Surface/Assignment.lean`.

- **Source-side non-interference** (`two_providers_same_behavior`,
  `two_providers_same_outputs`): two providers of one design whose raw inputs
  induce the same semantic Source trace (`SameTrace`: agreement at every
  declaration other than the two raw ones, at every global tick) evaluate every
  term that mentions neither raw declaration alike, and every logical output
  alike. The raw types need not be related; a sequence number, a frame id, a
  retry token that the channel discards does not exist for the behaviour.
- **The replacement-invariance criterion** — a carrier replaced under the same
  semantic trace changes no behaviour (TCP → USB CDC, CAN → another transport,
  polling → interrupts) — is the conjunction of this theorem with Phase 14's
  `two_realizations_same_behavior` and Phase 15's `two_policies_same_commands`
  (FVD-0144).
- **The origin of a profile is unread** (`assign_indistinguishable`,
  `assignSource_origin_irrelevant`): a `builtin` entry and a `package` entry
  with one profile give one lowered design, one raw command relation, one
  adapter operation relation. A package contributes a profile satisfying the
  contract Phases 13/14 already state (`InputContract`, `OutputContract`), and
  the realizable world grows monotonically with the catalogue
  (`realizable_mono`, `provisionable_mono`); no typing, evaluation, causality or
  clock rule takes a catalogue (FVD-0145).
- **`assign` is deployment-only** (`assignOutput_behavior_unchanged`,
  `assignOutput_transparent`, `assignOutput_checked`,
  `assignSource_transparent`): `assign o using en` _is_ Phase 14's lowering,
  `assign s using en.channel i` _is_ Phase 13's provision; the design is
  literally the same off the fresh identities and is accepted by the unchanged
  judgments (FVD-0146).
- **Semantic admissibility and deployment feasibility are separate**
  (`admissible_iff`; `exQ_contract_not_feasible`):
  `Admissible ↔ OutputContract ∧ Feasible`; the pair profile satisfies the
  contract for `DesiredPos` on the Nano and on a one-pin board alike, and is
  feasible on one only (FVD-0147).
- **A paired axis** (`paired_commands_of_one_value`): two realizations of one
  output specify, at each tick, the two encoders' transfers of _one_ value; the
  prepare/prepare/commit order is the backend's per-tick commit below the
  adapter operation. No transaction primitive (FVD-0148).

## 4. What is not established

The provider's occurrence contract — that a `list raw` reading delivers the
occurrences since the previous tick in arrival order, that a transport retry is
delivered once, that two raw sources are merged into one order, that the batch
is bounded — is what the encodings rest on below the boundary and has no formal
statement (FVI-0029). The occurrence-preserving crossing to a _slower_ device
(the Phase-9a window mirrored into the output lowering) is a construction over
existing primitives that is not built (FVI-0024, amended). Backend support as a
second half of feasibility (production's `adapter.profile_unsupported`) is not
modelled. Priority ordering and telemetry were not executed; neither raises a
primitive question.

## 5. Verdicts

Event / message / stream types, a queue primitive, a transaction primitive:
REMOVE. Catalogue entries and origins: KEEP IN DEPLOYMENT DATA. `assign`: KEEP
IN DEPLOYMENT CONSTRUCTION — it is the lowering or the provision. Contract vs
feasibility: KEEP SEPARATE. Package management: OUT OF SCOPE.

## 6. Production guidance

What exists at `aa6e7f4` (read from the code, not the prose): five builtin
output profiles in `bdl-output::realization::profiles()` and no input profile;
the first adapters refuse a design with a Source (`adapter.inputs_unbound`);
collections are bounded by the design (ADR-0027); the five-declaration buffer
runs in every engine but has no surface form (ISS-0001); the device library is a
sketch (`docs/spec/concept-library.md`, "Device library (separate, later)").

The missing work is production's, not the language's (_design recommendation_,
each its own record):

1. **Source device profiles** — ISS-0016's other half: a catalogue entry
   `provides { raw, channels }` beside the output entry's
   `consumes { representation, encoder, raw }`, with the raw reading's
   occurrence contract (FVI-0029) stated in the entry: one item per semantic
   occurrence, arrival order, a per-tick bound.
2. **Package-supplied profiles** — a catalogue that lists builtin and packaged
   entries alike; admissibility checks the contract and the board and reports
   them separately (`deploy.realization_*` already does; a `deploy.provision_*`
   family would mirror it). The package name is display data on the Deploy page.
3. **`assign`** — a deployment spelling for both sides, persisted in the device
   body like `realization <id>`; the design graph does not change.
4. **The window's surface form** (ISS-0001) and a `list raw` Source reading
   bounded like a collection — the two ways several occurrences reach one tick.
5. **Backend protocol adapters** own frames, retries, sequence numbers and
   commit order; nothing of them reaches the design.

Nothing here is implemented; the correspondence page records Phase 16 as _not
consumed_.
