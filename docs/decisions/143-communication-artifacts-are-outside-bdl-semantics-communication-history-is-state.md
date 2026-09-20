---
id: FVD-0143
legacy-id:
status: accepted
date: 2026-09-20
phase: 16
area: surface
supersedes: []
superseded-by: []
related: [FVD-0036, FVD-0048, FVD-0085, FVD-0140]
production: [ISS-0001/bears-on, ISS-0016/bears-on, ISS-0017/bears-on]
---

# FVD-0143: Communication artifacts are outside BDL semantics; communication history is state over the existing kernel

## Status

Accepted in Phase 16.

## Decision

BDL models semantic state and its evolution, not messages, packets, frames,
bytes or transport events. A communication's product-observable content is what
it does to state: an occurrence is `opt τ` at the tick, a batch is `list τ`,
occurrences across clocks are the Phase-9a window, a queue is a bounded list
under `delay`, an acknowledgement, a freshness age, a timeout, a latched fault
are booleans and counts under `delay`. Communication appears only at the two
physical boundaries — Source provision (Phase 13) and output realization with
its adapter (Phases 14–15). No `Event`, `Message`, `Packet`, `Stream` or
`Channel` type, no queue or transaction primitive, enters `Ty` or `Expr`.

## Alternatives rejected

A message/event type (for the fourth time, after FVD-0036, FVD-0048, FVD-0085);
a queue primitive; a transaction primitive (FVD-0148); transport identity in the
Source's type.

## Reason

The state-encoding audit of `BDL/Experiments/CommunicationExamples.lean`: every
case of a reduced auto_typer-style controller — multiplicity
(`exA_multiplicity`), ordering (`exB_ordering`), several occurrences in one
tick (`exC_same_tick`), cancellation by semantic id (`exD_cancellation`), a
bounded queue with an observable refusal (`exE_bounded`), semantic identity
(`exF_identity`), freshness and timeout (`exG_freshness`), settling over
repeated samples (`exH_settling`), fault latching (`exI_fault_latch`),
acknowledgement (`exJ_ack`), the composed controller (`exQM_composed`),
cross-clock delivery (`exK_cross_clock`), transport identity (`exL_theorem`,
`exL_executed`), the paired axis (`exN_pair`) — is executed with the existing
kernel; no non-encodability witness was found. The bar for a new primitive
(a minimal counterexample the existing state, list, clock, sync and buffer
machinery cannot encode without changing observable behaviour) was not met.

## Consequences

Production's Source device binding (ISS-0016) and the window's surface form
(ISS-0001) are the work; the language is not. What the thesis rests on below
the boundary is the provider's occurrence contract (FVI-0029) and the
occurrence-preserving crossing to a slower device (FVI-0024, amended).
