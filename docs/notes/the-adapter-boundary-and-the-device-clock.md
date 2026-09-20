---
kind: note
phase: 15
area: surface
date: 2026-09-20
status: current
---

# The adapter boundary and the device clock

For production and for a reader who will not open the Lean: what the formal
model now says about the step _after_ the raw command — the adapter's reading of
a command into an abstract sink operation, and the line it drives — and about
realizing an output in a device domain of its own. It summarises the
[Phase 15 report](../reports/phase-15-the-adapter-boundary-and-the-explicit-device-clock.md),
`BDL/Surface/Adapter.lean`, `BDL/Surface/DeviceClock.lean` and
`BDL/Experiments/AdapterExamples.lean`, and FVD-0140 … FVD-0142.

## 1. The question and the answer

Phase 14 stops at `RawCommand`. Production's first embedded adapter (ADR-0037)
consumes exactly those commands: `Tick.commands → adapter::apply → AdapterOp`,
with a policy — a finite duty in `0 ..= 255` rounds half up and is applied,
anything else is refused and the line holds, a driver that is not due leaves the
line — and a host-recorded operation trace. The smallest honest formal boundary
is that step and nothing below it: a **policy** reads the command, an
**operation** (`set`, `refused`, `held`) is the result, the **line** is the fold
of the operations. Nothing enters the kernel; the adapter is a relation over the
unchanged design, gated by the output's clock.

The explicit device clock that Phase 14 deferred survives: a realization lowered
through `sync` into a device domain keeps every preservation theorem and
corresponds to the command sampled at the last activation of the output's clock
strictly before — Phase 5's rule, inside Phase 14's correspondence.

## 2. What is proved

- `AdapterOp.det`; `adapter_of_sink` / `sink_of_adapter`: the operation at an
  active tick is the policy's reading of the value the lowered machine sink
  carries — `lower_correspondence` carried one step further.
- `adapter_downstream`, `two_policies_same_commands`: no policy and no refusal
  reaches the behaviour or the command; two adapters see one command trace.
- `Line.det`, `line_holds_on_refusal`, `line_holds_when_inactive`,
  `line_last_accepted`, `line_value_accepted`: reject-and-hold is a property of
  the fold; the line never carries a refused command.
- `lowerSync_*`: behaviour literally unchanged off `e`; refinement,
  single-driver, well-formed edges in the device domain, typing under the empty
  grant, causality with **no new instantaneous edge**, clocks with the
  transported operand in the output's clock; `lowerSync_correspondence`: the
  sampled command, or the initial representation's transfer before the first
  activation.

Executed: duty 102 set; duty 306 refused (line holds), clamped to 255 or applied
as 306 under other policies; an inactive tick holds; the device domain on odd
ticks sampling 102 then 107; the initial representation before the first
activation; slew-rate limiting as an upstream `delay` declaration with the
ramped raw trace.

## 3. What is not established

Below the operation: production's `f64` rounding, the HAL, the register, the
electrical world (FVI-0023 — the generated Rust's agreement with `AdapterOp` is
production-tested, never proved). A device that acknowledges; which initial
representation a device should hold (FVI-0024). A stateful realization witness
(FVI-0025). The atomic-frame criterion (FVI-0026). Output commitments (FVI-0027,
deferred).

## 4. Verdicts

Policy, operation, line: MACHINE/BACKEND, modelled as relations. The explicit
device clock: DEPLOYMENT CONSTRUCTION. Carrier as `ClockId`, reject-and-hold as
encoder state, a stateful realization primitive, `f64` rounding in the kernel:
REMOVE.

## 5. Production guidance

- ADR-0037's `duty8`, `AdapterOp` and `TickTrace.adapter` are the objects the
  model mirrors; the row in the correspondence page is _formally proved (model)
  · production-tested_ for the operation and _not established_ below it (_design
  recommendation_: keep the numeric policy a table with tests, as it is).
- A device at its own rate has a formal spelling now — `sync` into a device
  domain with an initial representation (FVD-0141) — but production has no
  spelling for a device domain and no device that needs one (ISS-0017); when one
  arrives, the deployment record should carry `dc` and `initRep`, never a
  carrier (_design recommendation_).
- Stateful adapters: implement slew, smoothing and hysteresis as behaviour (the
  designer's declarations), dithering and batching in the adapter; do not add
  state to `Encoder` (FVD-0142, _design recommendation_).
