---
kind: note
phase: 9a
area: core
date: 2026-09-17
status: current
---

# Lossless Buffered Cross-Domain Events with Ordinary List Data

_A formal note on Phase 9a of the BDL development (`BDL/Core/ListData.lean`,
`BDL/Surface/Buffer.lean`, `BDL/Validation/Capacity.lean`,
`BDL/Experiments/BufferAlternatives.lean`)._

## 1. The open problem

Phase 5 established the multi-domain semantics on one transport primitive,
`sync src init e`: the value of `e` in domain `src` at its last activation
strictly before now. It also showed (`opt_loses_multiplicity_under_sync`) that
this primitive, applied to an event-valued declaration, is a _zero-order hold_:
a slow consumer of a fast event source sees the last value only, so two fast
events in one slow period collapse to one and an event followed by a quiet tick
is dropped. The phase then proved, on tick sets, that the destination's _window_
— the source activations since the destination's previous activation — equals
the source's accumulated log read now minus the log length read at the previous
destination activation (`buffer_from_log_and_cursor`). Two single-instant reads,
a `sync` of a log and a `delay` of a cursor, suffice. What Phase 5 could not do
was _write_ the log in the object language: the kernel had no sequence data.
That is the stated limitation Phase 9a closes.

## 2. The extension: `Ty.list`, and nothing else

The object language gains one type former, `Ty.list τ`, one value form,
`Value.list`, and six registered operators, typed through the ordinary `Prim.ty`
table:

| operator    | type                    |
| ----------- | ----------------------- |
| `nil τ`     | `list τ`                |
| `cons τ`    | `τ → list τ → list τ`   |
| `length τ`  | `list τ → q 0`          |
| `take τ`    | `q 0 → list τ → list τ` |
| `reverse τ` | `list τ → list τ`       |
| `head τ`    | `list τ → opt τ`        |

A list is data exactly when its elements are (`list_data`), so it may be delayed
and transported under the existing rules. There is no list typing rule beyond
primitive application, no list evaluation rule beyond `applyPrim`, and no list
clause in the domain judgment (`list_clock_conservative`): wrapping a
cross-domain read in `cons` is rejected exactly as the bare read is
(`list_direct_wire_rejected`).

Every earlier theorem holds unchanged. Determinism, totality in one and many
domains, provenance, erasure and the renaming lemmas are generic in values and
primitives; the list corollaries (`list_eval_deterministic`,
`reactive_total_with_lists`, `multi_domain_total_with_lists`) are instances, not
new proofs. The logical relation's list clause — a list value is related when
each element is — is what totality delivers: a declaration of type `list τ`
evaluates to a list of related elements.

## 3. The buffer as five declarations

With list data the Phase-5 construction is written directly:

```text
log     @src :  cons src (delay nil log)             -- source-side accumulator
logD    @dst :  sync src nil log                     -- the log, transported
seen    @dst :  length logD                          -- log length now
cursor  @dst :  delay 0 seen                         -- log length at the previous activation
window  @dst :  reverse (take (seen − cursor) logD)  -- the new entries, oldest first
```

`log` lives in the source domain and grows by one entry per source activation.
`logD` is the one cross-domain read, an explicit `sync` with the explicit
initial value `nil`. The other three are destination-local arithmetic over the
transported log. Nothing new is evaluated.

The elaboration is well typed in any environment with the declared types
(`buffer_elaboration_well_typed`) and well clocked with `src`, `log` in the
source domain and the rest in the destination
(`buffer_elaboration_well_clocked`); the only cross-domain reference is the
`sync`.

**Theorem M** (`buffer_window_correspondence`). For every schedule, every input,
every destination domain and every tick,

```text
MEv S Δ I dst t [] window = list (map (I src) (windowTicks S src dst t))
```

whenever the six declarations are realized as above and `src` is an input. The
window declaration evaluates to exactly the source's values at the Phase-5
window ticks, in order and with multiplicity. The statement makes no assumption
on the schedules and holds at activation and non-activation ticks alike; the
strictly-before rule is preserved, so the window at `t` contains source
activations `< t` only. The proof is by the Phase-5 tick-set identity together
with a characterization of the log at every tick (`log_at`): the source's value
now followed by its values at every earlier activation, newest first.

## 4. Losslessness, and why a bounded summary cannot have it

A _summary_ is any function from the window's value list to a value. It is
_lossless_ when injective — when the window can be recovered from it. The list
summary is lossless by injectivity of the `list` constructor
(`buffer_lossless`); its entries are indexed by the window ticks in strictly
increasing order (`window_to_list_preserves_order`), and for every property of
values the number of entries with the property equals the number of window
activations whose value has it (`window_to_list_preserves_multiplicity`).

The models the brief asked to test:

| model            | keeps            | lossless? | witness                                                  |
| ---------------- | ---------------- | --------- | -------------------------------------------------------- |
| A `latest`       | the newest value | no        | `[1, 2]` vs `[2]` — `latest_not_lossless`                |
| B `count`        | the length       | no        | `[1, 2]` vs `[2, 1]`, vs `[3, 4]` — `count_not_lossless` |
| C `coalesce (+)` | a fold           | no        | `[1, 4]` vs `[2, 3]` — `sum_not_lossless`                |
| D fixed pair     | the two newest   | no        | `[0, 1, 2]` vs `[1, 2]` — `modelD_not_lossless`          |
| E list           | everything       | **yes**   | `buffer_lossless`                                        |

The general statement behind A and D is `bounded_summary_not_lossless`: a
summary that depends only on the newest `k` entries, for any fixed `k`,
identifies a `k`-entry window with a `(k+1)`-entry window. So if multiplicity
and order are observable — and Phase 5 showed they are — no summary of bounded
size preserves them; unbounded sequence data is required. The claim is not that
the list is the only such representation. It is that among the representations
tested an ordinary list is the smallest general one, and that any lossless one
must be injective on windows and hence unbounded in size
(`lossless_iff_injective`).

## 5. Capacity is a validation obligation

The kernel model is the unbounded log. A deployment has finite memory and must
show that no window exceeds its capacity. `CapacitySufficient S src dst cap T`
states that every window up to horizon `T` fits; it is decidable for a finite
horizon, and `requiredCapacity` computes the least sufficient value with a proof
(`requiredCapacity_sufficient`). For periodic schedules the horizon is
unnecessary: a window never holds more than one destination period of source
activations (`periodic_window_bound`), so one period is a sufficient capacity at
every horizon (`periodic_capacity_sufficient`).

Overflow policies are explicit functions of the unbounded window —
`dropOldest cap`, `dropNewest cap` — and under a sufficient capacity both are
the identity (`sufficient_capacity_preserves`, `bounded_buffer_agrees`). Under
an insufficient capacity they change the trace: on the running example the
three-entry window at tick 3 becomes two entries under either policy, capacity 2
fails the check at horizon 6, and the required capacity at horizon 30 is 3
(`negE`). Consequently the only overflow policy that preserves the kernel
semantics is to _reject the deployment_; dropping is a semantic change and must
be written by the designer as ordinary computation over the window if it is
wanted.

## 6. `Event` is still not a kernel type

An event stream is a data-typed declaration in a domain; an occurrence is its
value at an activation; a lossless cross-domain view of it is the five
declarations above; `latest`, `count`, `coalesce`, `drop`, `sample` are ordinary
computations over `window`. None of this needs an `Event` type, a buffer
primitive, a scheduler order, same-tick visibility, an implicit overflow rule or
an effect system, and none was added. The answer to the Phase-5 question is
therefore complete: every finite cross-domain window the Phase-5 semantics
defines is expressible with the existing temporal basis plus ordinary list data,
and Theorem M proves it for the whole supported fragment (any schedule, any
tick, any input source).

## 7. The component view

The buffer is also a Phase-8a system with no new binding kind
(`BDL/Experiments/BufferAlternatives.lean`, §4). A _sensor_ component provides
its event and its log, written against a clock parameter; a _consumer_ component
requires the log and computes `seen`, `cursor`, `window`. Instantiated in `fast`
and `slow` and bound through an ordinary transported binding with initial value
`nil`, the flattened system's window evaluates to `[none, some 1, some 2]` at
tick 3 and `[none, none, none]` at tick 6 (`transport_trace`), whereas binding
the event itself through `sync` yields `some 2` at tick 3 and has lost the
tick-1 event (`latest_transport_loses`). The design decision "buffer or not" is
thus a choice of _which provided port to bind_, visible in the interface, and
not a property of the transport.

## 8. What is not established

- Theorem M assumes `src` is an input; a realized source needs the source's own
  evaluation to be threaded through `log_at`, which is routine but not done.
- The list operators are the six needed for the buffer and the tested policies;
  a designer-facing library (`map`, `filter`, folds) is surface and was not
  tested.
- Capacity is proved for the exact window; a deployment that reads the log at a
  coarser cadence than the destination activation needs its own bound.
- The component-transport example is executed, not proved in general: it
  instantiates Theorem M through `flatten`, whose semantic preservation (Phase
  8a's Theorem J) is stated for the single-domain fragment.
