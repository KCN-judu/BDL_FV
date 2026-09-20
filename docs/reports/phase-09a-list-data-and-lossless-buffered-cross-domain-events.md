---
kind: report
phase: 9a
area: core
date: 2026-09-17
status: current
---

# Phase 9a — List data and lossless buffered cross-domain events

Research question (brief §0): can every lossless finite cross-domain event
window required by the Phase-5 semantics be expressed with the existing temporal
basis plus ordinary list data — and what is the smallest object-language
extension that makes it expressible? Files: `BDL/Core/ListData.lean`
(corollaries of the kernel extension), `BDL/Surface/Buffer.lean` (the
elaboration and Theorem M), `BDL/Validation/Capacity.lean`,
`BDL/Experiments/BufferAlternatives.lean`. Design note:
`docs/notes/lossless-buffered-cross-domain-events.md`.

## 9a.1 The extension

`Ty.list τ` in `Base.lean`; `Value.list` in `Reactive.lean`; six registered
operators `nil`, `cons`, `length`, `take`, `reverse`, `head`, typed through
`Prim.ty` (`length` yields `q 0`). `list τ` is data / sem-free iff `τ` is
(`list_data`, `list_semFree`). No typing rule, evaluation rule, or domain rule
was added: typing is primitive application, evaluation is `applyPrim`, and
`Clocked` has no list clause. The logical relation gained the clause "a list
value is related when each element is", which is what makes
`reactive_total`/`multi_domain_total` deliver a list of related elements at a
list type. Every exhaustive match over `Ty`/`Prim` in the core and the
experiments (`erase`, `denote`, `rename`, `eraseDim`, …) was extended and every
earlier theorem held without change of statement.

## 9a.2 Models tested (brief §2)

| model                | window summary | lossless? | witness                                                           |
| -------------------- | -------------- | --------- | ----------------------------------------------------------------- |
| A `latest`           | newest value   | no        | `latest_not_lossless`; general: `bounded_summary_not_lossless 1`  |
| B `count`            | length         | no        | `count_not_lossless` (`[1,2]` vs `[2,1]`, vs `[3,4]`)             |
| C `coalesce (+)`     | fold           | no        | `sum_not_lossless` (`[1,4]` vs `[2,3]`)                           |
| D fixed tuple (pair) | two newest     | no        | `modelD_not_lossless`; general: `bounded_summary_not_lossless 2`  |
| E list               | all, in order  | **yes**   | `buffer_lossless`; `window_to_list_preserves_order/_multiplicity` |

`bounded_summary_not_lossless k f`: any summary depending on the newest `k`
entries only identifies a `k`- and a `(k+1)`-entry window. Hence a lossless
summary is injective (`lossless_iff_injective`) and unbounded. Claim discipline:
the list is _the smallest general sequence representation tested_, not the only
possible one.

## 9a.3 The elaboration and the correspondence theorem

Five declarations over the Phase-5 log-and-cursor model
(`BDL/Surface/Buffer.lean`): `log @src := cons src (delay nil log)`;
`logD @dst := sync src nil log`; `seen := length logD`;
`cursor := delay 0 seen`; `window := reverse (take (seen − cursor) logD)`. The
Phase-5 tick-set result `buffer_from_log_and_cursor` is reused, not replaced.

| theorem                                                             | statement                                                                                                                                                  | status                                |
| ------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------- |
| A `list_data`                                                       | `(list τ).Data ↔ τ.Data`                                                                                                                                   | proved (`Iff.rfl`)                    |
| B `list_nil_red`, `list_cons_red`, `list_prims_red`, `list_compute` | constructors/eliminators inhabit their types and compute                                                                                                   | proved                                |
| C `list_eval_deterministic`                                         | `Ev.det` at lists                                                                                                                                          | proved (instance)                     |
| D `reactive_total_with_lists`                                       | a `list τ` declaration evaluates to a list of related elements                                                                                             | proved (instance of `reactive_total`) |
| E `multi_domain_total_with_lists`                                   | the `MEv` version                                                                                                                                          | proved                                |
| F `list_clock_conservative`, `list_direct_wire_rejected`            | `cons` around a read is clocked iff the read is; the direct cross-domain wire stays rejected                                                               | proved                                |
| G `window_to_list_preserves_order`                                  | window ticks strictly increasing; `i`-th entry = source value at `i`-th window activation                                                                  | proved                                |
| H `window_to_list_preserves_multiplicity`                           | for every predicate, entries satisfying it = window activations whose value does                                                                           | proved                                |
| I `latest_not_lossless`                                             |                                                                                                                                                            | counterexample                        |
| J `count_not_lossless`                                              |                                                                                                                                                            | counterexample                        |
| K `buffer_elaboration_well_typed`                                   | the five bodies have their declared types, any `Θ`/`G`, data `τ`                                                                                           | proved                                |
| L `buffer_elaboration_well_clocked`                                 | each body clocked in its declaration's domain; only `logD` crosses, through `sync`                                                                         | proved                                |
| **M** `buffer_window_correspondence`                                | `MEv S Δ I dst t [] window = list (map (I src) (windowTicks S src dst t))` for every `S`, `I`, `dst`, `t`, given `Realized` and `src` an input             | **proved**                            |
| N `buffer_lossless`                                                 | `Value.list` injective on windows                                                                                                                          | proved                                |
| O `sufficient_capacity_preserves`, `bounded_buffer_agrees`          | under sufficient capacity both drop policies are the identity                                                                                              | proved                                |
| P `insufficient_capacity_counterexample` (`negE`)                   | capacity 2 changes the tick-3 trace under either policy; `requiredCapacity` at horizon 30 = 3                                                              | executed (`decide`)                   |
| — `periodic_window_bound`, `periodic_capacity_sufficient`           | a window never exceeds one destination period; one period is sufficient at every horizon                                                                   | proved                                |
| — `requiredCapacity_sufficient`                                     | the computed capacity is sufficient for its horizon                                                                                                        | proved                                |
| — `buffer_typed`, `buffer_clocked`, `buffer_causal`                 | the elaborated design on the Phase-5 example passes the three checkers                                                                                     | executed                              |
| — `buffer_trace`                                                    | window at slow tick 3 = `[none, 1, 2]`, at 6 = `[none, none, none]`; `latest` = `2`                                                                        | executed                              |
| — `buffer_distinguishes_what_latest_identifies`                     | `Iev₁`/`Iev₂` equal under `latest`, differ under the window                                                                                                | executed                              |
| — `transport_trace`, `latest_transport_loses`                       | the Phase-8a component transport (sensor provides log, consumer requires it through a `sync` binding) yields the window; binding the event yields `latest` | executed                              |

All statements depend on `propext`/`Quot.sound` only (checked for all 73
Phase-9a theorems); `Classical.choice` was removed where it had entered through
`List.filter_eq_nil_iff` and `simp` arithmetic.

## 9a.4 Negative examples (brief §16)

|     | statement                                                                          | theorem                                                  |
| --- | ---------------------------------------------------------------------------------- | -------------------------------------------------------- |
| A   | same `latest`, different histories                                                 | `negA` (= `buffer_distinguishes_what_latest_identifies`) |
| B   | same `count`, different values or order                                            | `negB`                                                   |
| C   | `coalesce (+)` collides: `1+4 = 2+3`                                               | `negC`                                                   |
| D   | fixed pair cannot hold the three-entry window of tick 3                            | `negD`                                                   |
| E   | insufficient capacity changes the trace; sufficient does not                       | `negE`, `negE_bound`                                     |
| F   | same-rate, nominally different clocks still need transport (listing does not help) | `negF`                                                   |

## 9a.5 Minimality audit

| construct                                                                  | verdict                                                                                | evidence                                                                          |
| -------------------------------------------------------------------------- | -------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------- |
| `Ty.list τ` + `nil`/`cons`/`length`/`take`/`reverse`/`head`                | **KERNEL** (data type + registered operators)                                          | Theorem M is unwritable without sequence data; `bounded_summary_not_lossless`     |
| `Event τ`                                                                  | **REMOVE**                                                                             | an event is a data-typed declaration in a domain; the window is five declarations |
| `buffer`                                                                   | **SURFACE-DESUGAR**                                                                    | `BDL.Buffer.decls`; Theorems K, L, M                                              |
| `latest` / `hold` / `sample` / `drop` / `coalesce`                         | **SURFACE-DESUGAR**                                                                    | ordinary computation over `window` (`latest`, `count`, `sumNat`, `head`)          |
| capacity                                                                   | **VALIDATION**                                                                         | `CapacitySufficient`, `requiredCapacity`, `periodic_capacity_sufficient`          |
| overflow policy                                                            | **explicit** (`dropOldest`/`dropNewest`); only _reject deployment_ preserves semantics | O, P                                                                              |
| scheduler order / same-tick visibility / implicit overflow / effect system | **not added**                                                                          | unchanged strictly-before rule (`MEv`)                                            |

## 9a.6 Answer to the final question

Yes. For the supported fragment — any schedule, any tick, any input source,
unbounded list — `buffer_window_correspondence` states that the elaborated
`window` evaluates to exactly the Phase-5 window, and the list summary is
injective. Capacity is a separate, decidable validation obligation with a
closed-form bound for periodic schedules; overflow is never implicit. The
Phase-5 pending item is closed.

## 9a.7 What is not established

`src` must be an input (a realized source is routine but not threaded through
`log_at`); the operator set is the six needed; the component transport is
executed, not proved in general (it inherits Theorem J's single-domain
restriction).
