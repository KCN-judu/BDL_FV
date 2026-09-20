---
kind: report
phase: 4
area: core
date: 2026-09-15
status: current
---

# Phase 4 — Reactive Core

## 4.1 The weakest temporal model, and what was built on it

Start point: a **tick-indexed evaluation relation** `Ev Δ I t ρ e v` over the
existing expression language, with one new primitive `delay init e` and no new
types. Every declaration is a stream by _interpretation_; unresolved
declarations are the inputs (`I : DeclId → Nat → Value`); a realized declaration
is evaluated at tick `t` from its body; `delay init e` at tick `t+1` evaluates
`e` at tick `t`, and `init` at tick 0. That is the whole temporal kernel.
Everything the brief listed as a candidate primitive was then attacked for
eliminability (§4.4, §4.5).

Two typing constraints on `delay` came out of the totality proof, not out of
taste:

- **data-typed** — `τ.Data` (no arrow inside). A delayed closure would have to
  persist across ticks; the logical relation for closures is tick-indexed and
  cannot be transported. So temporal state stores values, not behaviour.
- **top level** — empty context. A delay under a lambda would re-evaluate its
  operand at the previous tick under an environment created at the current tick.
  So temporal state belongs to declarations; mappings are pointwise. (Lustre:
  `pre` lives in nodes, not in functions.) Consequence: function abstraction
  over _stateful_ behaviour (a reusable filter) needs instantiation into fresh
  declarations — a Phase-8 elaboration concern, not a kernel construct.

Both constraints also scoped a Phase-1 result: context weakening, hence inlining
a body under binders (`Unfolds.preserves_typing`), now carries a `DelayFree`
hypothesis. That is the domain of validity §7 asked for, not a weakening: the
Phase-1 statements are unchanged on the timeless fragment
(`Causal_iff_acyclic_of_delayFree`, `InstDependsOn_iff_DependsOn_of_delayFree`).

## 4.2 Results (claim strength in brackets)

| Result                                                                                                                                                                                                         | Lean                                                                                          | Strength                                                                                                                                               |
| -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------ |
| **`reactive_step_deterministic`**: one tick, one environment, one term — at most one value; no evaluation order is hidden                                                                                      | `Ev.det`                                                                                      | formally proved                                                                                                                                        |
| executable interpreter, sound for `Ev`; all traces below are `decide`-checked                                                                                                                                  | `evalF`, `evalF_sound`                                                                        | formally proved                                                                                                                                        |
| **`instantaneous_cycle_rejected`**: a strict cycle (through no lambda and no delay) has no value at any tick                                                                                                   | `Ev.not_of_strictCyclic`, `algebraic_loop_no_value`, `mixed_no_value`                         | formally proved                                                                                                                                        |
| **`delayed_cycle_is_causal`**: `A := delay 0 B, B := A` is structurally cyclic (no unfolding), causal, and runs at every tick; likewise self-delay                                                             | `delayed_loop_does_not_unfold`, `delayed_loop_causal`, `delayed_loop_runs`, `self_delay_runs` | formally proved                                                                                                                                        |
| **totality**: causal + globally well formed + well-typed inputs ⇒ every declaration has a value at every tick, related to its type                                                                             | `fundamental`, `reactive_total`, `Ev.red`                                                     | formally proved (logical relation, induction on (tick, rank, derivation))                                                                              |
| **`temporal_state_preserves_semantic_identity`**: with delays, closures and primitives present, if no signature announces `sem s` and no input carries `s`, no value at any tick carries `s`                   | `Ev.tag_provenance`, `temporal_state_preserves_semantic_identity`                             | formally proved                                                                                                                                        |
| `delay_preserves_type` / `temporal_state_preserves_dimension`: the rule is `delay : τ → τ → τ` for data `τ`; a backward difference over a time step has dimension `Length − Time` with no derivative primitive | `HasType.delay`, `delay_preserves_dimension`, `backward_difference_rate_typed`                | formally proved                                                                                                                                        |
| representation access is not stateful: `rep (delay i x) ≡ delay (rep i) (rep x)`; re-labelling a _stored_ tilt still needs the grant                                                                           | `rep_delay_commute`, `semantic_delay_typed_and_isolated`                                      | formally proved                                                                                                                                        |
| **unfolding vs stepping**: acyclic ⇒ causal; on wiring designs (no lambdas/variables) stepping the unfolded program equals stepping the references                                                             | `Causal.of_acyclic_bounded`, `unfolds_preserves_eval`                                         | formally proved; higher-order case not formalized (closure equivalence)                                                                                |
| `event_encoding_equivalent` (single domain) / `event_encoding_loses_multiplicity` (cross-domain observation)                                                                                                   | §7 of the experiment                                                                          | formally proved, both                                                                                                                                  |
| `count_desugars_to_state` etc. — `previous`, `hold`, `count`, `since`, `once`, `every`, `rise` as declaration graphs, each executed on a concrete input trace                                                  | `*_trace`, `ops_well_typed`, `ops_causal`                                                     | formally proved by execution (typing + trace); no general equivalence theorem, because there is no independent kernel definition to be equivalent _to_ |
| `statehandler_desugars_to_reactive_core` — activation, entry (rising edge), reset-on-entry local state, zero when inactive                                                                                     | `enter_trace`, `scoped_counter_trace`                                                         | formally proved by execution on one representative behaviour; see §4.11 for what this does _not_ establish                                             |
| missing initialization: undefined or nondeterministic first tick                                                                                                                                               | `first_tick_undefined_without_init`, `first_tick_nondeterministic_without_init`               | formally rejected by counterexample (toy relations)                                                                                                    |
| temporal changes (add/remove a delay, change init) are edits, not `DeclLeq`                                                                                                                                    | `temporal_change_is_edit`                                                                     | formally proved                                                                                                                                        |

## 4.3 Cycles: what replaces blanket acyclicity

Three reference sets now exist, and the distance between them is the content of
the causality result:

| Set          | Excludes                                                    | Used for                                      |
| ------------ | ----------------------------------------------------------- | --------------------------------------------- |
| `refs`       | nothing                                                     | structural dependency; `Unfolds` (Phase 1)    |
| `instRefs`   | operands of `delay`                                         | **`Causal`** — the positive criterion         |
| `strictRefs` | operands _and_ initial values of `delay`, and lambda bodies | the negative theorem `Ev.not_of_strictCyclic` |

- **Legal after delay exists**: any structural cycle every one of whose cycles
  passes through a delayed operand (`Causal`). Self-delay, mutual delayed
  recursion, multiple delays — all run.
- **Still illegal**: any instantaneous cycle, including one that is _partly_
  delayed (`Δmixed`: removing delayed edges must leave the whole graph acyclic).
- **Cycles through unresolved declarations** still cannot exist
  (`DependsOn.realized`): an input has no body.
- **The gap** (recorded, not hidden): `A := λx. A x` is not causal, yet
  `declRef A` evaluates — to a closure; only _applying_ it diverges
  (`lamloop_evaluates`). `Causal` is conservative for lambda-guarded cycles; the
  negative theorem covers strict cycles only. Likewise a cycle through a delay's
  _initial value_ is rejected by `Causal` (needed at tick 0) but exempt from the
  negative theorem.

Phase 1's `Unfolds.not_of_cyclic` is untouched: unfolding still fails on every
structural cycle. The change is in _which semantics matters_: `Unfolds` is a
correct optimization wherever it exists (`unfolds_preserves_eval`); `Ev` is the
semantics, and exists exactly on causal designs.

## 4.4 The minimal basis

One primitive. Every candidate was reduced to it plus `Prim`:

| Candidate                        | Reduction                                                           | Independent state? |
| -------------------------------- | ------------------------------------------------------------------- | ------------------ |
| `previous x` (with init)         | `delay init x` — literally                                          | no                 |
| `previous x` (without init)      | `delay none (some x)` — the absence is pushed to consumers as `opt` | no                 |
| `hold init ev`                   | `getD ev (delay init self)`                                         | no (self-delayed)  |
| `count ev`                       | `ite (isSome ev) (1 + delay 0 self) (delay 0 self)`                 | no                 |
| `since ev`                       | `ite (isSome ev) 0 (1 + delay 0 self)`                              | no                 |
| `once ev`                        | `delay false self ∨ isSome ev`                                      | no                 |
| `every n`                        | modulo counter over `delay`                                         | no                 |
| `rise b`                         | `b ∧ ¬ delay false b`, as an `opt bool`                             | no                 |
| `after`, `for`, `while`, `until` | comparisons over `since`/`once`/activation; not separately executed | —                  |

No candidate changes observable behaviour beyond what `delay` provides; none
changes causality (each adds exactly one delayed self-edge); none needs its own
storage. **State identity is structural**: a "cell" is a `delay` node in a
declaration body; it has no identifier because nothing refers to it — consumers
refer to the _declaration_. There is consequently no "two writers to one cell"
in this kernel; multiple writers arise only with actions (Phase 6).

## 4.5 Signal and Event

- **`Signal τ` as a type**: not added. Under the tick semantics it would be
  inhabited by exactly the terms of type `τ`; it distinguishes nothing and
  rejects nothing. What a signal type _will_ carry is the domain index
  `Signal[d]` of Phase 5 — information about which clock, not about being a
  stream. [engineering preference; no result needed the constructor]
- **`Event τ` vs `opt τ`**: in one domain an input delivers one value per tick
  by construction of `Input`, so an event input _is_ an `opt` stream;
  `event_encoding_equivalent` says the `opt` streams are exactly the
  multiplicity-≤1 streams. `event_encoding_loses_multiplicity` exhibits the
  counterexample — two occurrences in one observation interval — and it is
  observable only when a source ticks faster than its observer, i.e. across
  domains, which is where the paper itself puts it (§4.8.2). Consumption vs
  persistence (`count` vs `hold`) is a difference between declaration shapes,
  not between event and signal. **Verdict**: `Event` is not an independent
  single-domain kernel primitive; multiplicity is a Phase-5
  synchronization-policy question. [equivalence by proof under the stated
  observation model; the cross-domain case is explicitly not covered]

## 4.6 Initialization

`delay init e` with an explicit initial value. Alternatives:
`previous : τ → opt τ` is derivable and merely relocates the case analysis;
declaration- level initial state coincides with `delay` once state is per
declaration; "no initial value" is either undefined or nondeterministic at tick
0 (two toy relations). Initialization is _semantic_, not validation: without it
there is no unique first step to validate.

## 4.7 Determinism, and where nondeterminism will come from

`Ev.det` is unconditional. The sources the brief listed:

| Source                                    | Status                                                                                                                                      |
| ----------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------- |
| simultaneous events                       | impossible within a domain (one `opt` per tick); merging two _sources_ requires a chosen policy (`getD`-style left bias is one) — Phase 5/6 |
| undefined initialization                  | excluded by the rule (§4.6)                                                                                                                 |
| instantaneous cycles                      | no value rather than several (`Ev.not_of_strictCyclic`)                                                                                     |
| ambiguous state updates / multiple writes | no cells to write (§4.4); Phase 6                                                                                                           |

## 4.8 Answers to §27

| Question                                                | Answer                                                                                                                                                            |
| ------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 1. Minimal stateful/reactive basis?                     | `delay init e` (data-typed, top level) + the tick semantics `Ev`. Nothing else.                                                                                   |
| 2. Signal: type or execution-level?                     | Execution-level. `Ty` unchanged.                                                                                                                                  |
| 3. Event independently necessary?                       | No (single domain). `opt τ` streams; multiplicity deferred to Phase 5.                                                                                            |
| 4. Which temporal operators are sugar?                  | All of `previous`, `hold`, `count`, `since`, `once`, `every`, `rise` (executed); `after`/`for`/`while`/`until` by composition.                                    |
| 5. Legal cycles after delay?                            | Structural cycles whose every instantaneous path is broken by a delayed operand (`Causal`).                                                                       |
| 6. What replaces blanket acyclicity?                    | `Causal` = rank on `InstDependsOn`; `Acyclic` is its delay-free special case; `Unfolds` keeps its Phase-1 theorems as an optimization.                            |
| 7. Initialization?                                      | Explicit `init` on every `delay`; semantic, not validation.                                                                                                       |
| 8. Deterministic?                                       | Yes, unconditionally (`Ev.det`); total on causal well-formed designs (`reactive_total`).                                                                          |
| 9. State preserves isolation/provenance?                | Yes (`Ev.tag_provenance` + `constructs_granted`): state carries tags, never creates them.                                                                         |
| 10. Composes with dimensions?                           | Yes: `delay : q d → q d → q d`; rates arise from the ordinary algebra.                                                                                            |
| 11. StateHandler eliminable?                            | For the representative behaviours tested (activation, entry, reset-on-entry local state, inactive default): yes, as declaration shapes. See §4.11 for the caveat. |
| 12. Rejected constructs?                                | `Signal τ` in `Ty`; `Event τ` as a primitive; every temporal operator as a primitive; `previous` without init; delay under lambda; delay at function type.        |
| 13. Did the declaration/refinement architecture change? | No. `DeclInterface`, `DeclLeq`, `tyView` unchanged. Temporal edits are realization edits (FVD-0016 covers them).                                                  |

## 4.9 Critical remarks

- The basis is Lustre's `fby`/`pre` with an initial value, in a
  declaration-per-stream setting. Nothing here is new as a _calculus_. The
  contribution is the same shape as in Phases 2–3: the negative results
  (Signal-as-type, Event-as-primitive, operator-as-primitive all fail to earn a
  place) and the precise scoping of the earlier results.
- The totality proof required two restrictions on `delay` that the paper does
  not state (data-typed, top level). They are consequences of the synchronous
  model, not design choices, and the second one is what makes "temporal state
  belongs to declarations, mappings are pointwise" a theorem rather than a
  slogan.
- The desugarings are _executed_, not proved equivalent to anything: there is no
  independent kernel `count` to be equivalent to. What is established is that
  the designer-facing vocabulary is _expressible_ with the intended traces, and
  that each item is a self-delayed cycle — the class Phase 1 forbade and Phase 4
  licenses.
- `unfolds_preserves_eval` is restricted to wiring designs. For higher-order
  mappings the agreement holds up to closure equivalence and was not formalized.

## 4.10 The Phase-4 result (§30)

> The smallest stateful/reactive core from which BDL's designer-facing temporal
> behaviour can be derived is: the existing typed declaration language, one
> primitive `delay init e` restricted to data types at declaration top level,
> and a tick-indexed evaluation relation in which every declaration is a stream
> and unresolved declarations are inputs. Execution is deterministic (`Ev.det`)
> and total exactly on causal designs — those whose dependency graph is acyclic
> once delayed operands are removed (`Causal`, `reactive_total`,
> `Ev.not_of_strictCyclic`). State preserves semantic identity and provenance
> (`Ev.tag_provenance`), composes with dimensions by the ordinary typing rule,
> and needs no identity of its own. `Signal`, `Event`, and every temporal
> operator are derived.

Among tested designs; the lambda-guarded cycle gap and the cross-domain event
case are the stated boundaries.

## 4.11 What §14 did _not_ establish about StateHandler

One representative behaviour was elaborated and executed. Not covered: nested
handlers, event-latched activation with exit-wins, per-handler action policies,
and "persistent" (non-resetting) local state — the last is just the un-gated
`delay`, the first three involve actions/policies (Phase 6) or domain structure
(Phase 5). The claim is therefore: _the tested StateHandler behaviour is a
surface shape over gated, self-delayed declarations_; it is not "StateHandler is
only sugar" in general.
