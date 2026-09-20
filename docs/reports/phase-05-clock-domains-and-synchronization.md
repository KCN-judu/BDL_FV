---
kind: report
phase: 5
area: core
date: 2026-09-15
status: current
---

# Phase 5 — Clock domains and synchronization

## 5.1 The time model, and what had to be explicit

The smallest model that distinguishes behaviour (§16): one global base tick and
a **schedule** `S : ClockId → Nat → Bool` saying at which global ticks each
domain activates. No physical time, no timestamps, no rates in the kernel: a
period `n` is validation data that _induces_ the schedule `t % n = 0`
(`Sched.periodic`). Domain-local time is not a separate counter; it is the
sequence of a domain's activations.

What must be explicit for cross-rate behaviour to be deterministic and
unambiguous turned out to be exactly three things:

1. **nominal clock identity** on every non-agnostic declaration
   (`ClockEnv Κ : DeclId → Option ClockId`);
2. **one transport primitive** `sync src init e` with a fixed read rule — _the
   last activation of `src` strictly before now_ — and an explicit initial
   value;
3. a **domain judgment** `Clocked` rejecting every other cross-domain reference.

Nothing else: no numeric rate, no timestamp, no scheduler order, no second state
mechanism.

## 5.2 Results (claim strength in brackets)

| Result                                                                                                                                                                                                                                                                        | Lean                                                                           | Strength                                                                                                                       |
| ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------ |
| **`single_domain_embedding`**: under the always-active schedule `MEv` _is_ `Ev`, in every domain — Phase 4 is the one-domain special case, not a replaced machine                                                                                                             | `single_domain_embedding`                                                      | reduction by proof                                                                                                             |
| **`delay_is_sync_own`**: `delay init e` in domain `c` is `sync c init e`; the domain judgment agrees                                                                                                                                                                          | `delay_is_sync_own`, `clocked_delay_iff_sync_own`                              | equivalence by proof — cross-domain transport is the Phase-4 state basis with its domain made explicit; no new state mechanism |
| **`multi_domain_step_deterministic`**: no evaluation order between simultaneously active domains appears in the semantics                                                                                                                                                     | `MEv.det`                                                                      | formally proved                                                                                                                |
| **`cross_domain_direct_wire_rejected`** (Counterexample A's positive half): same value type does not imply connectability across domains — the temporal analogue of Phase 2's representation ≠ identity                                                                       | `cross_domain_direct_wire_rejected`, `both_well_typed` (typing is blind to it) | formally proved                                                                                                                |
| **`explicit_transport_accepted`**; a domain-agnostic pure mapping serves two domains with one declaration                                                                                                                                                                     | `explicit_transport_accepted`, `transport_trace`                               | formally proved (judgment + execution)                                                                                         |
| **Counterexample A**: the unpolicied wire is ambiguous — latest / first / count / sum of the window `[0,1,2]` are all type-correct and all differ                                                                                                                             | `unpolicied_wire_ambiguous`                                                    | formally proved                                                                                                                |
| **Counterexample B / `equal_rate_not_same_domain`**: a clone with the identical schedule is a different domain (wire rejected); a same-rate domain shifted in phase reads different values through `sync`                                                                     | `equal_rate_not_same_domain`, `phase_matters`                                  | formally proved                                                                                                                |
| **`delay_is_domain_relative`**: a slow `delay` reads three global ticks back, a fast one reads one, same syntax                                                                                                                                                               | `delay_is_domain_relative`                                                     | formally proved by execution                                                                                                   |
| **Counterexample E**: moving a producer to another domain, or pinning an agnostic mapping to one, invalidates unchanged clients                                                                                                                                               | `clock_change_invalidates_clients`, `clock_assignment_invalidates_clients`     | formally proved                                                                                                                |
| **Counterexample F**: a transport that lets simultaneously active domains see each other's _current_ values makes the scheduler order observable — two priorities, two outputs. `MEv`'s strictly-before rule has no such parameter                                            | `scheduling_order_observable` (toy `MEvLE`)                                    | formally rejected by counterexample (for the same-tick-visible alternative)                                                    |
| **`transport_preserves_semantic_identity`**, **`transport_preserves_dimension`**: `Tilt@fast → Tilt@slow` and `q Length@fast → q Length@slow` typed; a crossing authorizes neither `Tilt → MotorAngle` (grant) nor `q Length → q Time`                                        | `transport_preserves_semantic_identity_and_dimension`                          | formally proved                                                                                                                |
| semantic form: with crossings present, a concept no signature announces never appears in any domain at any tick                                                                                                                                                               | `MEv.tag_provenance`, `sync_preserves_semantic_identity`                       | formally proved                                                                                                                |
| **`transport_breaks_instantaneous_dependency`**: `instRefs (sync _ i e) = instRefs i` — a transport reads strictly earlier, so cross-domain edges are never instantaneous; causality is the _unchanged_ `Causal Δ`                                                            | `Expr.instRefs`, `mfundamental`                                                | by definition + formally proved consequence                                                                                    |
| **`multi_domain_total`**: causal + globally well formed + well-typed inputs ⇒ a value in every domain at every tick, hence deterministic first activation with the explicit initial values                                                                                    | `multi_domain_total`                                                           | formally proved (same induction as Phase 4: `prevAct_lt`)                                                                      |
| **Counterexample C**: `opt` under zero-order hold loses events — two fast events vs one are indistinguishable at the slow tick, and a single event followed by a quiet fast tick is _dropped_                                                                                 | `opt_loses_multiplicity_under_sync`                                            | formally rejected by counterexample (for `sync` as event transport)                                                            |
| **`buffer_from_log_and_cursor`**: the exact window of source occurrences since the destination's previous activation equals the log read at `t` minus the log length read at `t₀`: two single-instant reads, i.e. `sync` of a source-side accumulator and `delay` of a cursor | `buffer_from_log_and_cursor`, `window_example`                                 | formally proved (on tick sets); object-language realization: Phase 9a (`buffer_window_correspondence`)                         |
| policies as functions of the window: `latest`, `count`, `count+latest` each identify distinct windows; only the list is injective                                                                                                                                             | `policies_lose_information`                                                    | formally proved                                                                                                                |
| clocked types force clock polymorphism for pure mappings; the judgment does not                                                                                                                                                                                               | `clocked_type_forces_polymorphism` (toy)                                       | engineering preference, with a formal witness of the cost                                                                      |

## 5.3 Where clock information lives (§7, §24, §25)

| Placement                                    | Verdict                                                                                                                                                                                                     |
| -------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| A — in `Ty` (`Signal[c, τ]`)                 | rejected: every pure mapping would need clock polymorphism (`clocked_type_forces_polymorphism`), and nothing it rejects is missed by the judgment. Not unsound; unnecessary. [engineering preference + toy] |
| B — declaration metadata + separate judgment | **this is the design**: `ClockEnv Κ` keyed by `DeclId`, `Clocked`                                                                                                                                           |
| C — execution environment only               | insufficient: typing would accept the direct wire and the semantics would be _ambiguous_, not merely undefined (`unpolicied_wire_ambiguous`); the check must exist somewhere static                         |
| D — separate domain judgment                 | = B; the judgment is the check, the projection is its data                                                                                                                                                  |

**Does `DeclInterface` change?** The clock is _interface data_ in every formal
sense that matters: clients' validity depends on it (Counterexample E), it is
frozen under refinement, changing it is an edit. It is stored as the projection
`Κ` rather than as a fourth record field, exactly as the concept representation
is stored in `Θ` rather than in `Ty.sem`. So the public interface of a
declaration is now `expectedType × commitments × clock`, with the third
component held in `ClockEnv`; `DeclInterface` the record is unchanged, `tyView`
is unchanged, typing is unchanged. Whether to fold `Κ` into the record is churn,
not semantics; recorded as FVD-0046.

**Was a new environment projection required (§25)?** Yes — by a formal
dependency, not symmetry: the domain judgment must resolve a reference's domain,
and nothing already in `Δ.tyView`, `Θ`, or `G` carries it.

## 5.4 Event transport (§11–§12)

`opt τ` remains the right _value_ representation of "at most one occurrence per
activation" (Phase 4). What Counterexample C shows is that `sync` — a
single-instant read — is the wrong _transport_ for events, not that `opt` is the
wrong type. The window model separates the two:

- a destination should be able to see the source's occurrences at the source
  activations _since its own previous activation_ (the window);
- `buffer_from_log_and_cursor` proves the window is derivable from two
  single-instant reads — `sync` of a source-side accumulated log and `delay` of
  the log length seen at the previous destination activation;
- `policies_lose_information` shows what each policy keeps: `latest` and `count`
  and `count+latest` are lossy; the list is not. Order within the window is the
  source's activation order and is preserved by the list.

So: **multiplicity and order are observable; buffering is required to keep them;
buffering is a structured use of the existing state basis plus list data; a
bound on the buffer is a validation obligation** (an unbounded log is the kernel
model, capacity/overflow is deployment). `Event` as a distinct semantic notion
is still not needed; what would be needed to _write_ the buffer in the object
language is `Ty.list` and a few list operators — plain data, deferred (done in
Phase 9a: `buffer_window_correspondence`).

## 5.5 Initialization, `delay`, and causality across domains

- Every `sync` carries an explicit `init`, used at a destination activation with
  no earlier source activation (`transport_trace` at tick 0). First activation
  is deterministic by `MEv.det` and exists by `multi_domain_total`.
- `delay` means _previous activation of the current domain_
  (`delay_is_domain_relative`), and is literally `sync` at that domain.
- Every crossing costs at least one destination-visible step: a source active at
  the same global tick is _not_ seen (strictly-before). This is a choice with an
  observable alternative (Counterexample F); the alternative makes scheduler
  order semantic. "Synchronous subdomains evaluated in one instant" are, in this
  model, the _same_ domain.
- Causality is unchanged: `Causal Δ` on `instRefs`, where `sync`'s operand is
  not instantaneous. No cross-domain cycle can be instantaneous.

## 5.6 Refinement vs edit vs validation (§23)

| Operation                                       | Kind                                                                                                  | Witness                                               |
| ----------------------------------------------- | ----------------------------------------------------------------------------------------------------- | ----------------------------------------------------- |
| unclocked (agnostic) → assigned domain          | edit                                                                                                  | `clock_assignment_invalidates_clients`                |
| domain A → domain B                             | edit                                                                                                  | `clock_change_invalidates_clients`                    |
| rate 100 Hz → 50 Hz                             | validation-only: changes the induced schedule, hence observed values, but no client's well-formedness | `Sched.periodic`; nothing in `Clocked` mentions rates |
| synchronization policy change (`sync` → buffer) | realization edit                                                                                      | FVD-0016                                              |
| buffer capacity change                          | validation-only                                                                                       | §5.4                                                  |

## 5.7 Answers to §35

| Question                                   | Answer                                                                                                                                                                                                                              |
| ------------------------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 1. Explicit clock identity required?       | Yes: without it the direct wire is ambiguous (A) and equal rates cannot distinguish domains (B).                                                                                                                                    |
| 2. Identity distinct from rate?            | Yes: `equal_rate_not_same_domain`, `phase_matters`; rates are not in the kernel.                                                                                                                                                    |
| 3. Where does clock information live?      | `ClockEnv Κ` (per declaration, interface-level) + the judgment `Clocked`.                                                                                                                                                           |
| 4. Does `DeclInterface` change?            | Semantically the interface gains a frozen clock component; the record is unchanged (held in `Κ`), FVD-0046.                                                                                                                         |
| 5. Clocks in `Ty`?                         | No (`clocked_type_forces_polymorphism`).                                                                                                                                                                                            |
| 6. Minimal transport primitive?            | `sync src init e`; `delay` is its own-domain instance.                                                                                                                                                                              |
| 7. Derived/surface policies?               | `hold`/`latest` = `sync`; `sample` = `sync` at the destination's activation; `buffer` = `sync` of a log + `delay` of a cursor (+ list data); `drop` = window head; `coalesce μ` = fold of the window. All derived given the window. |
| 8. Is `opt τ` still sufficient for events? | As the per-activation value, yes; as the _transported_ value under `sync`, no (C).                                                                                                                                                  |
| 9. What exactly is missing?                | Multiplicity and order across a crossing — i.e. a window read, which is buffering; not a distinct Event semantics.                                                                                                                  |
| 10. Transport initialization?              | Explicit `init` on every `sync`, used at the first activation.                                                                                                                                                                      |
| 11. `delay` in multiple domains?           | Previous activation of the expression's own domain (`delay_is_domain_relative`).                                                                                                                                                    |
| 12. Generalized causality?                 | The same `Causal Δ`; transports are never instantaneous.                                                                                                                                                                            |
| 13. Deterministic?                         | Yes (`MEv.det`), total on causal designs (`multi_domain_total`).                                                                                                                                                                    |
| 14. Semantic provenance preserved?         | Yes (`sync_preserves_semantic_identity`).                                                                                                                                                                                           |
| 15. Dimensional correctness preserved?     | Yes, by the typing rule of `sync`.                                                                                                                                                                                                  |
| 16. Validation-only timing concerns?       | numeric rates/periods, drift, jitter, latency, buffer capacity/overflow, value age.                                                                                                                                                 |
| 17. Refinement vs edit?                    | All clock changes are edits; rate and capacity changes are validation-only (§5.6).                                                                                                                                                  |

## 5.8 Critical remarks

- The strictly-before rule is Lustre/Esterel's "a signal computed this instant
  is visible next instant" applied across domains, and the paper's own
  causal-boundary convention. What Phase 5 adds is the _reason_ it is the right
  default: the alternative makes scheduler order semantic (Counterexample F),
  and the strict rule makes cross-domain causality free.
- `delay_is_sync_own` is the phase's cleanest result and also its most
  uncomfortable: it says the Phase-4 "only state primitive" was already the
  transport primitive with its domain implicit. The honest reading is that the
  kernel has one temporal primitive — _read a domain at its previous activation_
  — and Phase 4 only saw its diagonal.
- The buffer derivation is proved on tick sets, not in the object language.
  Writing it there needs `Ty.list`; until then "buffering needs no new
  primitive" is a semantic-level reduction. (Closed in Phase 9a.)

## 5.9 The Phase-5 result (§37)

> The smallest clock-domain and synchronization mechanism is: nominal `ClockId`
> on every non-agnostic declaration (interface-level, frozen), a schedule
> outside the design saying when domains activate, one transport primitive
> `sync src init e` reading the source at its last activation strictly before
> now with an explicit initial value, and a domain judgment rejecting every
> other cross-domain reference. `delay` is `sync` at the own domain; the
> single-domain semantics embeds exactly; evaluation is deterministic and total
> on the unchanged causality condition; semantic identity, provenance and
> dimensions pass through transport untouched; event buffering is derivable from
> the same two reads plus list data, with capacity left to validation.

Among tested designs; the same-tick-visible alternative and clocked types were
rejected for stated, mechanized reasons; the object-language buffer was the
stated pending item, closed in Phase 9a.
