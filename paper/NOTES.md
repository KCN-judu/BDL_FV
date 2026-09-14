# Design changes in this revision

- Rewritten in academic English.
- Reorganized into an ACM-style research-paper structure.
- Promoted **signature-first authoring** to a core semantic principle.
- A Mapping Block is now defined by a type signature before its body, e.g. `?f : Tilt -> Brightness`.
- Formula/curve/example definitions are attachments to a Mapping Block, not separate execution nodes.
- Separated semantic nominal types from physical dimensions.
- Kept refinement/range/timing/device feasibility as validation obligations rather than core type equality.
- Restricted the first action-handler model to deterministic request/policy semantics instead of claiming a general algebraic-effect calculus.
- Made clocks explicit in reactive types and prohibited hidden resampling.
- Specified reset-on-entry semantics for local StateHandler temporal state.
- Added deterministic tick semantics, causality conditions, and preservation/determinism theorem statements with explicit proof assumptions.
- Added a designer-centered progressive authoring workflow and evaluation plan.

## Formal-semantics correction pass (2026-09-14)

- Removed `d/H` from the reactive type system. StateHandlers now preserve the enclosing domain and contribute only an activation mask plus reset semantics.
- Added activation stratification so a handler cannot depend instantaneously on values that only exist while that handler is active.
- Added a locally-finite global physical-time schedule for multi-domain execution and rewrote tick semantics over global steps rather than an undefined root clock.
- Made cross-domain synchronization a causal boundary: target ticks observe only source data committed at strictly earlier physical times.
- Corrected the equal-rate case: a cross-domain synchronizer does not degenerate to an identity wire; zero-latency behavior requires an explicit domain merge.
- Replaced generic event `coalesce` with `coalesce(mu)` requiring an explicit deterministic merge function, and made bounded-buffer capacity an engineering obligation.
- Added `Raw[r]` as a representation type and removed the unsound identification of raw device readings with `Q[0]`.
- Replaced the frequency/angular-velocity nominal-typing example with torque/energy; angle is retained as an explicit physical dimension where needed.
- Changed action signatures to request-only operation declarations `Delta(op) = P_op`; runtime requests are dependent pairs and no unused synchronous result type remains.
- Fixed the `Verified(P)` typesetting typo and weakened the workshop anecdote from a causal claim to evidence suggesting a representational problem.
- Removed the unresolved five-axis-printer TODO from the paper's claims; the example now motivates asynchronous outcomes without pretending that unreported timing data are evidence.
