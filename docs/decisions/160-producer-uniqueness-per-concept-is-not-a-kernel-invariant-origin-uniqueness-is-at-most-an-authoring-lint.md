---
id: FVD-0160
legacy-id:
status: superseded
date: 2026-09-21
phase: 19
area: experiments
supersedes: []
superseded-by: [FVD-0161]
related: [FVD-0159, FVD-0052, FVD-0066, FVD-0067]
production: [ADR-0034/bears-on]
---

# FVD-0160: Producer uniqueness per concept is not a kernel invariant — signature-uniqueness is refuted by bindings and transports, and origin-uniqueness (`MkUnique`) is at most an authoring-level lint with a component boundary rule

## Status

Accepted in Phase 19.

## Decision

Neither `SigUnique Δ` (at most one declaration announcing `C` in result
position) nor `MkUnique Δ` (at most one declaration originating `C` — a `mk C`
in its body or an unresolved Source of `C`) is a judgment of the kernel, a
condition of `GlobalWF`, or a hypothesis of any kernel theorem. `MkUnique` may
be offered by an authoring surface as an optional lint over a flattened design,
under the boundary rule that a shared concept is provided by at most one
instance or is instance-private; the lint counts syntactic origins (a `mk C`
anywhere in a body, a Source), so a re-wrapped value and a transport's `mk C`
initial value count as origins, and the lint's reading must say so.

## Alternatives rejected

- `SigUnique` as an invariant: Phase 8a's `lamp` has three `sem Tilt` signatures
  and two `sem Bright` after flattening (`binding_makes_second_signature`); a
  named transport is a second signature (`transport_second_signature`).
- `MkUnique` as a kernel invariant: fails on two instances sharing a provided
  concept (`lamp_two_origins`), on Phase 6's explicit composition
  (`phase6_not_mkUnique`), on Phase 14's `light := mk Brightness (rep dial)`
  (`rewrap_counts_as_origin`); a Source and a formula of the same concept are
  two origins (`source_and_formula`). No kernel judgment consumes it, and the
  drive edge cannot be derived from it (`one_origin_two_outputs`,
  `driver_not_origin`).

## Reason

The theorems above. What survives is stated positively: `MkUnique` is preserved
by every refinement that adds no declaration (`mkUnique_refine`), so an
origin-unique design stays so while it is realized, and the private-concept form
splits the origins of two instances into two concepts
(`private_lamp_two_concepts`, from `inst_sem_disjoint`).

## Consequences

`SingleDriver` (FVD-0052) and producer uniqueness constrain different objects —
declarations per output versus origins per concept; neither implies the other.
The design-meaning notion of origin that a lint would need, and the necessity
witness for two origins, are FVI-0030.
