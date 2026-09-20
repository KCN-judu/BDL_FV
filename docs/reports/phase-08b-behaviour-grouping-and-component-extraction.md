---
kind: report
phase: 8b
area: behavior
date: 2026-09-16
status: current
---

# Phase 8b — Behaviour grouping and component extraction

## 8b.1 The claim

Designers may reorganize atomic behaviour declarations into larger cognitive
units without changing program meaning, and may later promote such a unit into a
reusable component through a semantics-preserving extraction. Formally, three
objects are kept apart:

| Object                         | Identity                     | Interface                                 | Instantiation      | Semantics                     |
| ------------------------------ | ---------------------------- | ----------------------------------------- | ------------------ | ----------------------------- |
| declaration (Mapping)          | `DeclId`                     | its `DeclInterface`                       | —                  | kernel                        |
| `BehaviorGroup`                | `GroupId` + member `DeclId`s | none (projections only)                   | none               | **none** (authoring metadata) |
| `BehaviorComponent` (Phase 8a) | template ids `< width`       | required/provided ports, clock parameters | fresh per instance | elaborates to declarations    |

The hierarchy
`Mapping → group → package/extract → component → instantiate → system` is
realized as: `GroupedDesign.group` (metadata), `Extract` (elaboration),
`BehaviorSystem` (Phase 8a). The kernel is unchanged.

## 8b.2 Grouping (`Group.lean`)

- `BehaviorGroup = ⟨GroupId, List DeclId⟩`;
  `GroupedDesign = ⟨Design, List BehaviorGroup⟩`; `eraseGroups` is the
  projection.
- Operations `group`, `ungroup`, `addMember`, `removeMember`, `move`, `merge`,
  `split` act on the group list only.
- Nested groups are a relation on the flat group list (`NestedIn`); no recursive
  structure.

| #   | Statement                                                                                                                                                   | Lean                                                                                            | Status             |
| --- | ----------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------- | ------------------ |
| A   | `eraseGroups (group D G) = D`                                                                                                                               | `erase_group`, `eraseGroups_*` (all `rfl`)                                                      | **proved**         |
| B   | group/ungroup round trip: design unchanged; with a fresh group id, the group list is restored exactly                                                       | `erase_ungroup_group`, `ungroup_group_groups`                                                   | **proved**         |
| C   | moving a declaration between groups (either direction, to/from ungrouped) is a semantic no-op                                                               | `move_erase`                                                                                    | **proved** (`rfl`) |
| D–G | typing, causality, clocks, outputs (drive, single-driver, completeness) of the erased design are the same propositions before and after any group operation | `typing_group`, `causal_group`, `clocked_group`, `outputs_group`, `judgments_*` (all `Iff.rfl`) | **proved**         |
| —   | dependency edges unchanged                                                                                                                                  | `dependsOn_group`, `instDependsOn_group`                                                        | **proved**         |
| —   | invalidation classification: every group operation is the identity on `design`, hence `EnvRefines` both ways                                                | `group_is_identity_on_design`, `group_envRefines`                                               | **proved**         |

That these are `rfl`/`Iff.rfl` is the result: grouping does not enter any kernel
judgment because it does not enter the design. Interface, realization, semantic
identity, reactive, clock, output and deployment states are all unchanged; only
authoring metadata changes.

## 8b.3 Projections and boundary inference (`Boundary.lean`)

Over a finite enumeration `ids` of a design's declarations
(`Design.Enumerates`):

- `crossIn D ids G` — non-members some member depends on (`DependsOn`, Phase 1);
- `crossOut D ids G` — members some non-member depends on;
- `openMembers` — unresolved members; `drivenMembers` — members driving a sink;
- `privateMembers` — members neither crossing out nor driving a sink;
- `InternalEdge` — producer and consumer both members;
- `externalInputs = crossIn ++ openMembers`, `externalOutputs = crossOut` —
  views, not declarations;
- `clocksOf` — every clock used: all become parameters.

| #   | Statement                                                                                                      | Lean                                                 | Status     |
| --- | -------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------- | ---------- |
| H   | aggregate sockets add no dependency: `r ∈ crossIn` says some member depends on `r`, nothing about the others   | `socket_no_fanout`; Counterexample 6                 | **proved** |
| I   | `r ∈ crossIn ↔ r ∈ ids ∧ r ∉ G ∧ ∃ m ∈ G, DependsOn m r`; `p ∈ crossOut ↔ p ∈ G ∧ ∃ u ∉ G, DependsOn u p`      | `mem_crossIn`, `mem_crossOut`                        | **proved** |
| J   | an internal edge never makes its producer crossing-in; a member with only member consumers is not crossing-out | `internal_not_crossIn`, `internal_only_not_crossOut` | **proved** |
| K   | external dependencies are exactly the required boundary                                                        | `mem_crossIn` (+ `comp_boundary` executed)           | **proved** |
| L   | externally consumed producers are exactly the provided boundary                                                | `mem_crossOut`                                       | **proved** |

## 8b.4 Extraction (`Extract.lean`)

`restrict D keep port` keeps the declarations with `keep`, keeps those with
`port` as unresolved copies, drops the rest; `template` wraps it with the
inferred ports and all clocks as parameters.

- component `comp = template D isMember isCrossIn crossIn crossOut clocks W`;
- residual `resid = template D isOutside isCrossOut crossOut crossIn clocks W`;
- `system`: instance 0 = residual, instance 1 = component, κ = identity,
  bindings `C.r := R.r` for `r ∈ crossIn` and `R.p := C.p` for `p ∈ crossOut`;
- `flat = flatten system`; `home d` = the copy of `d` on its own side.

Identity policy: templates keep the original identities (`< W`); the flattened
system has `W + n` (residual) and `2W + n` (component) plus port copies; a later
instance of the component gets `3W + n`. The group's `GroupId` never appears in
the component.

Physical outputs: a member's drive edge stays with the member; sinks stay
external; no semantic port is created for a sink (`drive_stays_with_member`).

## 8b.5 Extraction correctness (`ExtractPreservation.lean`)

Hypotheses (`Input.WF`): `D.WF`, an enumeration, `G ⊆ ids` nodup, width above
all ids/concepts/clocks/sinks, clocks of `Κ` and of sinks covered by `clocks`,
and evidence `InterfaceLocal`; Phase-8a evidence conditions (`Monotone`,
`Equivariant`, `PortSound`) for the flattening theorems.

| #   | Statement                                                                                                                                                                                                                 | Lean                                                                                      | Status                                                                                                   |
| --- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------- |
| —   | a closed restriction realizes its template interface                                                                                                                                                                      | `restrict_realizes` (generic), `comp_realizes`, `resid_realizes`                          | **proved**                                                                                               |
| M   | the extracted system is `ComposeWF`; its flattening is `Design.WF`                                                                                                                                                        | `system_composeWF`, `flat_WF`                                                             | **proved**                                                                                               |
| N   | typing: `flat_globalWF` (by Phase 8a `flatten_globalWF`)                                                                                                                                                                  | `flat_globalWF`                                                                           | **proved**                                                                                               |
| O   | causality: the flattened instantaneous graph is the original with crossing edges subdivided; rank `2·rank` on home copies, `2·rank+1` on port copies                                                                      | `flat_causal`                                                                             | **proved** — _without_ `InstAcyclic`, which fails for any group with both inputs and outputs             |
| P   | clocks: `flat_wellClocked` (by Phase 8a); clock parameters are all of `D`'s clocks, κ = id, so no domain is captured                                                                                                      | `flat_wellClocked`, `ren_c`                                                               | **proved**                                                                                               |
| Q   | outputs: `DriveWF`, `SingleDriver` of the flattening; drives stay with members                                                                                                                                            | `flat_driveWF`, `flat_singleDriver`, `drive_stays_with_member`                            | **proved**                                                                                               |
| R   | observational equivalence: for wiring `D` with closure-free inputs, `Ev D I (declRef d) v ↔ Ev flat (liftInput I) (declRef (home d)) v` (forward for every term visible on a side; backward on declarations via totality) | `eval_orig_to_flat`, `orig_iff_flat`, `orig_total`; executed `extraction_preserves_trace` | **proved for the single-domain wiring fragment**; `MEv` with transports and higher-order bodies **open** |
| —   | open members stay open (progressive formalization survives packaging)                                                                                                                                                     | `flat_open_member`                                                                        | **proved**                                                                                               |
| J'  | private members are not provided ports, source no binding, and are never referenced by the residual side                                                                                                                  | `private_unobservable`                                                                    | **proved**                                                                                               |
| §29 | each crossing-out member is its own provided port                                                                                                                                                                         | `provided_iff`; executed `two_ports`                                                      | **proved**                                                                                               |

Assumptions required by the equivalence (R), explicitly:

1. `D` is a wiring design (no lambdas/variables) and inputs carry no closures;
2. `Input.WF`: enumeration, bounds, clock coverage, evidence locality;
3. Phase-8a evidence: monotone, equivariant, port-sound;
4. the backward direction uses totality of `D` (`reactive_total`: causal, well
   formed, well-typed inputs);
5. single-domain semantics `Ev` (the `sync` clock is renamed but ignored by
   `Ev`; `MEv` not covered).

## 8b.6 Counterexamples (`Experiments/GroupAlternatives.lean`)

| #   | Naive rule                                                                  | What breaks                                                                                                                         | Lean                                                      |
| --- | --------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------- |
| 1   | every reference of a member is a required input                             | the internal producer `f` becomes an open port; `g` reads the port instead of computing `a` (99 vs 10)                              | `naive_exposes_internal`, `naive_changes_behaviour`       |
| 2   | only the members' own open declarations are inputs                          | the external `a` is missing: the template has a dangling, ill-typed reference                                                       | `hidden_dependency_ill_typed`, `correct_lists_external`   |
| 3   | no clock parameters                                                         | `c0` is freshened per instance; the reconnecting binding fails its clock condition                                                  | `captured_clock_mismatch`, `captured_binding_clock_fails` |
| 4   | convert the member's sink into a semantic provided port and strip the drive | the component describes a behaviour with no physical effect: alone (or reused) it drives nothing; correct extraction keeps the edge | `converted_loses_effect`, `drive_kept`                    |
| 5   | one tuple-returning declaration for `{f := a, g := b}`                      | the consumer of `f` now depends instantaneously on `b`; correct extraction gives two independent ports                              | `tuple_forces_dependency`, `two_ports`                    |
| 6   | the input socket as a fan-out declaration read by every member              | `h` acquires a dependency on `a` it never had; the correct socket is a projection                                                   | `fanout_false_dependency`, `socket_is_projection`         |

## 8b.7 Minimality audit

| Construct                                   | Verdict                                        | Reason                                                          |
| ------------------------------------------- | ---------------------------------------------- | --------------------------------------------------------------- |
| `BehaviorGroup`, membership                 | AUTHORING METADATA                             | Theorems A–G are `rfl`                                          |
| collapse/expand                             | UI/LAYOUT ONLY                                 | not modelled; nothing to model                                  |
| aggregate input/output sockets              | DERIVED PROJECTION                             | `externalInputs`/`externalOutputs`; Theorem H; Counterexample 6 |
| group/ungroup/move/merge/split              | SEMANTIC NO-OP                                 | `group_is_identity_on_design`                                   |
| nested groups                               | AUTHORING METADATA (relation on the flat list) | `NestedIn`; no kernel significance                              |
| boundary inference (`crossIn`/`crossOut`/…) | ANALYSIS / ELABORATION                         | over Phase-1 `DependsOn`                                        |
| `restrict`/`template`/`Extract`             | SURFACE ELABORATION                            | output is a Phase-8a system                                     |
| `Evidence.InterfaceLocal`                   | constraint on validation                       | needed for template realization                                 |
| tuple-return / `MultiOutputMapping`         | REMOVE                                         | Counterexample 5                                                |
| fan-out socket declaration                  | REMOVE                                         | Counterexample 6                                                |
| group-level runtime edge                    | REMOVE                                         | bindings are Phase-1 realization                                |
| new kernel term                             | NOT NEEDED                                     | `BDL/Core` unchanged                                            |

## 8b.8 Critical remarks

- The strongest results here are the trivial ones: grouping transparency holds
  by `rfl` because the group never touches the design. That is the design
  principle, stated as a proof obligation that dissolves.
- Extraction's causality theorem could not reuse Phase 8a's coarse `InstAcyclic`
  — a group with inputs and outputs always induces instance edges both ways. The
  subdivision argument is the honest replacement and suggests that Phase 8a's
  condition should eventually be refined to port level.
- `Evidence.InterfaceLocal` joins `Monotone`, `Equivariant`, `PortSound` as a
  condition on the validation layer. Four conditions on one abstract relation is
  a sign that a concrete evidence model (compositional discharge over
  interfaces) should be fixed in a later phase.
- Theorem R is on the same fragment as Phase 8a's Theorem J. The obstacle is the
  same: transported ports would need a domain-indexed input.
- `clocks` must cover every clock in `Κ` and in sinks; a `sync` clock inside a
  body that is not also a declaration's clock is renamed to a fresh domain.
  Harmless for `Ev` and for `Clocked` (its operands must then be agnostic), but
  it is a coverage gap the elaborator should close by collecting body clocks
  too.

## 8b.9 The Phase-8b result

> A behaviour group is authoring metadata: every group operation is the identity
> on the design, so every kernel judgment and the semantics are unchanged by
> construction. Its boundary — required, provided, private, clock parameters,
> physical sinks — is a projection of the existing declaration-based dependency
> relation. Packaging a group is an elaboration into a Phase-8a system of two
> templates reconnected by realization steps; the flattening is globally well
> formed, well clocked, causal (by subdividing the original graph), and
> single-driver, keeps open members open and sinks with their drivers, and, on
> the single-domain wiring fragment, evaluates every original declaration to the
> same value as its home copy.
