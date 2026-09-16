# From Behavior Grouping to Reusable Behavior Components

*A formal note on Phase 8b of the BDL development (`BDL/Behavior/Group.lean`,
`Boundary.lean`, `Extract.lean`, `ExtractPreservation.lean`), followed by
implementation guidance for the BDL Studio/IDE.*

## Part I — The note

### 1. Three things that must not be confused

A designer who selects several Mapping Blocks and chooses *Group as
Behavior* has made an authoring decision, not a semantic one. A designer
who later chooses *Package as Component* has made a semantic decision:
from that point the unit has an interface, can be instantiated with fresh
identity, and can be bound to other behaviours. Phase 8b keeps the two
apart formally.

| | Mapping / declaration | `BehaviorGroup` | `BehaviorComponent` |
|---|---|---|---|
| identity | `DeclId` | `GroupId` and a member list | template identities, fresh per instance |
| public interface | its own `DeclInterface` | none — only projections | required / provided ports, clock parameters |
| instantiation | — | none | fresh identities (Phase 8a) |
| flattening | — | none needed | `flatten` |
| semantics | kernel | **none**: authoring metadata | elaborates to declarations |

The hierarchy `Mapping → group → component → system` is therefore not a
hierarchy of semantic objects. It has exactly one semantic step, packaging,
and that step is an elaboration into the Phase-8a system model.

### 2. Why groups are not semantic primitives

A `BehaviorGroup` is a `GroupId` and a list of member `DeclId`s. A
`GroupedDesign` is an ordinary `Design` with a list of groups beside it,
and `eraseGroups` forgets the list. Every group operation — `group`,
`ungroup`, `addMember`, `removeMember`, `move`, `merge`, `split` — acts on
the list and leaves the design untouched.

The consequence is that every kernel judgment of the erased design is the
*same proposition* before and after any group operation. In the
development these are Theorems A–G, and every one of them is proved by
`rfl` or `Iff.rfl`. That is not a weakness of the theorems; it is the
point. Grouping is transparent to typing, satisfaction, causality, clocks,
outputs and evaluation because it never enters the design, and the proof
obligation dissolves rather than being discharged. Dependency edges are
untouched for the same reason (`dependsOn_group`). Nested groups need no
recursive structure: nesting is a relation on the flat group list, and
carries no kernel significance because no group does.

In the Phase-1 vocabulary of refinement and edit, grouping is a fourth
class below "validation-only": nothing is rechecked, because nothing
changed.

### 3. Why visual aggregation stays transparent

A collapsed group shows aggregate input and output sockets. These are
*projections*. Over a finite enumeration of the design's declarations,
`crossIn` lists the non-members some member depends on and `crossOut` the
members some non-member depends on, both through the existing
declaration-based `DependsOn` of Phase 1; `openMembers` lists the group's
unresolved members; `drivenMembers` the members driving a sink;
`privateMembers` the rest. The socket is `externalInputs = crossIn ++
openMembers`; the output socket is `crossOut`. None of these is a
declaration.

The property that makes the socket safe is Theorem H, `socket_no_fanout`:
`a ∈ crossIn` says that *some* member depends on `a`, and says nothing
about the others. Counterexample 6 shows what goes wrong if the socket is
realized as a declaration that every member reads: a member that never
depended on `a` acquires an instantaneous dependency on it. Counterexample 5
shows the same failure for the other tempting encoding, a single
tuple-returning declaration for the whole group: the consumer of one
mapping comes to depend on the inputs of all of them. The kernel has no
tuples, and this is a reason not to add them for this purpose.

### 4. How a behaviour boundary is inferred

Given a design `D` and members `G`:

* **required** ports are exactly `crossIn` (Theorem K, `mem_crossIn`): a
  declaration outside the group that a member depends on;
* **provided** ports are exactly `crossOut` (Theorem L, `mem_crossOut`): a
  member that a non-member depends on;
* an **internal** edge (both ends in `G`) never produces a required port
  (Theorem J, `internal_not_crossIn`), and a member consumed only by
  members is not provided (`internal_only_not_crossOut`);
* **private** members are those neither provided nor driving a sink;
* **clock parameters** are every clock the design uses: a group owns no
  domain, so nothing is captured (Counterexample 3 shows what capturing
  costs: the reconnecting binding fails its clock condition);
* **physical sinks** are not ports. A member that drives a sink keeps its
  drive edge inside the component, and the sink stays external. Converting
  the sink into a semantic provided port produces a component that
  describes a behaviour with no physical effect (Counterexample 4).

Two naive rules are rejected by counterexample: taking every reference of
a member as required exposes internal producers as open ports and changes
behaviour (Counterexample 1); taking only the members' own open
declarations hides external dependencies and leaves the template ill-typed
(Counterexample 2).

### 5. How packaging changes authoring structure without changing meaning

*Package as Component* is the function `Extract`. It builds two
**restrictions** of the design: the component keeps the members and holds
an unresolved copy of each crossing-in declaration as a required port; the
residual keeps the non-members and holds an unresolved copy of each
crossing-out member. It then forms a Phase-8a system — instance 0 the
residual, instance 1 the component, clock parameters mapped identically —
with one direct binding per crossing declaration. Each binding is a
Phase-1 realization step: the port copy is realized as a reference to the
home copy. No body is translated, copied across the boundary, or rewritten.

The results, all mechanized:

* both templates realize their inferred interfaces (`restrict_realizes`);
* the system is a well-formed composition (`system_composeWF`) and its
  flattening is a well-formed design: typed, well clocked, causal,
  single-driver (`flat_WF`, Theorems M–Q);
* causality needed its own argument. Phase 8a's condition — an acyclic
  inter-instance graph — is never satisfied by a group with both inputs
  and outputs, yet the extraction is causal: the flattened instantaneous
  graph is the original graph with every crossing edge subdivided through
  a port copy, and doubling the original rank witnesses it (`flat_causal`);
* open members stay open (`flat_open_member`); private members are not
  provided ports, source no binding, and are never referenced by the
  residual (`private_unobservable`); each crossing-out member is its own
  provided port (`provided_iff`) — a group of several independent mappings
  yields several independent ports;
* **behaviour is preserved** (Theorem R, `orig_iff_flat`): for a wiring
  design with closure-free inputs, an original declaration and its home
  copy in the flattened extraction evaluate to the same value at every
  tick. The forward direction holds for every term visible on a side; the
  backward direction uses totality of the original design.

Identity is handled in two stages. Before packaging nothing is renamed.
After packaging the templates keep the original identities, and the
flattened system carries Phase-8a fresh identities: an original `n` lives
at `W + n` on the residual side and `2W + n` on the component side, with a
port copy on the other side where the boundary is crossed; a later second
instance of the component receives `3W + n`. The group's identity never
becomes a component identity.

### 6. What this says about behaviour as a design material

Phase 8a showed that behaviour can be packaged behind an interface,
instantiated, bound, nested and flattened into the same kernel. Phase 8b
adds the step before packaging: the cognitive unit a designer forms by
gathering mappings is not yet a semantic object, and need not be one. It
can be reorganized freely — members dragged in and out, groups merged and
split, collapsed to sockets — with no effect on meaning, because it has
none. When it is promoted, the boundary the designer sees on the collapsed
group is exactly the interface the component receives, and the promotion
preserves what the design computed. That is the bridge from atomic
behaviour to organized behaviour to reusable behaviour to a behaviour
system, and each step is either an identity or a proved elaboration.

### 7. What is not established

* Theorem R is proved for the single-domain semantics `Ev` on wiring
  designs with closure-free inputs; transported ports under `MEv` and
  higher-order bodies are not covered (the same obstacle as Phase 8a's
  Theorem J: a domain-indexed input).
* The clock parameter list must cover the clocks of declarations and
  sinks; a `sync` clock appearing only inside a body is renamed to a fresh
  domain, which is harmless for `Ev` and `Clocked` but should be collected
  by an elaborator.
* Four conditions now rest on the abstract evidence relation
  (`Monotone`, `Equivariant`, `PortSound`, `InterfaceLocal`); a concrete
  compositional evidence model would discharge them once.
* Phase 8a's `InstAcyclic` is too coarse for extraction; a port-level
  inter-instance graph would subsume both results.

---

## Part II — Implementation guidance for BDL Studio / IDE

### What production must persist for a `BehaviorGroup`

A group identity and its member list, and nothing else: no types, clocks,
formulas, outputs or sockets. Anything derived (sockets, boundary
candidates, private/exposed status) is recomputed from the design and is
not authoritative if stored. Display name and documentation are surface
metadata alongside the identity.

### What belongs only in layout

Collapsed/expanded state, position, size, colour, ordering of members,
socket placement. None of it is modelled and none of it affects any check.

### Whether grouping triggers semantic invalidation

Never. `group`, `ungroup`, drag-in, drag-out, merge and split are the
identity on the design (`group_is_identity_on_design`). The workspace must
not re-run typing, causality, clock, output or hardware checks on a group
operation, and must not clear cached verdicts. This is a stronger statement
than "the checks would pass": they are the same propositions.

### How aggregate sockets are computed

Input socket: `crossIn` (non-members some member references, through the
existing dependency relation) plus `openMembers` (unresolved members).
Output socket: `crossOut` (members some non-member references). Sinks
driven by members are shown separately as physical outputs, never as
semantic sockets. Sockets are views: connecting a wire to a socket must be
realized as a wire to the specific member declaration, never as an edge to
a socket object, and the socket must never appear as a fan-out to all
members (Counterexample 6) or as a tuple (Counterexample 5).

### How drag-in / drag-out behave

Change the member list; recompute sockets; do nothing else. Moving a
mapping between groups, or between a group and the top level, is `move`,
a semantic no-op (Theorem C). Split and merge likewise.

### How "Package as Component" computes interface candidates

From the member set: required = `crossIn`; provided = `crossOut`; private
= members neither in `crossOut` nor driving a sink; clock parameters =
every clock the design uses (never a subset); physical sinks driven by
members stay with the members, external. Present these as the default and
let the designer widen them: a private member may be promoted to
provided; an additional external input may be added as an open required
port. The designer may *not* narrow below the inferred required set
(Counterexample 2) or turn a sink into a semantic port (Counterexample 4).

The packaging operation itself is: build the component and residual
templates as restrictions of the design; instantiate the component once;
bind the boundary through ordinary port bindings. Do not rewrite or copy
bodies; do not introduce a group-level edge kind. Run the standard
Phase-8a checks on the result; the flattened design is guaranteed well
formed under the stated hypotheses, and the causality check will pass
even though the instance graph shows edges both ways — do not gate
packaging on Phase 8a's coarse instance-level acyclicity.

### What user choices cannot be inferred safely

* Whether an unresolved member is the component's *input* (leave it a
  required port) or an *open internal* to be realized later inside the
  component (both are structurally valid; the tool must ask or default to
  "input" and let the designer change it).
* Whether a private member should nevertheless be exported (a design
  choice about the interface, not derivable from use).
* Whether a member's physical sink should be private to the component or
  remain external (Phase 8a's `internalOut` flag). Extraction keeps sinks
  external by default; making a sink private changes deployment identity
  and must be explicit.
* Component display name and documentation.

### What existing facilities are reused

Everything. Dependency analysis (`DependsOn`) for sockets and boundary
inference; Phase-1 realization for reconnection; Phase-8a components,
instances, fresh identity, bindings, `ComposeWF` and `flatten`; the
existing typing, causality, clock and output checkers on the flattened
result; Phase-7 hardware validation on the flattened sinks. No new checker
and no new runtime edge kind is required.

### Assumptions the equivalence relies on (for the record)

1. wiring designs (no lambdas/variables) and closure-free inputs;
2. a correct enumeration of the design's declarations, identities below
   the chosen width, clock coverage;
3. evidence that is monotone, equivariant, port-sound and interface-local;
4. totality of the original design (causal, well formed, well-typed inputs)
   for the backward direction;
5. single-domain semantics.
