---
kind: report
phase: 20
area: core
date: 2026-09-21
status: current
---

# Phase 20 — One producer per concept: the invariant, its preservation under refinement and composition, and the concept reference

Question (the owner's design decision after Phase 19's audit): a concept is _one
product quantity_ — at each tick it has one value, provided by the environment
or computed by exactly one relationship; every other candidate is an input of
that relationship, not a value of the concept. Can this be made a global
invariant of the model without touching typing, evaluation or the grant, does it
survive refinement and composition, and does it give a concept the denotation
Phase 19 said it lacked — so that a formula, and the canvas, may name a
**concept** where the kernel names a declaration? Answer: **yes, each of them,
proved.** `ProducerUnique Δ` — at most one _origin_ per concept, an origin being
a `mk C` outside initial-value positions or an unresolved announcer of `C` — is
a global invariant beside `SingleDriver` (`Core/Producer.lean`). It is preserved
by every refinement that adds no declaration (`ProducerUnique.refine`) and by
realizing with a relaying body (`update_relay`); it is preserved by flattening
under the boundary rule that mirrors `ExternalSingleDriver` — a shared concept
is originated by at most one instance, ports not counting — with every port
bound and the bindings relaying (`flatten_producerUnique`), decided by one
Boolean over a finite presentation (`flatten_producerUnique_ofB`). Under it
`producerOf` is a function; a surface concept reference `cref C` elaborates to
`declRef (producerOf C)` (`elabS_cref`), conservatively (`elabS_embed`), stably
under refinement (`elabS_refine`), and _the_ value of a concept at a tick is
determined (`valueOf_det`). The designs Phase 19 found with several producers —
Phase 6's composition and priority, Phase 14's re-wrap, Phase 8a's shared lamp —
are rewritten in the invariant's form with the same executed traces
(`composition_unique`, `priority_unique`, `rewrap_unique`,
`private_lamp_unique`). Files: `BDL/Validation/Producer.lean` (moved from
`Core/` in Phase 21), `BDL/Behavior/Producer.lean`,
`BDL/Experiments/ConceptRef.lean` (moved from `Surface/` in Phase 21),
`BDL/Experiments/ProducerUniqueExamples.lean`; decisions FVD-0161 (supersedes
FVD-0159, FVD-0160), FVD-0162; note:
[one-producer-per-concept.md](../notes/one-producer-per-concept.md).

## 20.1 The model

`Validation/Producer.lean` (in Phase 20 `Core/Producer.lean`, a global
invariant; nothing in `Ty`, `Expr`, `HasType`, `Ev`/`MEv` or the grant changes):

- `Expr.mkSet` — the concepts a term constructs, as a list (`mem_mkSet_iff` with
  `Expr.constructs`, which becomes decidable).
- `Expr.originSet` — the same **outside the initial-value position** of `delay`
  and `sync` (`constructs_of_mem_originSet`). The explicit initial value of a
  transport or a memory is the relay's default, the value stood in before the
  first sample, and every transported concept value must have one (FVD-0038); it
  is not a producer.
- `DesignDecl.origins` — the body's `originSet`, or the signature's `grant` if
  unresolved. `Produces Δ d C := ∃ h, Δ d = some h ∧ C ∈ h.origins` (decidable,
  `producesB`). Phase 19's `MkProduces`/`MkUnique` are now abbreviations of
  these.
- `ProducerUnique Δ := ∀ C d₁ d₂, Produces Δ d₁ C → Produces Δ d₂ C → d₁ = d₂`.
- `producerOf ids Δ C := ids.find? (Produces Δ · C)`; `producerOf_eq`,
  `produces_iff_producerOf`: under the invariant, the relation is the graph of
  this function.
- `producerUniqueB`, `ProducerUnique.ofList` — the decision procedure for finite
  designs.

`Behavior/Producer.lean`: `IsPort` (a required port or a parameter),
`ExternalSingleProducer S` (the boundary rule), `PortsBound S`, `StoredId`,
`Finite S` (a template's declarations as a list) with the Boolean checkers
`externalSingleProducerB`, `originsBoundB`, `portsBoundB`, `templatesUniqueB`,
`relayB`.

`Surface/ConceptRef.lean`: `SExpr` (the kernel's forms plus `cref C`),
`elabS ids Δ : SExpr → Option Expr`, `embed`, `ValueOf`.

## 20.2 Refinement

`Produces.of_refine`: an origin of the refined environment was an origin before
— a declaration that became realized announced every concept its body may
originate (`constructs_granted`), and a realized one keeps its body. Hence
`ProducerUnique.refine` (hypotheses `GlobalWF Δ₂`, `EnvRefines Δ₁ Δ₂`, no new
declaration) and `producerOf_refine`: **the producer does not move while the
design is realized.** Adding a second producer is an edit, refused like a second
driver of an output. `Produces.of_update` and `ProducerUnique.update_relay`:
realizing a declaration with a body whose `originSet` is empty — a wire, a
transport, a memory, a selection — removes an origin and adds none.

## 20.3 Composition

`flatten_producerUnique`: for a system whose templates are stored under their
own identities and producer-unique, whose bindings relay (`originSet = []`),
which satisfies the boundary rule, whose originated concept identities are below
the width, and whose required ports and parameters are all bound, the flattened
design is producer-unique. Proof: an origin of `flattenΔ` is an origin of
`unionΔ` that no binding targets (`produces_foldl`, by induction over the
bindings with `of_update`); an origin of `unionΔ` is the renamed origin of one
instance (`produces_union`, with `rename_originSet` and `Ty.rename_grant`); two
such of one concept are either both internal — then the same instance and, by
the template's uniqueness, the same declaration (`inst_sem_disjoint`) — or both
shared and neither a port (a port is bound and a bound destination is no
origin), hence the same by the boundary rule; a mixed pair is impossible
(`inst_sem_not_global`). `flatten_producerUnique_of_composeWF` takes the stored
identities and the relaying bindings from `ComposeWF` (a binding body is typed
under `Grant.none`, `originSet_nil_of_noGrant`). `flatten_producerUnique_ofB`:
one Boolean over a `Finite` presentation decides all five hypotheses.

The boundary rule is the concept analogue of `ExternalSingleDriver` (FVD-0068's
system judgment): "an external sink is driven by at most one instance" becomes
"a shared concept is originated by at most one instance"; a required port is a
placeholder, as an undriven sink is.

## 20.4 The concept reference

`elabS` replaces `cref C` by `declRef d` where `producerOf ids Δ C = some d`; a
concept nobody produces leaves the term open (`elabS_cref_none`) — a design in
progress, not an error. `elabS_embed`: kernel terms elaborate to themselves
(conservative). `elabS_congr`: the elaboration depends on the design only
through `producerOf`. `elabS_refine`: whatever the refined design elaborates a
term to, the design before elaborated it to the same kernel term — **an edge
drawn to a concept block keeps its meaning while the design is realized.**
`ValueOf ids S Δ I c t C v` (the value of the producer under `MEv`) and
`valueOf_det` (from `MEv.det`): a concept has at most one value at a tick.

A reader in another clock domain elaborates to `declRef` of the producer as
well; `WellClocked` then requires the transport, which the surface inserts on
the edge — the register mark — and which is a relay (`transport_unique`), not a
second producer.

## 20.5 The designs rewritten, executed

| Design                                                                  | Before (Phase 19)                       | After                                                                                                                | Theorem                                  |
| ----------------------------------------------------------------------- | --------------------------------------- | -------------------------------------------------------------------------------------------------------------------- | ---------------------------------------- |
| Phase 6 composition `base, corr, final : MotorAngle`                    | two origins (`phase6_not_mkUnique`)     | `base : BaseAngle`, `corr : Correction`, `final : MotorAngle`; angle 15 in both                                      | `composition_unique`                     |
| Phase 6 priority `emergencyTarget, normalTarget, selected : MotorAngle` | two origins                             | `EmergencyTarget`, `NormalTarget`, one `selected`; 0 / 90 in both                                                    | `priority_unique`                        |
| Phase 14 `light := mk Brightness (rep dial)`                            | two origins (`rewrap_counts_as_origin`) | the wire `light := dial`; the light reads 40 in both                                                                 | `rewrap_unique`                          |
| Phase 8a `lamp`, `Bright` shared by two dimmers                         | two origins (`lamp_two_origins`)        | `Bright` instance-private: unique by the boundary rule, one `decide`                                                 | `lamp_not_unique`, `private_lamp_unique` |
| Phase 19 sensors (Model C form)                                         | unique already                          | `hot` written over the concept `Temperature` elaborates to `declRef temp`; the temperature at ticks 1, 2 is 310, 290 | `read_by_concept`, `temperature_value`   |
| Phase 19 transport `xS := sync c₁ (mk C 0) x`                           | counted as an origin (§19.5)            | a relay; `producerOf C = x`                                                                                          | `transport_unique`                       |
| Phase 19 one origin, two outputs                                        | unique; drivers not origins             | unchanged: β independent of the producer                                                                             | `driver_independent`                     |

## 20.6 Models tried

| Model                                                     | Decided by                                                                                                                                                  |
| --------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------- |
| origins counting initial values (Phase 19's `MkProduces`) | every transported concept value would be a second origin (`transport_second_signature`, FVD-0038 makes the initial value mandatory); rejected — `originSet` |
| uniqueness as a typing condition                          | nothing in `HasType` counts declarations; a global invariant like `SingleDriver` needs no typing change; not tried further                                  |
| a resolver primitive                                      | not needed: the resolver is one ordinary declaration (`composition_unique`, `priority_unique`); Phase 19's finding stands                                   |
| concept reference as a kernel term                        | the kernel keeps `declRef` only: `elabS` is a surface projection, `elabS_embed` conservative; a kernel `cref` would make evaluation depend on `producerOf`  |
| the boundary rule counting ports                          | two dimmers requiring `Tilt` would violate it although bound; ports are placeholders, hence `IsPort` excluded and `PortsBound` required                     |

## 20.7 Theorems

| Claim                                                                  | Theorem                                                                                                                                                           | Hypotheses                                                                            |
| ---------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------- |
| origins are constructions; construction is granted                     | `constructs_of_mem_originSet`, `Produces.of_refine`                                                                                                               | `GlobalWF Δ₂`, `EnvRefines`, same domain                                              |
| refinement preserves the invariant; the producer does not move         | `ProducerUnique.refine`, `producerOf_refine`                                                                                                                      | as above                                                                              |
| realizing with a relay preserves it                                    | `Produces.of_update`, `ProducerUnique.update_relay`                                                                                                               | `h'.origins = []`                                                                     |
| the relation is the graph of `producerOf`                              | `producerOf_produces`, `producerOf_eq`, `produces_iff_producerOf`                                                                                                 | `ProducerUnique`, `d ∈ ids`                                                           |
| finite decision                                                        | `ProducerUnique.ofList`                                                                                                                                           | `producerUniqueB l = true`                                                            |
| an origin of the flattened design is an untargeted origin of the union | `produces_foldl`, `produces_union`, `storedId_union`                                                                                                              | bindings relay, templates stored under their ids                                      |
| flattening preserves the invariant                                     | `flatten_producerUnique`, `flatten_producerUnique_of_composeWF`, `flatten_producerUnique_ofB`                                                                     | templates unique, boundary rule, origins below the width, ports bound, bindings relay |
| a binding's body originates nothing under `ComposeWF`                  | `bindingBody_originSet`, `originSet_nil_of_noGrant`                                                                                                               | `ComposeWF`                                                                           |
| concept reference: to the producer, conservative, congruent, stable    | `elabS_cref`, `elabS_cref_none`, `elabS_embed`, `elabS_congr`, `elabS_refine`                                                                                     | `ProducerUnique`; refinement hypotheses                                               |
| a concept's value is determined                                        | `valueOf_det`, `valueOf_of_produces`                                                                                                                              | `MEv.det`                                                                             |
| the rewritten designs (executed)                                       | `composition_unique`, `priority_unique`, `rewrap_unique`, `private_lamp_unique`, `read_by_concept`, `temperature_value`, `transport_unique`, `driver_independent` | closed designs, `decide`                                                              |

48 theorem-like declarations added (12 + 20 + 7 + 9); `ProducerAlternatives`
loses two (its definitions moved); every one on `propext`/`Quot.sound`
(`#print axioms` on the twenty headline theorems); no `sorry`; the whole
development 1 612 across 73 files; `lake build` 76 jobs, clean, no warnings.

## 20.8 Claim audit

- **Proved**: every row of §20.7 except the last; `flatten_producerUnique` is
  general over systems, not over the lamp.
- **Executed**: the rewritten designs' traces (finite ticks, concrete inputs);
  `private_lamp_unique` is a `decide` through the general theorem.
- **Definitional**: an initial value is not an origin (a definition, chosen —
  FVD-0161 says why); multi-input is not multi-producer.
- **Not established**: a general theorem that every design with several origins
  of one concept rewrites into the invariant's form with the same trace — the
  invariant is a design choice and refuses such designs; the rewriting is shown
  on the development's cases. `hbound` (originated concept identities below the
  width) is taken as a hypothesis, derivable from well-formedness in principle.
  The converse of `elabS_refine` (a producer is never lost by refinement) is not
  stated; realizing an unresolved producer keeps it one only if its body
  originates the concept, which `Causal` forces and which is not proved.
- **Corrected from Phase 19**: §19.5's clock-domain line ("a transport's
  explicit initial value is an origin") is struck — under `originSet` the
  initial value is the relay's default; §19.12's verdicts and FVD-0159/0160 are
  superseded by FVD-0161, right on their evidence until the consumer of
  uniqueness (the concept reference, the canvas as a value graph) was required.
- **Design recommendation**: the canvas as a bipartite graph — relationship →
  concept (produces, one edge in), concept → relationship (reads, any number
  out); the intermediate-concept naming for candidates.

## 20.9 Verdicts

- `ProducerUnique` — **KEEP IN KERNEL** as a global invariant beside
  `SingleDriver` (FVD-0161); checked, not typed.
- `originSet` (initial values excluded) as the origin count — **KEEP IN KERNEL**
  (FVD-0161).
- `ExternalSingleProducer`, `PortsBound` — **KEEP IN BEHAVIOR** as the
  composition-level judgment beside `ExternalSingleDriver` (FVD-0161).
- `cref` / `elabS`, `producerOf` — **KEEP IN SURFACE-DESUGAR** (FVD-0162); no
  kernel term names a concept.
- a resolver primitive — **REMOVE** (unchanged from Phase 19).
- FVI-0030 — resolved by FVD-0161 (the origin count is decided; the necessity
  witness is moot under the invariant).
