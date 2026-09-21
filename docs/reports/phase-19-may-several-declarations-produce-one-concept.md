---
kind: report
phase: 19
area: experiments
date: 2026-09-21
status: current
---

# Phase 19 — May several declarations produce values of one nominal concept? Models A, B, C

Question (an audit brief; the production canvas's Concept/Output projection is
frozen until it concludes): in one design, may several distinct declarations or
mappings produce values of the same nominal concept — is `sem C` a nominal
_type_ whose values many declarations may construct (Model A), the identity of
_one_ product-level quantity with one producing relationship (Model B), or a
type whose several candidate producers are admitted only under an explicit
resolution (Model C)? Answer: **in the kernel a concept is a nominal type and
several declarations may produce it; this is the state at HEAD `5f71710`, and
the audit keeps it** — not because the kernel already permits it, but because
(i) the kernel has no consumer of "the value of concept `C`": every reference is
to a declaration (`declRef`), so multiplicity of producers causes no ambiguity
in any judgment (`second_producer_invisible`, `Ev.det`); (ii) the
signature-level uniqueness that production's word _produces_ would name is
refuted by the development's own constructions — every component binding and
every named transport is a second declaration of type `sem C`
(`binding_makes_second_signature`, `transport_second_signature`); (iii) the
origin-level uniqueness that survives (`MkUnique`) is preserved by refinement
(`mkUnique_refine`) but fails on ordinary component reuse (`lamp_two_origins`),
on Phase 6's explicit-composition designs (`phase6_not_mkUnique`) and on Phase
14's re-wrapped Source (`rewrap_counts_as_origin`), and has no kernel judgment
that would consume it; (iv) every alternative-producer use the development knows
rewrites, with intermediate concepts and one resolving declaration over existing
constructs, to an origin-unique design with the same downstream trace
(`sensors_rewriting_same_trace`, `override_rewriting_same_trace`,
`sensorsC_mkUnique`) — Model C is a design discipline expressible today, not a
primitive; (v) the drive edge is independent of producers
(`one_origin_two_outputs`, `driver_not_origin`). No design that _needs_ two
origins of one concept was found; none is claimed impossible (FVI-0030). Files:
`BDL/Experiments/ProducerAlternatives.lean`; note:
[concepts-and-their-producers.md](../notes/concepts-and-their-producers.md);
paper impact:
[paper-impact-producers-of-one-concept.md](../notes/paper-impact-producers-of-one-concept.md).

## 19.1 HEAD audited, and what "Concept" is in the formal artifacts

Audited at `5f71710600bc` (the reference HEAD of the brief, in sync with
`origin/main`). The relevant artifacts, read before any definition was written:

- `Ty.sem SemanticId` (`Core/Base.lean`, `Core/Decl.lean`): a concept is a
  **nominal type** over an internal identity (FVD-0019, FVD-0020 "a concept is a
  type, a declaration is a value"). `ConceptEnv : SemanticId → Option Ty` binds
  a representation; nothing in the kernel binds a concept to a declaration.
- `Grant.of τ = τ.grant` — the concepts in result position of a declaration's
  expected type — and `HasType.constructs_granted`: a realization may construct
  (`mk C`) only concepts its own signature announces (Phase 3.1). This is
  authority _per declaration_; nothing counts declarations per concept.
- `Expr.constructs`, `Ev.tag_provenance`,
  `temporal_state_preserves_semantic_identity`,
  `sync_preserves_semantic_identity` (Phase 4/5): a value tagged `C` at any tick
  came from a realization that constructs `C`, an input carrying `C`, or the
  term; memory and transport preserve tags. These are provenance theorems: they
  bound _where_ a `C` may come from, not _how many_ places.
- References: `Expr.declRef d` is the only way a term names another declaration;
  `dependsOn`, `Causal`, `NoMention`, `update_transparent`, `input_congr` are
  all indexed by `DeclId`. There is no construct that names a concept and asks
  for a value — no `valueOf C`, no implicit resolution.
- `GlobalWF ev Θ Δ` checks each declaration's realization against its own
  interface; it contains no per-concept clause. `DriveWF`/`SingleDriver` are
  per-declaration and per-output; they mention no concept multiplicity.
- Production's records (read only, `../BDL` at `4e87d4f`): ADR-0034 §4 "One
  definition of _produces_. _Produces_ is the signature: a relationship whose
  output is _C_ produces _C_, rule or value … _C_ is **carried by**" the values
  and Sources that produce it — a many-relation; the concept node's input socket
  receives every producer. Nothing in production's records claims a unique
  producer either.

So at HEAD: **several declarations of result type `sem C` are legal**, and the
current claims (kernel pages, decisions FVD-0019 … FVD-0024, Phase 6, the two
papers) nowhere assert one producer per concept. The documents differ in
_style_, recorded in §19.8.

## 19.2 The current multiple-producer witness

`Δxy = [x : C := mk C 1, y : C := mk C 2]` is `GlobalWF` and `Causal`
(`witness_two_values`); `Δfg = [a : A, b : B, f : A -> C, g : B -> C]` with `f`
and `g` realized as `mk C (rep _ + k)` is `GlobalWF` (`witness_two_arrows`).
Both are accepted by `GlobalWF` (typing under each declaration's grant),
`Causal`, and — with the trivial clock environment — `WellClocked`. At tick 0
`x` evaluates to the `C`-tagged `1` and `y` to the `C`-tagged `2`, each by a
deterministic derivation (`two_C_values_coexist`, executed; `Ev.det`). "The
value of concept `C`" has no denotation; "the value of declaration `d`" has.

Phase 6's own design `ΔB` — the explicit base/correction composition it calls
correct, `base : MotorAngle` a Source, `corr`, `final : MotorAngle` realized —
has three signatures and two origins of `MotorAngle` (`phase6_not_sigUnique`,
`phase6_not_mkUnique`), and its priority design
`explicit_priority_single_driver` has
`emergencyTarget, normalTarget, selected : MotorAngle`. Phase 8a's `lamp` has
two dimmers providing `Bright`; Phase 14's `Δ` has `dial` and `light`, both
`Brightness`. Multiplicity is pervasive at HEAD, not an edge case.

## 19.3 The notions

Q1 "may several declarations be typed `sem C`", Q2 "may several construct `C`",
Q3 "may several be Sources of `C`" are separated by two definitions
(`ProducerAlternatives.lean`, experimental; nothing enters `Core`):

- `SigProduces Δ d C` — `d`'s signature announces `C` in result position
  (`C ∈ tyView.grant`); `SigUnique Δ` — at most one such `d` per `C`. This is
  production's _produces_ (ADR-0034 §4). It answers Q1 and covers Q3 (a Source
  is an unresolved announcer).
- `MkProduces Δ d C` — `d` **originates** a `C`: its realization constructs `C`
  (`Expr.constructs`, a `mk C` anywhere in the body — including inside a
  `sync`/`delay` initial value) or it is unresolved with `C` in result position
  (a Source). A wire (`declRef`), a transport (`sync`), a memory (`delay`), a
  selection (`ite`) of `C` values is **not** an origin. `MkUnique Δ` — at most
  one origin per `C`. This answers Q2 ∪ Q3, the strongest defensible reading of
  Model B.
- `SigUnique.toMkUnique`: under `GlobalWF`, signature-uniqueness implies
  origin-uniqueness (`constructs_granted`). The converse fails
  (`transport_second_signature`).
- A declaration with several `C`-typed _inputs_ and one output is one producer
  of at most one concept (its result); multi-input is not multi-producer. Both
  notions are decidable on concrete designs (`sigProducesB`, `mkProducesB`,
  `constructsB` with `_iff` lemmas).

## 19.4 Model A — nominal type, many producers

Model A is the kernel at HEAD. Its strongest witness is §19.2. **Ambiguity
result**: a second producer that no term references changes nothing any term
evaluates — `second_producer_invisible` is `update_transparent` instantiated at
`Δx ⊕ y` for the consumer `h : bool := rep x < 5`; `MEv … h v` holds before iff
after. Since every reference is a `declRef` and evaluation is deterministic
(`Ev.det`, `MEv.det`), no judgment of the kernel is made ambiguous by a second
producer: the only thing two producers create is two values, each with its own
name. What Model A does _not_ give is a design-level reading "the `C`" — that
reading is a surface projection (the concept node), and §19.8 says what it
means.

## 19.5 Model B — one producer per concept

`SigUnique` is **structurally refuted**: Phase 8a's `lamp` after flattening has
three declarations of type `sem Tilt` (the source's provided port and both
dimmers' bound required ports — a binding realizes the required port as a wire
to the provider) and two of `sem Bright` (`binding_makes_second_signature`); and
every named transport `xS : C := sync c₂ init x` is a second declaration of type
`sem C` (`transport_second_signature`). A model that counts signatures rejects
every bound component and every named cross-domain transport. (FVD-0160.)

`MkUnique` survives those two — a wire and a transport are not origins — and the
results are:

- **Source ownership**: a Source `s : () -> C` and a formula `f : C := mk C …`
  are two origins (`source_and_formula`). Under `MkUnique` a concept with a
  Source has no computed producer; under Model A they coexist.
- **Refinement**: realizing declarations in the same domain never adds an origin
  (`mkUnique_refine`, hypotheses `GlobalWF Δ₂`, `EnvRefines Δ₁ Δ₂`, no new
  declaration): a declaration that becomes realized was an unresolved announcer
  of every concept its body may construct, so it was already counted. Adding a
  second origin is an edit, never a refinement step.
- **Composition / flattening**: two instances of one component with a shared
  provided concept are two origins after flattening (`lamp_two_origins`), so
  `MkUnique` fails on ordinary reuse; with the concept instance-private the two
  instances originate two _different_ concepts (`private_lamp_two_concepts`,
  from `inst_sem_disjoint`). The boundary rule under which flattening preserves
  origin-uniqueness is therefore: a shared concept is provided by at most one
  instance, or is private — a rule about the system's binding, checkable, not a
  kernel invariant.
- **Clock domains**: a transport is not an origin, but its explicit initial
  value is what it says — `sync c (mk C 0) x` constructs `C` (the initial value
  is a `C` from nowhere) and `sync c 0 x` does not
  (`transport_second_signature`, last two conjuncts). The count is syntactic.
- **State**: the same for `delay`: memory preserves tags
  (`temporal_state_preserves_semantic_identity`) and originates nothing beyond
  its initial value.
- **Physical redundancy**: two temperature sensors are two Sources of one
  concept in Model A (`ΔsensA`); Model B refuses the design as written.
- **Origin is syntactic**: Phase 14's
  `light : Brightness := mk Brightness (rep dial)` is a second origin of what
  `dial` supplies, and the wire `light := dial` is not
  (`rewrap_counts_as_origin`). A lint on `MkUnique` decides by the shape of the
  term; the design-meaning notion of "origin" is not defined (FVI-0030).

`MkUnique` has no consumer in the kernel: no judgment resolves by concept, so
establishing it would let nothing new be proved (§19.7 for the drive edge).

## 19.6 Model C — explicit resolution

Model C admits several candidate producers under an explicit resolution. In this
kernel it needs no new construct: a resolution is a declaration whose formula
selects, blends or bounds over declaration references — Phase 6's
`selected := if emergency then emergencyTarget else normalTarget`, `blended`,
`maxed`, each one declaration over several `C`-typed inputs. Two rewritings are
executed to show the intermediate-concept form has the same downstream trace as
the shared-concept form:

- **Redundant sensors** — `tA, tB : Temperature` Sources and
  `temp := if availA then tA else tB` (Model A, two origins) versus
  `tA : SensorA`, `tB : SensorB`,
  `temp : Temperature := mk Temperature (if availA then rep tA else rep tB)`
  (Model C, one origin): `hot := 300 < rep temp` has the same trace over ticks 0
  … 3 (`sensors_rewriting_same_trace`, executed), and the Model C design is
  origin-unique (`sensorsC_mkUnique`, proved).
- **Manual/automatic override** — `manual, auto, bright : Brightness` versus
  `manual : ManualBrightness`, `auto : AutoBrightness`, one
  `bright : Brightness`: same trace (`override_rewriting_same_trace`, executed).

So explicit resolution is **encodable without a resolver primitive**, the
intermediate concepts are optional (Model A form) or mandatory (origin-unique
form), and each candidate stays a first-class declaration. The rewriting is
mechanical: each candidate of `C` becomes a concept `C_i` with `C`'s
representation, and the resolver is the one `mk C` in the design.

**Necessity-witness search.** A design that _needs_ two origins of one concept —
one that no rewriting with intermediate concepts and explicit selection
reproduces — was looked for among the development's cases: Phase 6's composition
and priority designs, Phase 8a's shared and private components, Phase 14's
re-wrapped Source, Phase 16's two providers of one Source (that is one Source;
`two_providers_same_behavior`), Phase 17's several raw sources (several
provisions of _one_ declaration, `mergeBySource`), Phase 18's recommended
`SensorATemperature`/`SensorBTemperature -> Temperature`. Each has the
explicit-resolution form. **No necessity witness was found; its absence is
recorded, not turned into an impossibility claim** (FVI-0030).

## 19.7 Outputs: β and `SingleDriver` are independent of producers

If producer uniqueness per concept were established, could the driver of an
output accepting `C` be derived from the unique producer of `C`? **No, by
counterexample.** `Δ2out = [x : C := mk C 1, xl := x, xr := x]` with two outputs
`oL, oR : C` and `β = {xl ↦ oL, xr ↦ oR}` is `GlobalWF`, `DriveWF`,
`SingleDriver` and origin-unique (`one_origin_two_outputs`, `driver_not_origin`
— `MkUnique Δ2out` proved), yet `β x = none` and neither driver originates `C`.
One origin feeds two outputs through two non-origin drivers; a selection
(`selected` in Phase 6) is a driver and no origin. `SingleDriver` constrains
_declarations per output_; producer uniqueness would constrain _origins per
concept_ — different invariants over different objects, and the first does not
follow from the second. Phase 6's verdicts (FVD-0050 … FVD-0054) stand
unchanged.

## 19.8 Original intent, and where the documents disagree

- Kernel and decisions: a concept is a type (FVD-0019, FVD-0020, FVD-0022 "a
  mapping is a declared arrow between concepts, not a conversion"). Consistent
  with Model A.
- Phase 6 (FVD-0053 "no runtime arbitration, no implicit priority, no merge
  policy"): alternatives to one output are several declarations of one concept
  resolved by an explicit declaration. Model A with Model C's discipline,
  intermediate concepts not used.
- Phase 18's note recommends
  `SensorATemperature`/`SensorBTemperature -> Temperature` for redundant sensors
  — Model C with intermediate concepts. Same kernel, different style: the two
  documents disagree on the naming discipline, not on a semantic claim.
  Recorded, not resolved here: both forms are legal and trace-equivalent
  (§19.6); which to _recommend_ is FVD-0159's guidance.
- The core-calculus paper's prose says both "a concept is what the designer
  means … a nominal type" (§5) and "the desired steering angle is a value" (§8,
  `driver_is_unit_domain`). The second sentence is about a _declaration_ (the
  driver), and is correct as written; it reads as Model B only if "the steering
  angle" is taken to be the concept. The paper-impact note lists the sentences.
- Production's ADR-0034 §4 defines _produces_ as the signature (`SigProduces`),
  a many-relation with a _Carried by_ list — Model A. The frozen Concept/Output
  projection is consistent with the result of this phase; what the audit adds is
  that the signature notion and the origin notion differ (§19.3) and that a "the
  producer" reading would be wrong.

## 19.9 Models tried

| Model                                     | Accepts / rejects                                                        | Decided by                                                                                   |
| ----------------------------------------- | ------------------------------------------------------------------------ | -------------------------------------------------------------------------------------------- |
| A — nominal type, many producers (HEAD)   | accepts §19.2, Phase 6, 8a, 14; no ambiguity in any judgment             | `second_producer_invisible`, `Ev.det`; kept (FVD-0159)                                       |
| B-sig — one `sem C` signature per concept | rejects every bound component and every named transport                  | `binding_makes_second_signature`, `transport_second_signature`; refuted (FVD-0160)           |
| B-origin — one origin per concept         | rejects shared-concept reuse, Phase 6's composition, a re-wrapped Source | `lamp_two_origins`, `phase6_not_mkUnique`, `rewrap_counts_as_origin`; not a kernel invariant |
| C-primitive — a resolver construct        | nothing it expresses is outside A                                        | `sensors_rewriting_same_trace`, `override_rewriting_same_trace`; not added                   |
| C-discipline — intermediate concepts      | accepted as the surface recommendation; origin-unique designs result     | `sensorsC_mkUnique`; FVD-0159 guidance, `MkUnique` a lint at most (FVD-0160)                 |
| β from the unique producer                | wrong: one origin, two outputs, non-origin drivers                       | `one_origin_two_outputs`, `driver_not_origin`                                                |

## 19.10 Theorems

| Claim                                                                     | Theorem                                                                                         | Hypotheses                                            |
| ------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------- | ----------------------------------------------------- |
| two `C` values, two arrows into `C`, well formed                          | `witness_two_values`, `witness_two_arrows`                                                      | closed designs; `GlobalWF` by `ofList`                |
| two `C` values at one tick, deterministic                                 | `two_C_values_coexist` (executed)                                                               | `evalF`, fuel 16                                      |
| Phase 6's composition has several producers                               | `phase6_not_sigUnique`, `phase6_not_mkUnique`                                                   | Phase 6 `ΔB`                                          |
| a second producer is invisible unless referenced                          | `second_producer_invisible`                                                                     | `I` avoids `y`; via `update_transparent`              |
| bindings and transports are second signatures                             | `binding_makes_second_signature`, `transport_second_signature`                                  | Phase 8a `lamp.flattenΔ`; `WellClocked` transport     |
| signature-uniqueness implies origin-uniqueness                            | `SigUnique.toMkUnique`                                                                          | `GlobalWF`                                            |
| refinement preserves origin-uniqueness                                    | `mkUnique_refine`                                                                               | `GlobalWF Δ₂`, `EnvRefines Δ₁ Δ₂`, no new declaration |
| shared reuse breaks it; private concepts split it                         | `lamp_two_origins`, `private_lamp_two_concepts`                                                 | Phase 8a `lamp`, `privateDimmer`                      |
| Source beside formula: two origins; re-wrap counts, wire does not         | `source_and_formula`, `rewrap_counts_as_origin`                                                 | Phase 14 `Δ`                                          |
| explicit resolution with intermediate concepts: same trace, origin-unique | `sensors_rewriting_same_trace`, `override_rewriting_same_trace` (executed); `sensorsC_mkUnique` | ticks 0 … 3 / 0 … 2, fuel 32                          |
| one origin, two outputs, non-origin drivers; β not derivable              | `one_origin_two_outputs`, `driver_not_origin`                                                   | `DriveWF`, `SingleDriver` by `ofList`                 |

22 theorem-like declarations added; every one on `propext`/`Quot.sound`
(`#print axioms` on all of the above); no `sorry`; the whole development 1 566
across 69 files; `lake build` 72 jobs, clean, no warnings. The Phase 18 report's
"1 545 across 68 files" was 1 544 by the same grep — struck there.

## 19.11 Claim audit

- **Proved**: every row of §19.10 except the three marked executed; the
  refinement result is general (any `Δ₁ ⊑ Δ₂` with the same domain).
- **Executed**: `two_C_values_coexist`, `sensors_rewriting_same_trace`,
  `override_rewriting_same_trace` — finite ticks, concrete inputs; they show the
  rewriting on one design each, not a general rewriting theorem.
- **Tested design failure**: `SigUnique` as an invariant; β-from-producer.
- **Definitional**: multi-input is not multi-producer; `SigUnique → MkUnique`.
- **Not established**: a general trace-preservation theorem for the
  intermediate-concept rewriting; a design-meaning (non-syntactic) notion of
  origin; the necessity witness for two origins (FVI-0030).
- **Design recommendation**: the intermediate-concept discipline for
  alternatives that are _different quantities_ (sensor A's reading, sensor B's
  reading), and the plain shared-concept form for alternatives that are _the
  same quantity from different rules_ (Phase 6's `base`/`corr`/`final`); the
  component boundary rule of §19.5.

## 19.12 Verdicts

- `Ty.sem` as a nominal type, many producers legal — **KEEP IN KERNEL**
  (FVD-0159; the Phase 2 verdict unchanged).
- producer uniqueness per concept (`SigUnique`, `MkUnique`) — **not a kernel
  invariant**; `MkUnique` with the boundary rule **MOVE TO AUTHORING/UI** as an
  optional lint at most (FVD-0160).
- a resolver primitive / concept-level value lookup — **REMOVE** (never added;
  FVD-0159): explicit resolution is an ordinary declaration.
- intermediate concepts for alternatives — **KEEP IN SURFACE** as guidance
  (FVD-0159).
- production: no semantic change; the frozen Concept/Output projection may
  resume on ADR-0034's definition, with the distinction of §19.3 available (the
  note §5). The papers: the impact note only; no revision in this phase.
