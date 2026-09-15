# REPORT — formal results so far

Project state: **Phase 6 complete** (physical outputs + single-driver
discipline).  Remaining: Phase 7 validation + invalidation; Phase 8 surface
elaboration + executable semantics; final minimality audit.  Everything builds
with `lake build`; no `sorry`; axioms used are `propext` and `Quot.sound`
(the latter only through `funext` in `DeclEnv.update_update_same` and
standard `simp` lemmas).  No `Classical.choice` anywhere.

## The kernel in one paragraph

```
DeclEnv         maps DeclId ↦ DesignDecl
DesignDecl      = id : DeclId  ×  interface : DeclInterface  ×  realization : Option Expr
DeclInterface   = expectedType : Ty  ×  commitments : List PropertyId      (monotone, public)
Ty              = bool | nat | arr Ty Ty | sem SemanticId | q Dim           (Phase 2: nominal concepts; Phase 3: quantities)
ConceptEnv Θ    maps SemanticId ↦ Option Ty                                 (Phase 3: representation binding, write-once, sem-free data)
Prim            registered operators; dimension algebra lives in Prim.ty     (Phase 3; Phase 4 adds bool/opt/comparison ops)
declRef d       refers to a declaration by stable identity
rep e / mk s e  observe / construct a semantic value                        (Phase 3; mk only under a grant)
delay init e    the value of e at the previous activation of its own domain (Phase 4; = sync own)
sync c init e   the value of e at the last activation of domain c strictly before now, init if none
                                                                            (Phase 5: the one transport/state primitive)
ClockEnv Κ      maps DeclId ↦ Option ClockId; none = domain-agnostic pure mapping (Phase 5: interface-level, frozen)
Clocked Κ c e   the domain judgment: references stay in their domain unless through sync (Phase 5; typing unchanged)
Sched S         which domains activate at which global ticks; rates are validation data that induce a schedule
typing          HasType Θ Δ G Γ e τ: sees Δ.tyView, the binding Θ s = some R, and the grant G — nothing else
realizations    are typed under Grant.of their own signature: a value of sem s is built only inside a
                declaration that announces sem s
semantics       Ev Δ I t ρ e v (one domain) ⊂ MEv S Δ I c t ρ e v (many domains): tick-indexed evaluation;
                unresolved declarations are inputs; Ty unchanged (no Signal, no Event); executable iff Causal
OutputEnv Ω     maps OutputId ↦ (accepted Ty, ClockId): what each physical sink takes   (Phase 6: resource identity)
DriveEnv β      maps DeclId ↦ Option OutputId: the drive edges; write-once               (Phase 6)
DriveWF         driver type = accepted type ∧ driver clock = sink clock; no coercion, no sync in the binding
SingleDriver β  at most one driver per sink — global, not typing; CompleteOutputs: every required sink driven
validation      may rely on commitments and evidence (Satisfies, GlobalWF)
monotone refinement (DeclLeq / DeclRefines / EnvRefines)   preserves every earlier commitment
arbitrary edit  (retype, drop commitment, detach/replace realization, re-identify)
                is outside the refinement order and may invalidate dependents → recheck
```

"Hole" is no longer a kernel concept.  An unresolved declaration is a
declaration whose `realization` is `none`; the word survives only as a
surface/HCI metaphor (D-15).

Layout:

| File | Contents |
|---|---|
| `BDL/Core/Base.lean` | `SemanticId`, `Dim`, `Ty` (`sem`, `q`), `Ty.SemFree`, `Prim`/`Prim.ty`, `DeclId`, `Expr` (`declRef`, `rep`, `mk`, `prim`), `refs`, `RefFree` |
| `BDL/Core/Interface.lean` | `DeclInterface` (expected type + commitments), `InterfaceRefines` preorder |
| `BDL/Core/Decl.lean` | `DesignDecl`, `DeclEnv`, `tyView`, `ConceptEnv`/`ConceptRefines`/`ConceptEnv.WF`, `Grant`/`Grant.of`/`Ty.grant`, structural order `DeclLeq` / `EnvRefines`, `EnvRefines_update` |
| `BDL/Core/Typing.lean` | `HasType Θ Δ G Γ e τ`, decidable `infer`, weakening, factoring lemmas `mono_env` / `mono_concept` / `mono_grant`, `constructs_granted` |
| `BDL/Core/Satisfaction.lean` | env-dependent `Evidence`, `Evidence.Monotone`, `Satisfies`, `WellFormedDecl`, `DeclRefines`, Theorems 1–6 |
| `BDL/Core/Env.lean` | `GlobalWF`, **`local_refinement_preserves_global_typing`**, **`local_refinement_preserves_global_wf`**, multi-step version |
| `BDL/Core/Dependency.lean` | `DependsOn`, `Reaches`, `Cyclic`/`Acyclic`, `InstDependsOn`, `Causal`, unfolding semantics `Unfolds` (timeless), cycle theorems |
| `BDL/Core/Reactive.lean` | Phase 4: `Value`, `Ev`, `Ev.det`, `evalF`+soundness, strict cycles, logical relation (generic in the application relation), `fundamental`/`reactive_total`, `Ev.tag_provenance`, `unfolds_preserves_eval` |
| `BDL/Core/Output.lean` | Phase 6: `OutputId`, `OutputSpec`/`OutputEnv`, `DriveEnv`, `DriveWF`, `SingleDriver`, `CompleteOutputs`, `first_output_binding_is_monotone`, `PartialOutputWF`/`ExecutableOutputs`, `PhysicalOutput`, `single_driver_output_deterministic` |
| `BDL/Core/Clock.lean` | Phase 5: `Sched`/`prevAct`, `ClockEnv`, `Clocked`/`WellClocked`, `MEv`, `MEv.det`, `mevalF`+soundness, `single_domain_embedding`, `delay_is_sync_own`, `MEv.tag_provenance`, `mfundamental`/`multi_domain_total`, window model, `buffer_from_log_and_cursor` |
| `BDL/Experiments/DeclCounterexamples.lean` | Phase-0 examples; Phase-1 probes 1–6; cycle examples |
| `BDL/Experiments/SemanticTypeAlternatives.lean` | Phase 2: baseline, Models A/B/C, erasure, denotation, counterexamples A–D |
| `BDL/Experiments/RepresentationBindingAlternatives.lean` | Phase 3.1: policies free/none/grant over a local `RExpr`; bypass counterexample; provenance theorem; the surviving grant model |
| `BDL/Experiments/DimensionAlternatives.lean` | Phase 3.2: dimension mismatch, erasure baseline, units as elaboration, semantic ⟂ dimension, rebinding is an edit |
| `BDL/Experiments/ReactiveAlternatives.lean` | Phase 4: cycle examples, derived operators with executed traces, initialization and Event alternatives, delay vs dimensions/semantics/refinement |
| `BDL/Experiments/OutputAlternatives.lean` | Phase 6: identity alternatives (D), Counterexamples A/B/C/E/F/G, explicit priority/blend/max, effect-row and action-value toys, StateHandler remainder, two drivers → two outputs |
| `BDL/Experiments/ClockAlternatives.lean` | Phase 5: the multi-rate design, counterexamples A/B/C/E/F, direct wire vs transport, typing across domains, same-tick-order toy, event policies, clocked-type toy |

---

## Phase 0 (preserved) — a single persistent declaration

Conclusions carried forward unchanged (Phase-0 vocabulary translated):

1. A persistent design declaration is a stable name + a fixed expected type
   + a monotonically growing commitment set + a write-once realization.
   The lifecycle closure is exactly this preorder (`DeclRefinesStar_iff`).
2. Strengthening the interface of a realized declaration must re-verify
   the realization (`DeclRefines.strengthen` carries the premise;
   `naive_breaks_wellformedness`).
3. Identity alone contributes nothing beyond a declaration name to the
   single-declaration theorems.
4. Theorem 4 (`preserves_wellFormed`) has no independent content: its
   hypothesis is unused because the invariant was moved into the definition.
   This is reported, not hidden (`DeclRefines.wellFormed_target`).

---

## Phase 1 — cross-declaration references

### 1.1 The model

* `Expr.declRef : DeclId → Expr`.
* `DeclEnv := DeclId → Option DesignDecl`; `Δ.tyView d := (Δ d).map (·.interface.expectedType)`.
* Typing rule: `Δ.tyView d = some τ ⟹ HasType Δ Γ (declRef d) τ`.  This is
  the only rule that reads `Δ`, and it reads only `tyView`.  **Typing
  depends on the type view of the interface; validation depends on
  commitments and evidence.**  This separation is a deliberate invariant.
* `Evidence : DeclEnv → Expr → PropertyId → Prop` — evidence may consult the
  environment (needed for compositional discharge: "`A` is monotone because
  `B` is committed to be monotone").
* The **order** is separated from the **invariant**:
  * `DeclLeq h₁ h₂` (structural): same id, `InterfaceRefines` on interfaces,
    realization write-once.  `EnvRefines Δ₁ Δ₂`: pointwise `DeclLeq`, new
    declarations allowed.
  * `GlobalWF ev Δ`: every stored declaration is under its own id and its
    realization satisfies its interface *in `Δ`*.

### 1.2 The main theorem, in two halves

**Typing half** — `local_refinement_preserves_global_typing`:

```
Δ B.id = some B  →  DeclLeq B B'  →  ∀ Γ e τ, HasType Δ Γ e τ → HasType (Δ.update B') Γ e τ
```

Hypotheses are purely structural: no evidence, no well-formedness of `B`,
`B'`, or anything else.  In fact only `B'.interface.expectedType = B.interface.expectedType`
is used.  **This theorem is a one-liner and it should be reported as such**:
it is true because typing was *defined* to factor through `tyView`
(`HasType.mono_env`).  Its content is that the "signature-first" design
decision — clients see interfaces, never bodies — is *sufficient* for client
stability.  Probe 4 shows `tyView` preservation is also *necessary*.

**Commitment half** — `local_refinement_preserves_global_wf`:

```
ev.Monotone → GlobalWF ev Δ → Δ B.id = some B → DeclRefines ev Δ [] B B' → GlobalWF ev (Δ.update B')
```

and the multi-step version `local_lifecycle_preserves_global_wf`.  This one
needed a hypothesis that was **not** in the brief and was discovered by
trying to make the theorem fail: `Evidence.Monotone` — the stability
condition for evidence that is meant to survive monotone environment
refinement.  Probe 6 shows the theorem is false without it.

### 1.3 The five probes ("try hard to make it fail")

`A : nat → bool`, `A := λx. f (B x)`, `B : nat → nat` unresolved.  Then:

| Probe | Operation on `B` | Kind | `A`'s typing | `A`'s commitments | Result |
|---|---|---|---|---|---|
| 1 | strengthen interface | refinement | preserved | preserved | theorem instance `probe1_*` |
| 2 | realize | refinement | preserved | preserved; `A` now unfolds to a reference-free program of the same type | `probe2_*` |
| 3a | re-identify **replacing** `B` | edit | **broken** — dangling reference | — | `probe3a_breaks_typing` |
| 3b | re-identify **beside** `B` | edit | preserved | vacuous | `A` still depends on the stale `B`; design can never become executable (`probe3b_*`) |
| 4 | change expected type (id kept) | edit | **broken** | — | `probe4_breaks_typing`; `probe4_id_alone_insufficient` |
| 5 | drop a commitment | edit | **preserved** | **broken** | `probe5_typing_kept`, `probe5_breaks_commitment` |
| 6 | (valid realize, but evidence non-monotone) | refinement | preserved | **broken** | `probe6_breaks`, `badEv_not_mono` |

The "Kind" column is the refinement-vs-edit distinction made explicit by the
migration: probes 3–5 are not refinements and are not covered by any
preservation theorem; they are edits that require rechecking dependents.

Two of these deserve comment.

**Probe 5 is the important negative result.**  Dropping `B`'s `monotone`
commitment does not change a single type; the type checker is silent.  But
`A`'s own `monotone` commitment was discharged *through* `B`'s commitment
(`compEv`), so `A` is now ill-formed without having been edited.
Consequence for the design: **commitments are part of the interface**.  The
interface that clients depend on is `expectedType × commitments`, and both
must be monotone for client stability.  The paper says properties "attach to
the name" (§3.2); this shows they are load-bearing for dependents, which is a
stronger claim than the paper makes.

**Probe 6 is the discovered invariant.**  Any discharge mechanism that
consults the *absence* of information (an unresolved declaration, a missing
commitment) produces evidence that valid refinement destroys.  So evidence
that is intended to survive refinement must be positive/monotone in the
environment.  This is not a decoration on the theorem; `badEv_not_mono`
derives non-monotonicity of the bad evidence from the theorem's failure.
(Evidence that is *not* meant to survive refinement — environment-sensitive
evidence that is rechecked on every change — is a legitimate future
category; it is documented, not implemented.)

### 1.4 Dependency graph and cycles

* `DependsOn Δ a b` iff `a`'s realization refers to `b`.  Interfaces contain
  no references in this model, so there is no interface-level dependency; a
  cycle can therefore never pass through an unresolved declaration
  (`DependsOn.realized`).
* Semantics at this phase is **unfolding** (`Unfolds Δ e e'`): inline
  realized references recursively, stop at unresolved ones.  It is
  deterministic (`Unfolds.det`), type-preserving under `GlobalWF`
  (`Unfolds.preserves_typing`, which needs closed-term weakening), and in a
  fully realized environment produces a reference-free term whose typing no
  longer depends on any environment (`Unfolds.refFree_of_fullyRealized`,
  `HasType.refFree_env_irrelevant`).  This is the formal content of the
  paper's "executable" acceptance level.
* **Every cycle blocks unfolding** (`Unfolds.not_of_cyclic`): a self-reference
  `S := S` and a mutual recursion `P := Q, Q := P` are both *well typed*
  (references are typed by interface) yet have no unfolding.  Conversely
  acyclic environments (rank-witnessed) unfold every term
  (`Unfolds.exists_of_acyclic`).
* There is **no harmless cycle** in this fragment: the pure language has no
  fixpoint, so a cyclic definition denotes nothing.  The distinction
  "structural cycle vs instantaneous computational cycle" cannot yet arise;
  it requires a delay operator (Phase 5/8).  Deferred, not dismissed.
* Classification: realization-acyclicity is a **kernel** well-formedness
  condition beyond typing (the semantic function is undefined otherwise),
  not a validation concern.

### 1.5 Is persistent identity formally non-trivial?

**No.  It is exactly a declaration name — and Phase 1 falsified the idea
that persistent identity is itself a new abstraction.**  Precisely:

* Every Phase-1 theorem that mentions `id` uses it in one way only: to make
  `Δ.update B'` land on the slot `declRef B` resolves to
  (`EnvRefines_update`).  That is what a name does in any environment-based
  semantics.
* What *is* non-trivial is not identity but the **environment order**
  `EnvRefines` and the two facts that clients depend on it only through
  (a) `tyView` for typing and (b) monotone evidence for commitments.  This is
  the standard interface/implementation separation: clients are typed
  against interfaces; bodies can be supplied or refined later.  It is the
  same structure as ML signatures / Coq `Parameter` later given a
  `Definition` / Lean's metavariable context (assignment write-once, types
  fixed), and `Evidence.Monotone` is the familiar "stable under world
  extension" condition of Kripke-style models.
* Two aspects are *slightly* non-standard, and they are where the design
  content sits: (i) the interface includes a growable commitment set, and
  the growth is a first-class operation on a declared-but-undefined name;
  (ii) the kernel imposes a stability condition on the validation layer's
  refinement-surviving evidence.  Neither is a new PL abstraction.

This is why the kernel is now declaration-centric (§M): the model is "an
environment of named declarations with monotone interfaces and write-once
bodies"; the non-trivial invariants live in the order on environments, not
in identity.

### 1.6 Theorems that became trivial by definition (reported per §21)

* `DeclRefines.preserves_wellFormed` (Phase 0) — hypothesis unused.
* `local_refinement_preserves_global_typing` — a one-line consequence of
  making the `declRef` rule read `tyView` only.  Its necessity direction
  (probe 4) is the non-trivial half.

### 1.7 Tension with the paper, recorded

The paper allows *detaching* a definition ("retracts an implementation while
retaining the claim that the relationship exists", §3.2).  In this model a
realization is write-once; detaching is not a `DeclLeq` step.  The formal
reason: detaching `B` does not affect typing of clients (`tyView` unchanged)
but destroys any client evidence that consulted `B`'s realization, i.e. it
is a non-monotone edit.  It can be supported as an *edit* that re-opens
validation of all transitive dependents, but not as a *refinement*.  See
`DESIGN_DECISIONS.md` D-07 and D-16.

---

## §M — Migration: holes → declarations

Performed after Phase 1, before Phase 2.  Semantic-preserving; the
declaration inventory (201 `theorem`/`def`/`structure`/… items) is identical
before and after modulo the rename map, and the axiom profile is unchanged.

### M.1 Which names changed?

| Old | New |
|---|---|
| `HoleId` | `DeclId` |
| `DesignHole` (field `spec`) | `DesignDecl` (field `interface`) |
| `HoleEnv` | `DeclEnv` |
| `Expr.holeRef` | `Expr.declRef` |
| `Expr.HoleFree` (+ `holeFree_*` lemmas) | `Expr.RefFree` (+ `refFree_*`) |
| `HoleLeq` / `HoleRefines` / `HoleRefinesStar` / `HoleRefinesStar_iff` | `DeclLeq` / `DeclRefines` / `DeclRefinesStar` / `DeclRefinesStar_iff` |
| `WellFormedHole` | `WellFormedDecl` |
| `Spec` (field `obligations`) | `DeclInterface` (field `commitments`) |
| `Refines`, `Refines_iff_semantic`, `Refines_addObligation`, `SpecEquiv` | `InterfaceRefines`, `InterfaceRefines_iff_semantic`, `InterfaceRefines_addCommitment`, `InterfaceEquiv` |
| `spec_refines`, `obligations_subset` | `interface_refines`, `commitments_subset` |
| `NaiveHoleRefines` (experiment) | `NaiveDeclRefines` |
| files `Hole.lean`, `Spec.lean`, `HoleCounterexamples.lean` | `Decl.lean`, `Interface.lean`, `DeclCounterexamples.lean` |

Kept unchanged: `tyView`, `Evidence`, `Evidence.Monotone`, `Satisfies`,
`GlobalWF`, `EnvRefines`, `DependsOn`, `Reaches`, `Unfolds`, `HasType`,
`infer`, all probe names.  No aliases were retained.

### M.2 Which semantics changed?

None.  Every definition is textually identical up to the rename; every
theorem statement and proof is unchanged.  The build succeeded on the first
attempt after the mechanical rename, before any docstring was touched.

### M.3 Which semantics intentionally did NOT change?

* `tyView` still exposes only `expectedType`; the `declRef` typing rule
  still reads only `tyView`.  Typing does not see commitments,
  realizations, or evidence.
* `Evidence` remains `DeclEnv → Expr → PropertyId → Prop`, and
  `Evidence.Monotone` is unchanged as a definition.  Only its *description*
  changed: it is the stability condition for refinement-surviving evidence,
  not a claim about all evidence.
* Realization remains write-once; no edit relation was added.
* `DependsOn` remains realization-only; `Unfolds` remains the Phase-1
  semantics; cycle results unchanged.
* Commitments and validation obligations are still the same `PropertyId`;
  the distinction is documented in `Interface.lean`, not implemented.

### M.4 Did any old theorem depend on the hole-centric formulation?

No.  This was tested, not assumed: the rename was applied mechanically and
the whole project compiled without a single proof edit.  Two identifiers
(`HoleRefinesStar_iff`, `NaiveHoleRefines`) were missed by the first
word-boundary pass and renamed in a second; that is a tooling detail, not a
semantic one.

The only place where the old vocabulary was doing conceptual work was in
prose: docstrings that described `realization = none` as "a hole" and
described `Evidence.Monotone` as a property of all valid evidence.  Both
were misleading relative to the Phase-1 results and have been rewritten.

### M.5 Does the declaration-centric model better match the Phase-1 results?

Yes, and the fit is exact rather than cosmetic:

* Phase 1 proved that `id` is used only as an environment key
  (`EnvRefines_update`) — i.e. it *is* a declaration name.  `DeclId` says
  so; `HoleId` suggested a syntactic position that never existed in the
  model (nothing in `DesignDecl` mentions where a reference occurs).
* Probe 5 proved that commitments are load-bearing for dependents — i.e.
  they are part of the public interface.  `DeclInterface.commitments` says
  so; `Spec.obligations` framed them as private proof duties.
* Probes 3–5 showed that retyping, dropping commitments, and
  re-identification are not covered by any preservation theorem.
  Documenting the refinement/edit split names that fact instead of leaving
  it implicit in which relations happen to exist.

### M.6 Kernel concepts vs surface metaphors, now

| Kernel (formal object) | Surface metaphor / display |
|---|---|
| `DeclId` — ordinary declaration key | "hole", display name, `?f` notation |
| `DesignDecl` with `realization = none` | "unresolved typed hole", "signature-first block" |
| `DeclInterface` = type + commitments | "signature" plus "declared properties" |
| `InterfaceRefines` / `DeclLeq` / `EnvRefines` | "progressive formalization" |
| edits outside the order (retype, drop, detach, replace, re-identify) | "editing the block" — must trigger rechecking |
| `tyView` | what the type checker shows |
| `Evidence`, `Evidence.Monotone` | validation overlay |

### M.7 Ready for Phase 2?

Yes, with two caveats stated honestly:

1. The vocabulary is clean, but the *representation* still carries one
   Phase-0 shortcut: `commitments : List PropertyId` doubles as the set of
   validation obligations.  Phase 2 (semantic types) does not need to
   resolve this; Phase 11 (validation) will.
2. No edit relation exists.  Phase 2 will add semantic-type declarations;
   if it needs to talk about "changing a declaration's semantic type", it
   will have to say *edit*, not *refine*, and there is currently no formal
   object for that.  This is intentional (nothing forces it yet), but it is
   the first thing to revisit if Phase 2 needs invalidation tracking.

No hole-centric terminology remains in the kernel, the experiments, or the
documents except where "hole" is named explicitly as a surface metaphor.

---

## Phase 2 — where does semantic identity live?

### 2.1 The baseline failure (Counterexample A)

With concepts represented only by representation types (`Tilt ↦ nat`,
`MotorAngle ↦ nat`), the direct wire `motorTarget := declRef tiltSensor` is
well typed and the design is globally well formed
(`counterexampleA_baseline_accepts_invalid_wire`).  Nothing in the model can
reject it because nothing in the model records the distinction.

### 2.2 Models tried

**Model A — nominal semantic types.**  `SemanticId` (internal, distinct from
`DeclId` and from display names) and one constructor `Ty.sem : SemanticId → Ty`
with *no* introduction or elimination forms in the pure fragment.

| Result | Lean |
|---|---|
| mismatch rejected statically | `semantic_identity_mismatch_rejected` |
| like-to-like sharing of a concept by several declarations | example after it |
| explicit semantic mapping `tiltToMotor : Tilt → MotorAngle` (a declared design relationship, itself unresolved) makes the connection well typed; the mapping is visible in the term | `explicit_semantic_mapping_accepted` |
| identity established before realization | example: every declaration in `ΔA_good` except the wire is unresolved |
| **erasure soundness**: semantic typing ⇒ representation typing | `HasType.erase` |
| erasure is not injective, and **the baseline is erased Model A** | `erase_not_injective`, `baseline_is_erased_modelA` |
| conservativity: sem-free programs get only sem-free types | `semantic_extension_preserves_structural_typing` |
| refinement preservation inherited unchanged from Phase 1 | `semantic_check_preserved_under_interface_refinement` |
| identity change is not a refinement and breaks clients (**Counterexample B**) | `semantic_identity_change_is_not_refinement`, `semantic_identity_change_breaks_client` |
| rename preserves identity; name-as-identity makes rename destructive (**Counterexample C**) | `semantic_rename_preserves_identity`, `rename_under_name_identity_breaks_client` |
| semantic values originate only from declarations (denotational proof, `sem ↦ Empty`) | `no_semantic_value_without_declaration` |

**Model B — semantic role as interface data, typing unchanged.**
`InterfaceB = expectedType × semanticRole : Option SemanticId × commitments`;
typing sees the representation type; a separate judgment checks roles.

| Result | Lean |
|---|---|
| **Counterexample D**: typing accepts the invalid wire; only the second judgment rejects it | `counterexampleD_typing_accepts_semantic_check_rejects` |
| the direct-wire checker is **evaded by η-expansion** `(λx. x) tilt` — same flow, no direct wire, both checkers silent | `bweak_evaded_by_eta` |
| role change keeps every type but flips the verdict on *unchanged* clients — an edit, exactly like a type change | `role_change_flips_unchanged_clients` |
| a checker that enforces identity through arbitrary term structure must reason compositionally about semantic flow (variables, lambdas, applications, references); the tested strong formulation — a role per subterm with role arrows — has the rule shapes of `HasType` over `Ty`-with-`sem` and runs alongside representation typing, which it implies (`HasType.erase`); in that formulation it duplicates nominal typing with no observed benefit | argued in §B.2, **not proved**; no definition was written because the tested formulation would coincide with `HasType` |

Conclusion for Model B, with claim strength:

* *B-weak (direct-wire metadata checker)*: **formally rejected by
  counterexample** (`bweak_evaded_by_eta`, Counterexample D).
* *B-strong (compositional role judgment)*: **tested formulation redundant
  with nominal typing; the broader family not universally ruled out.**
  Flow-sensitive, indexed/effect-like, abstract-interpretation, or
  relational semantic analyses were not formalized and no theorem here
  excludes them.  What the mechanized evidence does establish is that any
  sound checker must be compositional over terms, i.e. of type-system
  strength, and that the one tested has no benefit over putting identity in
  the type.  Its one distinctive feature — a "type-correct but semantically
  pending" state — costs the guarantee that structural typing implies
  connectability.

**Model C — concepts as *ordinary* `DesignDecl`s, identity = `DeclId`.**

| Result | Lean |
|---|---|
| category error 1: the concept is usable as a *value* (`declRef Tilt : nat`) | `conceptC_usable_as_value` |
| category error 2: the concept can be realized by a number, as a legal refinement step | `conceptC_realizable_by_a_number` |

Conclusion for Model C, with claim strength:

* *Concept = ordinary `DesignDecl` in the value sort*: **formally rejected by
  the two category-error counterexamples.**
* *Stratified concept-declaration family* (`ConceptDecl = id × displayName ×
  Option representation` in a distinct sort): **not rejected.**  But once
  concepts inhabit a distinct category with independent identity, the
  Phase-2 kernel requirement is again an independent `SemanticId` — Model
  A's core — and the remaining fields are representation metadata, deferred
  to Phase 3.  So this family does not offer a *smaller* Phase-2 kernel; it
  offers a home for Phase-3 data.

### 2.3 The surviving model and the answer to §18

> **Among the tested designs, the smallest mechanism that enforces semantic
> non-interchangeability compositionally, without a second semantic
> analysis, is one nominal type constructor `Ty.sem : SemanticId → Ty`,
> over an internal identity distinct from declaration identity and from
> display names, with no introduction or elimination forms.**

This is a claim about the tested designs, not a proof that nominal typing is
the only possible mechanism in principle (see §2.7).  Why it is minimal
among them and sufficient:

* *Non-interchangeable by default:* `sem s₁ = sem s₂ ↔ s₁ = s₂`
  (`sem_injective`), so two concepts with the same representation are
  distinct types, and the ordinary STLC rules reject the wire.
* *Explicit semantic mappings still allowed:* a mapping is an ordinary
  declaration of arrow type `sem a → sem b` — a design relationship between
  concepts, not a coercion, cast, or representation conversion.  No such
  mechanism exists in the kernel; the mapping is visible in the term and is
  itself a signature-first declaration that may remain unresolved.
* *Nothing else changed:* `DeclInterface` unchanged, `tyView` unchanged, all
  Phase 0/1 theorems unchanged.  The only proof that had to change was
  `InterfaceRefines_iff_semantic`, which used a canonical closed inhabitant
  of every type; opaque semantic types have none, and the replacement —
  inhabit any type by an *unresolved declaration* (`DeclEnv.single_hasType`)
  — is itself a signature-first observation.
* *Erasure:* `HasType.erase` shows Model A is conservative over the
  representation language (generated code is well typed after erasing
  concepts), and `baseline_is_erased_modelA` shows the baseline is exactly
  what erasure leaves behind.

What was deliberately *not* added: representation binding (`mk`/`rep`).
`no_semantic_value_without_declaration` proves that without it a semantic
value can only come from a declaration of semantic type.  That is the
correct Phase-2 state: it separates *distinctness* (needs only the nominal
constructor) from *realizing a mapping by a formula* (needs a representation
binding, which is Phase-3 material where the representation is `Q[d]`).

### 2.4 Answers to §15

| Question | Answer |
|---|---|
| Did `Ty` change? | Yes: one constructor `sem SemanticId`.  This was the only acceptable kernel change; §2.2 shows both alternatives fail or reduce to it. |
| Did `DeclInterface` change? | No. |
| Did `tyView` change? | No.  Semantic identity rides inside `expectedType`; typing still consults `tyView` only. |
| Is semantic identity change refinement or edit? | **Edit**, in every model.  In A it is a type change (`InterfaceRefines` fails, clients break); in B a role change flips verdicts on unchanged clients while keeping every type.  So a semantic role field would have to be frozen exactly like the type — which is the argument for putting it *in* the type. |
| How are explicit semantic mappings represented? | As ordinary declarations of type `sem a → sem b`.  No kernel relation, coercion, or cast. |
| What does this mean for the paper's `Sem[n, d]`? | The nominal half is right and is the whole of the Phase-2 result, with one correction: `n` must be an internal identity, not the display name (Counterexample C).  The `d` component is Phase 3.  `mk_n`/`rep` are representation binding: needed to attach formulas, not for distinctness.  The paper's "no global `Real → Brightness` coercion" is exactly `erase_not_injective` + nominal typing. |

### 2.5 Classification (§13)

| Candidate construct | Verdict | Reason |
|---|---|---|
| `SemanticId` | KEEP_IN_KERNEL | the identity `Ty.sem` refers to; distinct from `DeclId` (Model C) and from names (Counterexample C) |
| nominal `Ty.sem` constructor | KEEP_IN_KERNEL | the whole mechanism |
| interface semantic field (`semanticRole`) | REMOVE (for the tested design) | Model B: would have to be frozen like the type; the tested design is dominated by putting identity in the type |
| separate semantic-compatibility judgment | tested weak form: REMOVE; general compositional-analysis family: NOT universally ruled out | weak: η-evaded (formal); strong: tested formulation redundant (argued) |
| explicit semantic mapping | KEEP_IN_SURFACE; represented as an ordinary declared arrow `sem a → sem b` | a design relationship, not a conversion; representation-level `mk`/`rep` pending Phase 3 |
| concept as ordinary `DesignDecl` | REMOVE | two category errors (formal) |
| stratified `ConceptDecl` | NOT REQUIRED IN PHASE 2; may reappear as surface/representation metadata in Phase 3 | not rejected; reduces the Phase-2 identity requirement to an independent `SemanticId` |

### 2.6 Critical remarks

* Model A is, once again, a standard construction: `Ty.sem` is a nominal
  abstract type (a `newtype` with no unwrapping in the pure fragment).  The
  Phase-2 contribution is the *negative* result — that the two tested ways
  to keep semantic identity out of the type system (a metadata field with a
  direct-wire checker; concept as ordinary value declaration) each fail for
  a concrete, mechanized reason — not the positive one.
* `no_semantic_value_without_declaration` is the sharpest statement of what
  the pure kernel now is: a language in which semantic quantities are
  *opaque* and flow only through declared relationships.  That matches the
  paper's intent, but it also means Phase 3 cannot avoid a representation
  binding if formulas are to realize mappings — and that binding will be the
  first place where the kernel's "typing sees only `tyView`" invariant is
  tested by something other than a rename.

### 2.7 Claim strength (methodological note)

Formal counterexamples reject the *specific tested design*, not every
conceivable design in the same informal family.  This project distinguishes
four strengths of conclusion and labels each rejected model with one:

| Strength | Meaning |
|---|---|
| **proven impossibility** | a theorem excludes the whole family |
| **tested design failure** | a mechanized counterexample breaks the specific formulation |
| **reduction/equivalence by proof** | a theorem shows one design is a special case of another |
| **engineering preference** | argued, not proved |

Phase-2 labels:

| Rejected design | Strength |
|---|---|
| Model B weak (direct-wire metadata checker) | tested design failure (`bweak_evaded_by_eta`, `counterexampleD_*`) |
| Model B strong (compositional role judgment) | engineering preference: tested formulation redundant with nominal typing; broader class of compositional analyses **not** universally ruled out |
| Model C as ordinary `DesignDecl` | tested design failure (`conceptC_usable_as_value`, `conceptC_realizable_by_a_number`) |
| Model C stratified declaration family | **not rejected**; reduces the Phase-2 identity requirement to an independent `SemanticId` |
| baseline = erased Model A | reduction by proof (`HasType.erase`, `baseline_is_erased_modelA`) |

Nothing in Phase 2 is a proven impossibility.  The same discipline applies
to later phases.

### 2.8 Phase 2 claim audit

1. **Which claims were too strong?**  (a) That a compositional Model-B
   checker "is `HasType` verbatim", hence that Model B "collapses exactly"
   to Model A.  (b) That Model C — "semantic concepts as declarations" — is
   rejected as a family.  (c) The word "conversion" for `Tilt → MotorAngle`,
   which suggested a coercion the kernel does not have.  (d) The §18 answer
   as originally phrased read as "the smallest mechanism" simpliciter.
2. **What was formally established instead?**  (a) The weak checker is
   unsound (η-evasion); semantic-role changes invalidate unchanged clients;
   any sound checker must be compositional over terms; the one strong
   formulation tested duplicates nominal typing.  (b) Concepts cannot be
   ordinary `DesignDecl`s in the value sort (two category errors).  (c) The
   only cross-concept path in the kernel is a declared arrow; there is no
   conversion mechanism at all.  (d) `Ty.sem` is the smallest mechanism
   *among the tested designs*.
3. **Which model families remain logically possible?**  Compositional
   semantic analyses other than the role-per-subterm formulation
   (flow-sensitive, indexed/effect-like, abstract-interpretation,
   relational); stratified concept-declaration sorts with independent
   identity.  Neither has a mechanized argument for or against it here.
4. **Why does `Ty.sem` still survive as the minimal tested solution?**  It is
   one constructor, changes neither `DeclInterface` nor `tyView`, leaves
   every Phase 0/1 theorem untouched, rejects the invalid wire by ordinary
   STLC rules, admits explicit mappings as ordinary declarations, and is
   conservative over the baseline by `HasType.erase`.  Every tested
   alternative either fails formally or contains an independent
   `SemanticId` anyway.
5. **What new obligation does Phase 2 impose on Phase 3?**  Representation
   binding must not destroy the nominal distinction.  See "Open items" below
   and D-25.
6. **How could representation binding accidentally defeat semantic
   identity?**  With unrestricted `rep : sem s → R` and `mk : R → sem s`
   available to every term, `mkMotor (repTilt x)` is a well-typed
   `Tilt → MotorAngle` path with no declared semantic mapping.
   `no_semantic_value_without_declaration` would become false and the
   nominal distinction ceremonial: the type checker would enforce only that
   the two words `mk`/`rep` appear, not that a design relationship was
   declared.

---


## Phase 3 — representation binding and physical dimensions

### 3.1 First task: try to break Phase 2

The obvious dangerous model — global `rep_s : sem s → R` and
`mk_s : R → sem s` for every concept — was built (`Policy.free`) and
attacked.  It breaks immediately:

| Attack | Lean | Strength |
|---|---|---|
| `λx. mkMotor (repTilt x) : Tilt → MotorAngle` in the **empty** environment — no declaration, no mapping | `unrestricted_representation_binding_bypasses_semantic_identity` | **formally rejected by counterexample** |
| `mkMotor 0 : MotorAngle` from nothing | `unrestricted_mk_creates_semantic_values_from_nothing` | formal |
| the crossing hides inside `brightnessCtrl : Tilt → Brightness`, whose signature says nothing about motors | `hidden_crossing_inside_unrelated_body` | formal |
| Phase-2 provenance (`no_semantic_value_without_declaration`) becomes false | `modelA_breaks_phase2_provenance` | formal |

So **yes: unrestricted `mk`/`rep` breaks semantic isolation**, and the
Phase-2 nominal distinction would be ceremonial under it.  Model A is
rejected.

A second, less obvious hazard surfaced while setting this up: if a concept
may be *represented by* another semantic type (`Θ tilt = some MotorAngle`),
then `rep` itself is a hidden mapping — under every policy, even
observation-only (`binding_to_semantic_type_is_hidden_mapping`).  Hence
`ConceptEnv.WF`: representation types are sem-free.  This is a constraint the
brief did not anticipate.

### 3.2 Models tried (representation binding)

All four are one judgment `RHasType Θ Δ P` with a *construction policy*
`P ∈ {free, none, grant G}`; the binding witness (Model D) is
`Θ s = some R`, required by both `rep` and `mk` in every model.

| Model | Policy | Verdict | Strength |
|---|---|---|---|
| A symmetric unrestricted | `.free` | bypass (§3.1) | formally rejected |
| B observation only | `.none` | safe — `provenance` holds for every concept — but **no mapping can be realized by a formula**: in an environment with only a tilt sensor, no closed term has type `Tilt → Brightness` (`modelB_cannot_realize_mapping`) | formally proved limitation |
| C realization-local construction | `.grant (Ty.grant τ)` where `τ` is the realized declaration's own signature | survives every attack; see §3.3 | formally proved |
| D explicit witness | `Θ s = some R` | is the binding *in* every model; on its own permits nothing — operations are governed by the policy | reduction: D is a component of C, not an alternative |
| E "mappings are the only cross-id path" | — | holds in the *occurrence* form: `constructs_granted` | formally proved |

The distinction the brief asked for — *observing* representation vs
*creating* semantic identity — is exactly the asymmetry Model B exposes:
observation is safe everywhere (`observation_is_available`,
`modelB_provenance`); creation is what must be controlled.  Model C controls
it by the smallest possible authority: the signature of the declaration
being realized.

### 3.3 The surviving model (promoted to core)

* `ConceptEnv Θ : SemanticId → Option Ty` — write-once representation
  binding (`ConceptRefines`; `ConceptEnv.bind`), sem-free (`ConceptEnv.WF`).
* `Expr.rep e` — typed `R` when `e : sem s` and `Θ s = some R`; available
  everywhere.
* `Expr.mk s e` — typed `sem s` when `e : R`, `Θ s = some R`, **and the
  grant permits `s`**.
* `Grant := SemanticId → Prop`; client code is typed under `Grant.none`; a
  realization under `Grant.of τ = (· ∈ τ.grant)`, the concepts in result
  position of its own signature (`Satisfies`).
* `Prim` — registered operators with dimensioned types (§3.5).

Results, all formally proved unless marked:

| Result | Lean |
|---|---|
| the global bypass, written with explicit `rep`/`mk`, is ill-typed in client code | `representation_binding_does_not_enable_hidden_semantic_mapping` |
| a declared mapping's body may observe its input and construct its output | `explicit_semantic_mapping_can_use_representation_formula` |
| the hidden crossing of §3.1 is rejected under `brightnessCtrl`'s own grant; declaring `tiltToMotor` makes it legal and visible | `hidden_crossing_rejected_under_grant`, `declared_crossing_realizable` |
| **provenance** (per-concept denotation, `sem t ↦ ∅`, others `↦ Unit`): if `t` is not granted and no declaration has a `t`-source type, no closed term does | `provenance`, `grant_provenance` |
| **occurrence invariant** (Model E): a well-typed term constructs `s` only if granted `s`; under `Grant.of τ`, only inside a realization announcing `sem s` | `HasType.constructs_granted` |
| binding a representation is monotone: typing, satisfaction, global WF all survive | `HasType.mono_concept`, `GlobalWF.of_conceptRefines` |
| unbound concepts still wire (signature-first at the type level); only `rep`/`mk` wait for the binding | `unbound_concept_still_wires` |
| **Counterexample D**: rebinding `Tilt ↦ nat` to `Tilt ↦ bool` breaks an existing realization and is not `ConceptRefines` | `representation_change_is_edit_not_refinement` |
| erasure soundness survives: `rep`/`mk` erase to their argument, generated code is well typed | `HasType.erase` (Phase-3 form) |
| unfolding preserves typing **under the universal grant** | `Unfolds.preserves_typing` |

The last line deserves a remark rather than a footnote.  Each inlined body
was typed under the grant of *its own* signature, so the flattened program
contains `mk`s that were individually authorized at their declarations.  The
unfolded program is the implementation, where design-time isolation has
been *discharged*, not violated: `constructs_granted` holds for every body
separately, and the flattened term is checked under `Grant.all` because the
authorization already happened.  Semantic isolation is a property of the
design graph, not of the executable.

**Did `tyView` change?**  No.  **Did a new judgment become necessary?**
Not a separate one: typing gained two parameters — the concept environment
(read only through `Θ s = some R`) and the grant.  The brief's suggested
split (`HasType` for structure, `Realizes` for bodies) is realized as one
judgment family indexed by the grant, with client code at `Grant.none` and
realizations at `Grant.of` their signature.  This is reported as the major
Phase-3 design result: **typing now consults a second, concept-level
projection**.  The Phase-1 declaration-level invariant (`tyView` only) is
intact.

### 3.4 Answers to the provenance test (§7)

The desired stronger property — a value of `sem t` either originates from a
declaration typed as a `t`-source or is produced inside an explicit mapping
whose codomain is `sem t` — holds in two complementary forms:

* *denotational*: `provenance` / `grant_provenance` (closed terms outside a
  `t`-granted realization have no `t`-source type unless a declaration does);
* *syntactic*: `constructs_granted` (`mk t` occurs only under a `t` grant,
  i.e. inside a realization announcing `sem t`).

"A MotorAngle cannot arise from a Tilt solely through erasure and
reconstruction" is `representation_binding_does_not_enable_hidden_semantic_mapping`
together with `shared_dimension_no_hidden_mapping` (with dimensions present).

### 3.5 Dimensions

`Ty.q d`, `d : Dim` an exponent vector over Length/Time/Angle; the algebra is
in the types of registered operators:

    add d : q d → q d → q d      mul d₁ d₂ : q d₁ → q d₂ → q (d₁+d₂)      div d₁ d₂ : … → q (d₁−d₂)

No dimension-specific typing rule exists; an application is checked by
ordinary STLC against `Prim.ty`.

| Result | Lean | Strength |
|---|---|---|
| **Counterexample B**: erasing every dimension to `q 0` (the numeric baseline) accepts `length + time`, and can no longer tell the two sensors apart; the erasure is sound | `counterexampleB_baseline_accepts_length_plus_time`, `HasType.eraseDim` | reduction by proof: the baseline *is* erased dimensional typing |
| `length + time` rejected; `length / time : q ⟨1,−1,0⟩` | `dimension_mismatch_rejected`, `velocity_typed` | formal |
| addition requires equal dimensions (by inversion) | `dimensional_addition_requires_equal_dimensions` | formal |
| **units are surface**: a literal `n u` elaborates to `prim (lit u.dim (n·u.scale))`; typed by the unit's dimension in any environment; changing the unit changes the value, never the type; mixed-unit addition works after elaboration | `unit_scaling_preserves_dimension`, `unit_change_is_value_not_type` | formal |
| **Counterexample C**: Tilt and MotorAngle both bound to `q Angle` remain distinct types; the direct wire is still rejected | `same_dimension_does_not_imply_same_semantic_identity` | formal |
| a mapping realized by a dimensioned formula `λx. mk bright (rep x · gain)` with `gain : q (0−Angle)`; a dimension error *inside* the formula is caught by the same typing; the formula cannot manufacture a MotorAngle despite the shared dimension | `explicit_semantic_mapping_uses_dimensioned_formula`, `dimension_error_inside_mapping_rejected`, `shared_dimension_no_hidden_mapping` | formal |
| **Counterexample D**: rebinding `Tilt ↦ q Angle` to `q Length` breaks the realization; not a `ConceptRefines` | `representation_change_is_edit_not_refinement'` | formal |
| dimensions as metadata / validation | not formalized | engineering preference: `mul`/`div` *produce* dimensions, so any checker recomputes `Prim.ty`-driven inference; the tested alternative (erasure) cannot distinguish; broader family not ruled out |

Affine units (°C vs K) are not modelled; the elaboration here is linear
scaling only, matching the paper's own restriction.

### 3.6 Answers to §22

| Question | Answer |
|---|---|
| 1. Does unrestricted `mk`/`rep` break semantic isolation? | Yes — three formal counterexamples (§3.1). |
| 2. Surviving representation-binding model? | Write-once witness `Θ s = some R` (sem-free) + `rep` everywhere + `mk s` only under the realized declaration's own grant (§3.3). |
| 3. Can formulas implement explicit semantic mappings? | Yes, inside the mapping's realization (`explicit_semantic_mapping_can_use_representation_formula`, dimensioned form in §3.5). |
| 4. Can cross-identity changes occur without declared mappings? | Not in client code (provenance), and `mk s` occurs only inside a realization announcing `sem s` (`constructs_granted`).  A declaration *of* `sem s` (e.g. `motorTarget : MotorAngle := mk motor (rep tilt)`) is itself the declared source — the crossing is visible in its signature. |
| 5. Do dimensions belong in the type system? | Among tested designs, yes: `Ty.q d` with the algebra in `Prim.ty`; the numeric baseline is its erasure. |
| 6. Units kernel or surface? | Surface: elaborated to scaled dimensioned literals; never in `Ty`. |
| 7. Is semantic identity independent of dimension? | Yes (Counterexample C); `Ty.sem s` is not indexed by `d`; the dimension is the concept's *representation*, stored in `Θ`. |
| 8. Where is the semantic-to-representation association stored? | In `ConceptEnv Θ`, a concept-level environment separate from `DeclEnv` and from `DeclInterface`; it is typing-visible (through `Θ s = some R` only). |
| 9. Is changing the binding a refinement or an edit? | Binding an unbound concept is a refinement (`ConceptRefines`, monotone).  Rebinding is an edit (Counterexample D, both forms). |
| 10. Did `tyView` remain unchanged? | Yes. |
| 11. Did a new realization-level judgment become necessary? | Typing gained a grant parameter; realizations and client code are the same judgment at different grants.  Typing also gained the concept environment — the major design change. |
| 12. Implication for `Sem[name, dimension]`? | Phase 2 + 3 yield `Ty.sem s` + `Θ s = some (q d)`, not a two-index constructor.  The paper's `mk_n`/`rep` are right in kind but must not be global: `mk` is licensed by the signature of the declaration being realized.  The paper's "units live at the boundary, not in the kernel" is confirmed; "dimensions in the kernel" is confirmed among tested designs. |

### 3.7 Q1 and Q2 (the Phase-3 result)

**Q1.**  Among the tested designs, the smallest representation-binding
mechanism that lets formulas implement semantic mappings without permitting
implicit cross-semantic reconstruction is: a write-once, sem-free binding
witness `Θ s = some R`; an unrestricted observation `rep : sem s → R`; and a
construction `mk s : R → sem s` licensed **only by the signature of the
declaration being realized** (`Grant.of`).  Observation is safe (Model B);
construction is the whole hazard (Model A); the signature is the smallest
authority that makes construction visible at the design level (Model C).

**Q2.**  Among the tested designs, the smallest dimensional mechanism that
rejects dimensionally invalid computation while keeping semantic identity
independent of representation is: a quantity type `q d` over an
exponent-vector `Dim`, with the algebra placed in the types of registered
operators and *no* dimension-specific typing rule; semantic concepts are
bound to `q d` through `Θ`, never indexed by `d`; units are elaborated away.

Neither answer is a proof that no other mechanism could work (§2.7
discipline): the metadata/validation families were argued against, not
excluded.

### 3.8 Critical remarks

* The grant mechanism is, once again, a known shape — it is a *capability*
  attached to a definition site, or equivalently the private constructor of
  an abstract type exported only to the module that declares it.  Its
  contribution here is *where* the capability comes from: the signature the
  designer already wrote, so no new annotation is needed.
* `Unfolds.preserves_typing` had to move to `Grant.all`.  That is the honest
  price of the design: isolation is a design-graph property and does not
  survive inlining as a *type* property.  It survives as provenance (each
  `mk` in the flattened term was authorized somewhere), which is what one
  wants of generated code, but a reader expecting "the executable is
  semantically typed" should not be told that.
* Typing now reads two environments.  The Phase-1 slogan "typing sees only
  `tyView`" is true of declarations and false of concepts; the accurate
  slogan is "typing sees the type view of declarations and the
  representation view of concepts, and nothing else."


## Phase 4 — Reactive Core

### 4.1 The weakest temporal model, and what was built on it

Start point: a **tick-indexed evaluation relation** `Ev Δ I t ρ e v` over the
existing expression language, with one new primitive `delay init e` and no
new types.  Every declaration is a stream by *interpretation*; unresolved
declarations are the inputs (`I : DeclId → Nat → Value`); a realized
declaration is evaluated at tick `t` from its body; `delay init e` at tick
`t+1` evaluates `e` at tick `t`, and `init` at tick 0.  That is the whole
temporal kernel.  Everything the brief listed as a candidate primitive was
then attacked for eliminability (§4.4, §4.5).

Two typing constraints on `delay` came out of the totality proof, not out of
taste:

* **data-typed** — `τ.Data` (no arrow inside).  A delayed closure would have
  to persist across ticks; the logical relation for closures is tick-indexed
  and cannot be transported.  So temporal state stores values, not behaviour.
* **top level** — empty context.  A delay under a lambda would re-evaluate its
  operand at the previous tick under an environment created at the current
  tick.  So temporal state belongs to declarations; mappings are pointwise.
  (Lustre: `pre` lives in nodes, not in functions.)  Consequence: function
  abstraction over *stateful* behaviour (a reusable filter) needs
  instantiation into fresh declarations — a Phase-8 elaboration concern, not
  a kernel construct.

Both constraints also scoped a Phase-1 result: context weakening, hence
inlining a body under binders (`Unfolds.preserves_typing`), now carries a
`DelayFree` hypothesis.  That is the domain of validity §7 asked for, not a
weakening: the Phase-1 statements are unchanged on the timeless fragment
(`Causal_iff_acyclic_of_delayFree`, `InstDependsOn_iff_DependsOn_of_delayFree`).

### 4.2 Results (claim strength in brackets)

| Result | Lean | Strength |
|---|---|---|
| **`reactive_step_deterministic`**: one tick, one environment, one term — at most one value; no evaluation order is hidden | `Ev.det` | formally proved |
| executable interpreter, sound for `Ev`; all traces below are `decide`-checked | `evalF`, `evalF_sound` | formally proved |
| **`instantaneous_cycle_rejected`**: a strict cycle (through no lambda and no delay) has no value at any tick | `Ev.not_of_strictCyclic`, `algebraic_loop_no_value`, `mixed_no_value` | formally proved |
| **`delayed_cycle_is_causal`**: `A := delay 0 B, B := A` is structurally cyclic (no unfolding), causal, and runs at every tick; likewise self-delay | `delayed_loop_does_not_unfold`, `delayed_loop_causal`, `delayed_loop_runs`, `self_delay_runs` | formally proved |
| **totality**: causal + globally well formed + well-typed inputs ⇒ every declaration has a value at every tick, related to its type | `fundamental`, `reactive_total`, `Ev.red` | formally proved (logical relation, induction on (tick, rank, derivation)) |
| **`temporal_state_preserves_semantic_identity`**: with delays, closures and primitives present, if no signature announces `sem s` and no input carries `s`, no value at any tick carries `s` | `Ev.tag_provenance`, `temporal_state_preserves_semantic_identity` | formally proved |
| `delay_preserves_type` / `temporal_state_preserves_dimension`: the rule is `delay : τ → τ → τ` for data `τ`; a backward difference over a time step has dimension `Length − Time` with no derivative primitive | `HasType.delay`, `delay_preserves_dimension`, `backward_difference_rate_typed` | formally proved |
| representation access is not stateful: `rep (delay i x) ≡ delay (rep i) (rep x)`; re-labelling a *stored* tilt still needs the grant | `rep_delay_commute`, `semantic_delay_typed_and_isolated` | formally proved |
| **unfolding vs stepping**: acyclic ⇒ causal; on wiring designs (no lambdas/variables) stepping the unfolded program equals stepping the references | `Causal.of_acyclic_bounded`, `unfolds_preserves_eval` | formally proved; higher-order case not formalized (closure equivalence) |
| `event_encoding_equivalent` (single domain) / `event_encoding_loses_multiplicity` (cross-domain observation) | §7 of the experiment | formally proved, both |
| `count_desugars_to_state` etc. — `previous`, `hold`, `count`, `since`, `once`, `every`, `rise` as declaration graphs, each executed on a concrete input trace | `*_trace`, `ops_well_typed`, `ops_causal` | formally proved by execution (typing + trace); no general equivalence theorem, because there is no independent kernel definition to be equivalent *to* |
| `statehandler_desugars_to_reactive_core` — activation, entry (rising edge), reset-on-entry local state, zero when inactive | `enter_trace`, `scoped_counter_trace` | formally proved by execution on one representative behaviour; see §4.11 for what this does *not* establish |
| missing initialization: undefined or nondeterministic first tick | `first_tick_undefined_without_init`, `first_tick_nondeterministic_without_init` | formally rejected by counterexample (toy relations) |
| temporal changes (add/remove a delay, change init) are edits, not `DeclLeq` | `temporal_change_is_edit` | formally proved |

### 4.3 Cycles: what replaces blanket acyclicity

Three reference sets now exist, and the distance between them is the
content of the causality result:

| Set | Excludes | Used for |
|---|---|---|
| `refs` | nothing | structural dependency; `Unfolds` (Phase 1) |
| `instRefs` | operands of `delay` | **`Causal`** — the positive criterion |
| `strictRefs` | operands *and* initial values of `delay`, and lambda bodies | the negative theorem `Ev.not_of_strictCyclic` |

* **Legal after delay exists**: any structural cycle every one of whose
  cycles passes through a delayed operand (`Causal`).  Self-delay, mutual
  delayed recursion, multiple delays — all run.
* **Still illegal**: any instantaneous cycle, including one that is
  *partly* delayed (`Δmixed`: removing delayed edges must leave the whole
  graph acyclic).
* **Cycles through unresolved declarations** still cannot exist
  (`DependsOn.realized`): an input has no body.
* **The gap** (recorded, not hidden): `A := λx. A x` is not causal, yet
  `declRef A` evaluates — to a closure; only *applying* it diverges
  (`lamloop_evaluates`).  `Causal` is conservative for lambda-guarded
  cycles; the negative theorem covers strict cycles only.  Likewise a cycle
  through a delay's *initial value* is rejected by `Causal` (needed at tick 0)
  but exempt from the negative theorem.

Phase 1's `Unfolds.not_of_cyclic` is untouched: unfolding still fails on
every structural cycle.  The change is in *which semantics matters*:
`Unfolds` is a correct optimization wherever it exists (`unfolds_preserves_eval`);
`Ev` is the semantics, and exists exactly on causal designs.

### 4.4 The minimal basis

One primitive.  Every candidate was reduced to it plus `Prim`:

| Candidate | Reduction | Independent state? |
|---|---|---|
| `previous x` (with init) | `delay init x` — literally | no |
| `previous x` (without init) | `delay none (some x)` — the absence is pushed to consumers as `opt` | no |
| `hold init ev` | `getD ev (delay init self)` | no (self-delayed) |
| `count ev` | `ite (isSome ev) (1 + delay 0 self) (delay 0 self)` | no |
| `since ev` | `ite (isSome ev) 0 (1 + delay 0 self)` | no |
| `once ev` | `delay false self ∨ isSome ev` | no |
| `every n` | modulo counter over `delay` | no |
| `rise b` | `b ∧ ¬ delay false b`, as an `opt bool` | no |
| `after`, `for`, `while`, `until` | comparisons over `since`/`once`/activation; not separately executed | — |

No candidate changes observable behaviour beyond what `delay` provides; none
changes causality (each adds exactly one delayed self-edge); none needs its
own storage.  **State identity is structural**: a "cell" is a `delay` node
in a declaration body; it has no identifier because nothing refers to it —
consumers refer to the *declaration*.  There is consequently no "two writers
to one cell" in this kernel; multiple writers arise only with actions
(Phase 6).

### 4.5 Signal and Event

* **`Signal τ` as a type**: not added.  Under the tick semantics it would be
  inhabited by exactly the terms of type `τ`; it distinguishes nothing and
  rejects nothing.  What a signal type *will* carry is the domain index
  `Signal[d]` of Phase 5 — information about which clock, not about being a
  stream.  [engineering preference; no result needed the constructor]
* **`Event τ` vs `opt τ`**: in one domain an input delivers one value per
  tick by construction of `Input`, so an event input *is* an `opt` stream;
  `event_encoding_equivalent` says the `opt` streams are exactly the
  multiplicity-≤1 streams.  `event_encoding_loses_multiplicity` exhibits the
  counterexample — two occurrences in one observation interval — and it is
  observable only when a source ticks faster than its observer, i.e. across
  domains, which is where the paper itself puts it (§4.8.2).  Consumption
  vs persistence (`count` vs `hold`) is a difference between declaration
  shapes, not between event and signal.  **Verdict**: `Event` is not an
  independent single-domain kernel primitive; multiplicity is a Phase-5
  synchronization-policy question.  [equivalence by proof under the stated
  observation model; the cross-domain case is explicitly not covered]

### 4.6 Initialization

`delay init e` with an explicit initial value.  Alternatives: `previous : τ
→ opt τ` is derivable and merely relocates the case analysis; declaration-
level initial state coincides with `delay` once state is per declaration;
"no initial value" is either undefined or nondeterministic at tick 0 (two toy
relations).  Initialization is *semantic*, not validation: without it there
is no unique first step to validate.

### 4.7 Determinism, and where nondeterminism will come from

`Ev.det` is unconditional.  The sources the brief listed:

| Source | Status |
|---|---|
| simultaneous events | impossible within a domain (one `opt` per tick); merging two *sources* requires a chosen policy (`getD`-style left bias is one) — Phase 5/6 |
| undefined initialization | excluded by the rule (§4.6) |
| instantaneous cycles | no value rather than several (`Ev.not_of_strictCyclic`) |
| ambiguous state updates / multiple writes | no cells to write (§4.4); Phase 6 |

### 4.8 Answers to §27

| Question | Answer |
|---|---|
| 1. Minimal stateful/reactive basis? | `delay init e` (data-typed, top level) + the tick semantics `Ev`.  Nothing else. |
| 2. Signal: type or execution-level? | Execution-level.  `Ty` unchanged. |
| 3. Event independently necessary? | No (single domain).  `opt τ` streams; multiplicity deferred to Phase 5. |
| 4. Which temporal operators are sugar? | All of `previous`, `hold`, `count`, `since`, `once`, `every`, `rise` (executed); `after`/`for`/`while`/`until` by composition. |
| 5. Legal cycles after delay? | Structural cycles whose every instantaneous path is broken by a delayed operand (`Causal`). |
| 6. What replaces blanket acyclicity? | `Causal` = rank on `InstDependsOn`; `Acyclic` is its delay-free special case; `Unfolds` keeps its Phase-1 theorems as an optimization. |
| 7. Initialization? | Explicit `init` on every `delay`; semantic, not validation. |
| 8. Deterministic? | Yes, unconditionally (`Ev.det`); total on causal well-formed designs (`reactive_total`). |
| 9. State preserves isolation/provenance? | Yes (`Ev.tag_provenance` + `constructs_granted`): state carries tags, never creates them. |
| 10. Composes with dimensions? | Yes: `delay : q d → q d → q d`; rates arise from the ordinary algebra. |
| 11. StateHandler eliminable? | For the representative behaviours tested (activation, entry, reset-on-entry local state, inactive default): yes, as declaration shapes.  See §4.11 for the caveat. |
| 12. Rejected constructs? | `Signal τ` in `Ty`; `Event τ` as a primitive; every temporal operator as a primitive; `previous` without init; delay under lambda; delay at function type. |
| 13. Did the declaration/refinement architecture change? | No.  `DeclInterface`, `DeclLeq`, `tyView` unchanged.  Temporal edits are realization edits (D-16 covers them). |

### 4.9 Critical remarks

* The basis is Lustre's `fby`/`pre` with an initial value, in a
  declaration-per-stream setting.  Nothing here is new as a *calculus*.  The
  contribution is the same shape as in Phases 2–3: the negative results
  (Signal-as-type, Event-as-primitive, operator-as-primitive all fail to
  earn a place) and the precise scoping of the earlier results.
* The totality proof required two restrictions on `delay` that the paper
  does not state (data-typed, top level).  They are consequences of the
  synchronous model, not design choices, and the second one is what makes
  "temporal state belongs to declarations, mappings are pointwise" a theorem
  rather than a slogan.
* The desugarings are *executed*, not proved equivalent to anything: there
  is no independent kernel `count` to be equivalent to.  What is established
  is that the designer-facing vocabulary is *expressible* with the intended
  traces, and that each item is a self-delayed cycle — the class Phase 1
  forbade and Phase 4 licenses.
* `unfolds_preserves_eval` is restricted to wiring designs.  For
  higher-order mappings the agreement holds up to closure equivalence and
  was not formalized.

### 4.10 The Phase-4 result (§30)

> The smallest stateful/reactive core from which BDL's designer-facing
> temporal behaviour can be derived is: the existing typed declaration
> language, one primitive `delay init e` restricted to data types at
> declaration top level, and a tick-indexed evaluation relation in which
> every declaration is a stream and unresolved declarations are inputs.
> Execution is deterministic (`Ev.det`) and total exactly on causal designs
> — those whose dependency graph is acyclic once delayed operands are
> removed (`Causal`, `reactive_total`, `Ev.not_of_strictCyclic`).  State
> preserves semantic identity and provenance (`Ev.tag_provenance`), composes
> with dimensions by the ordinary typing rule, and needs no identity of its
> own.  `Signal`, `Event`, and every temporal operator are derived.

Among tested designs; the lambda-guarded cycle gap and the cross-domain
event case are the stated boundaries.

### 4.11 What §14 did *not* establish about StateHandler

One representative behaviour was elaborated and executed.  Not covered:
nested handlers, event-latched activation with exit-wins, per-handler action
policies, and "persistent" (non-resetting) local state — the last is just
the un-gated `delay`, the first three involve actions/policies (Phase 6) or
domain structure (Phase 5).  The claim is therefore: *the tested
StateHandler behaviour is a surface shape over gated, self-delayed
declarations*; it is not "StateHandler is only sugar" in general.


## Phase 5 — Clock domains and synchronization

### 5.1 The time model, and what had to be explicit

The smallest model that distinguishes behaviour (§16): one global base tick
and a **schedule** `S : ClockId → Nat → Bool` saying at which global ticks
each domain activates.  No physical time, no timestamps, no rates in the
kernel: a period `n` is validation data that *induces* the schedule
`t % n = 0` (`Sched.periodic`).  Domain-local time is not a separate
counter; it is the sequence of a domain's activations.

What must be explicit for cross-rate behaviour to be deterministic and
unambiguous turned out to be exactly three things:

1. **nominal clock identity** on every non-agnostic declaration
   (`ClockEnv Κ : DeclId → Option ClockId`);
2. **one transport primitive** `sync src init e` with a fixed read rule —
   *the last activation of `src` strictly before now* — and an explicit
   initial value;
3. a **domain judgment** `Clocked` rejecting every other cross-domain
   reference.

Nothing else: no numeric rate, no timestamp, no scheduler order, no second
state mechanism.

### 5.2 Results (claim strength in brackets)

| Result | Lean | Strength |
|---|---|---|
| **`single_domain_embedding`**: under the always-active schedule `MEv` *is* `Ev`, in every domain — Phase 4 is the one-domain special case, not a replaced machine | `single_domain_embedding` | reduction by proof |
| **`delay_is_sync_own`**: `delay init e` in domain `c` is `sync c init e`; the domain judgment agrees | `delay_is_sync_own`, `clocked_delay_iff_sync_own` | equivalence by proof — cross-domain transport is the Phase-4 state basis with its domain made explicit; no new state mechanism |
| **`multi_domain_step_deterministic`**: no evaluation order between simultaneously active domains appears in the semantics | `MEv.det` | formally proved |
| **`cross_domain_direct_wire_rejected`** (Counterexample A's positive half): same value type does not imply connectability across domains — the temporal analogue of Phase 2's representation ≠ identity | `cross_domain_direct_wire_rejected`, `both_well_typed` (typing is blind to it) | formally proved |
| **`explicit_transport_accepted`**; a domain-agnostic pure mapping serves two domains with one declaration | `explicit_transport_accepted`, `transport_trace` | formally proved (judgment + execution) |
| **Counterexample A**: the unpolicied wire is ambiguous — latest / first / count / sum of the window `[0,1,2]` are all type-correct and all differ | `unpolicied_wire_ambiguous` | formally proved |
| **Counterexample B / `equal_rate_not_same_domain`**: a clone with the identical schedule is a different domain (wire rejected); a same-rate domain shifted in phase reads different values through `sync` | `equal_rate_not_same_domain`, `phase_matters` | formally proved |
| **`delay_is_domain_relative`**: a slow `delay` reads three global ticks back, a fast one reads one, same syntax | `delay_is_domain_relative` | formally proved by execution |
| **Counterexample E**: moving a producer to another domain, or pinning an agnostic mapping to one, invalidates unchanged clients | `clock_change_invalidates_clients`, `clock_assignment_invalidates_clients` | formally proved |
| **Counterexample F**: a transport that lets simultaneously active domains see each other's *current* values makes the scheduler order observable — two priorities, two outputs.  `MEv`'s strictly-before rule has no such parameter | `scheduling_order_observable` (toy `MEvLE`) | formally rejected by counterexample (for the same-tick-visible alternative) |
| **`transport_preserves_semantic_identity`**, **`transport_preserves_dimension`**: `Tilt@fast → Tilt@slow` and `q Length@fast → q Length@slow` typed; a crossing authorizes neither `Tilt → MotorAngle` (grant) nor `q Length → q Time` | `transport_preserves_semantic_identity_and_dimension` | formally proved |
| semantic form: with crossings present, a concept no signature announces never appears in any domain at any tick | `MEv.tag_provenance`, `sync_preserves_semantic_identity` | formally proved |
| **`transport_breaks_instantaneous_dependency`**: `instRefs (sync _ i e) = instRefs i` — a transport reads strictly earlier, so cross-domain edges are never instantaneous; causality is the *unchanged* `Causal Δ` | `Expr.instRefs`, `mfundamental` | by definition + formally proved consequence |
| **`multi_domain_total`**: causal + globally well formed + well-typed inputs ⇒ a value in every domain at every tick, hence deterministic first activation with the explicit initial values | `multi_domain_total` | formally proved (same induction as Phase 4: `prevAct_lt`) |
| **Counterexample C**: `opt` under zero-order hold loses events — two fast events vs one are indistinguishable at the slow tick, and a single event followed by a quiet fast tick is *dropped* | `opt_loses_multiplicity_under_sync` | formally rejected by counterexample (for `sync` as event transport) |
| **`buffer_from_log_and_cursor`**: the exact window of source occurrences since the destination's previous activation equals the log read at `t` minus the log length read at `t₀`: two single-instant reads, i.e. `sync` of a source-side accumulator and `delay` of a cursor | `buffer_from_log_and_cursor`, `window_example` | formally proved (on tick sets); object-language realization needs list data (pending) |
| policies as functions of the window: `latest`, `count`, `count+latest` each identify distinct windows; only the list is injective | `policies_lose_information` | formally proved |
| clocked types force clock polymorphism for pure mappings; the judgment does not | `clocked_type_forces_polymorphism` (toy) | engineering preference, with a formal witness of the cost |

### 5.3 Where clock information lives (§7, §24, §25)

| Placement | Verdict |
|---|---|
| A — in `Ty` (`Signal[c, τ]`) | rejected: every pure mapping would need clock polymorphism (`clocked_type_forces_polymorphism`), and nothing it rejects is missed by the judgment.  Not unsound; unnecessary. [engineering preference + toy] |
| B — declaration metadata + separate judgment | **this is the design**: `ClockEnv Κ` keyed by `DeclId`, `Clocked` |
| C — execution environment only | insufficient: typing would accept the direct wire and the semantics would be *ambiguous*, not merely undefined (`unpolicied_wire_ambiguous`); the check must exist somewhere static |
| D — separate domain judgment | = B; the judgment is the check, the projection is its data |

**Does `DeclInterface` change?**  The clock is *interface data* in every
formal sense that matters: clients' validity depends on it (Counterexample
E), it is frozen under refinement, changing it is an edit.  It is stored as
the projection `Κ` rather than as a fourth record field, exactly as the
concept representation is stored in `Θ` rather than in `Ty.sem`.  So the
public interface of a declaration is now
`expectedType × commitments × clock`, with the third component held in
`ClockEnv`; `DeclInterface` the record is unchanged, `tyView` is unchanged,
typing is unchanged.  Whether to fold `Κ` into the record is churn, not
semantics; recorded as D-46.

**Was a new environment projection required (§25)?**  Yes — by a formal
dependency, not symmetry: the domain judgment must resolve a reference's
domain, and nothing already in `Δ.tyView`, `Θ`, or `G` carries it.

### 5.4 Event transport (§11–§12)

`opt τ` remains the right *value* representation of "at most one occurrence
per activation" (Phase 4).  What Counterexample C shows is that `sync` — a
single-instant read — is the wrong *transport* for events, not that `opt` is
the wrong type.  The window model separates the two:

* a destination should be able to see the source's occurrences at the
  source activations *since its own previous activation* (the window);
* `buffer_from_log_and_cursor` proves the window is derivable from two
  single-instant reads — `sync` of a source-side accumulated log and `delay`
  of the log length seen at the previous destination activation;
* `policies_lose_information` shows what each policy keeps: `latest` and
  `count` and `count+latest` are lossy; the list is not.  Order within the
  window is the source's activation order and is preserved by the list.

So: **multiplicity and order are observable; buffering is required to keep
them; buffering is a structured use of the existing state basis plus list
data; a bound on the buffer is a validation obligation** (an unbounded log
is the kernel model, capacity/overflow is deployment).  `Event` as a
distinct semantic notion is still not needed; what would be needed to *write*
the buffer in the object language is `Ty.list` and a few list operators —
plain data, deferred.

### 5.5 Initialization, `delay`, and causality across domains

* Every `sync` carries an explicit `init`, used at a destination activation
  with no earlier source activation (`transport_trace` at tick 0).  First
  activation is deterministic by `MEv.det` and exists by `multi_domain_total`.
* `delay` means *previous activation of the current domain*
  (`delay_is_domain_relative`), and is literally `sync` at that domain.
* Every crossing costs at least one destination-visible step: a source
  active at the same global tick is *not* seen (strictly-before).  This is a
  choice with an observable alternative (Counterexample F); the alternative
  makes scheduler order semantic.  "Synchronous subdomains evaluated in one
  instant" are, in this model, the *same* domain.
* Causality is unchanged: `Causal Δ` on `instRefs`, where `sync`'s operand is
  not instantaneous.  No cross-domain cycle can be instantaneous.

### 5.6 Refinement vs edit vs validation (§23)

| Operation | Kind | Witness |
|---|---|---|
| unclocked (agnostic) → assigned domain | edit | `clock_assignment_invalidates_clients` |
| domain A → domain B | edit | `clock_change_invalidates_clients` |
| rate 100 Hz → 50 Hz | validation-only: changes the induced schedule, hence observed values, but no client's well-formedness | `Sched.periodic`; nothing in `Clocked` mentions rates |
| synchronization policy change (`sync` → buffer) | realization edit | D-16 |
| buffer capacity change | validation-only | §5.4 |

### 5.7 Answers to §35

| Question | Answer |
|---|---|
| 1. Explicit clock identity required? | Yes: without it the direct wire is ambiguous (A) and equal rates cannot distinguish domains (B). |
| 2. Identity distinct from rate? | Yes: `equal_rate_not_same_domain`, `phase_matters`; rates are not in the kernel. |
| 3. Where does clock information live? | `ClockEnv Κ` (per declaration, interface-level) + the judgment `Clocked`. |
| 4. Does `DeclInterface` change? | Semantically the interface gains a frozen clock component; the record is unchanged (held in `Κ`), D-46. |
| 5. Clocks in `Ty`? | No (`clocked_type_forces_polymorphism`). |
| 6. Minimal transport primitive? | `sync src init e`; `delay` is its own-domain instance. |
| 7. Derived/surface policies? | `hold`/`latest` = `sync`; `sample` = `sync` at the destination's activation; `buffer` = `sync` of a log + `delay` of a cursor (+ list data); `drop` = window head; `coalesce μ` = fold of the window.  All derived given the window. |
| 8. Is `opt τ` still sufficient for events? | As the per-activation value, yes; as the *transported* value under `sync`, no (C). |
| 9. What exactly is missing? | Multiplicity and order across a crossing — i.e. a window read, which is buffering; not a distinct Event semantics. |
| 10. Transport initialization? | Explicit `init` on every `sync`, used at the first activation. |
| 11. `delay` in multiple domains? | Previous activation of the expression's own domain (`delay_is_domain_relative`). |
| 12. Generalized causality? | The same `Causal Δ`; transports are never instantaneous. |
| 13. Deterministic? | Yes (`MEv.det`), total on causal designs (`multi_domain_total`). |
| 14. Semantic provenance preserved? | Yes (`sync_preserves_semantic_identity`). |
| 15. Dimensional correctness preserved? | Yes, by the typing rule of `sync`. |
| 16. Validation-only timing concerns? | numeric rates/periods, drift, jitter, latency, buffer capacity/overflow, value age. |
| 17. Refinement vs edit? | All clock changes are edits; rate and capacity changes are validation-only (§5.6). |

### 5.8 Critical remarks

* The strictly-before rule is Lustre/Esterel's "a signal computed this
  instant is visible next instant" applied across domains, and the paper's
  own causal-boundary convention.  What Phase 5 adds is the *reason* it is
  the right default: the alternative makes scheduler order semantic
  (Counterexample F), and the strict rule makes cross-domain causality free.
* `delay_is_sync_own` is the phase's cleanest result and also its most
  uncomfortable: it says the Phase-4 "only state primitive" was already the
  transport primitive with its domain implicit.  The honest reading is that
  the kernel has one temporal primitive — *read a domain at its previous
  activation* — and Phase 4 only saw its diagonal.
* The buffer derivation is proved on tick sets, not in the object language.
  Writing it there needs `Ty.list`; until then "buffering needs no new
  primitive" is a semantic-level reduction.

### 5.9 The Phase-5 result (§37)

> The smallest clock-domain and synchronization mechanism is: nominal
> `ClockId` on every non-agnostic declaration (interface-level, frozen), a
> schedule outside the design saying when domains activate, one transport
> primitive `sync src init e` reading the source at its last activation
> strictly before now with an explicit initial value, and a domain judgment
> rejecting every other cross-domain reference.  `delay` is `sync` at the
> own domain; the single-domain semantics embeds exactly; evaluation is
> deterministic and total on the unchanged causality condition; semantic
> identity, provenance and dimensions pass through transport untouched;
> event buffering is derivable from the same two reads plus list data, with
> capacity left to validation.

Among tested designs; the same-tick-visible alternative and clocked types
were rejected for stated, mechanized reasons; the object-language buffer is
the stated pending item.


## Phase 6 — Physical outputs and the single-driver discipline

### 6.1 The model

A declaration computes a value; it does not move hardware.  Physical effect
happens only through an explicit **drive edge** from a declaration to a
**physical sink**.  The smallest model that survived:

* `OutputId` — nominal resource identity of a sink;
* `OutputEnv Ω : OutputId → Option OutputSpec`, `OutputSpec = (accepts : Ty, clock : ClockId)`;
* `DriveEnv β : DeclId → Option OutputId` — the drive edges, a per-declaration
  projection like `Κ`, write-once;
* `DriveWF Ω Κ Δ β` — a drive edge is well formed iff the driver's type
  **equals** the sink's accepted type and the driver's clock is the sink's;
* `SingleDriver β` — at most one driver per sink;
* `CompleteOutputs β req` — every required sink is driven.

Nothing was added to `Ty`, `HasType`, `Clocked`, `MEv`, or the grant
discipline.  No effect rows, no action values, no arbitration.

### 6.2 Results (claim strength in brackets)

| Result | Lean | Strength |
|---|---|---|
| **Counterexample A / `multiple_direct_drivers_rejected`**: two drivers of one sink — globally well typed, well-clocked, causal, each edge individually well formed — fail only `SingleDriver`.  Local typing is insufficient; the invariant is global | `two_direct_drivers_locally_fine`, `multiple_direct_drivers_rejected` | formally proved |
| semantically, two drivers make the output *not a function*: `base = 10` and `corr = 40` are both physical outputs at the same tick | `two_drivers_two_outputs` | formally proved |
| **`single_driver_completed_design_deterministic`**: with one driver the physical output is a partial function of the tick | `single_driver_output_deterministic` | formally proved |
| **Counterexample B / `explicit_target_composition_accepted`**: `base + corr → final → motor` passes everything; the contributors are dependencies, not drivers | `explicit_target_composition_accepted`, `contributors_are_not_drivers` | formally proved |
| **Counterexample C**: first/last/max over the same value graph give three physical outputs — arbitration policy is design information | `hidden_arbitration_observable` | formally rejected by counterexample (for hidden policies) |
| explicit priority as an ordinary conditional in a single driver; blend and max likewise | `explicit_priority_single_driver`, `blend_and_max_are_ordinary_targets` | formally proved (typing + execution) |
| **Counterexample D / `output_identity_distinct_from_semantic_identity`**: two servos accept the same type; a type-keyed binding collides, nominal `OutputId` does not | `type_keyed_binding_collides` | formally proved |
| **Counterexample E / `output_binding_preserves_semantic_identity`, `…_dimension`**: `Tilt`, bare `q Angle`, `q Length` cannot drive the `MotorAngle` sink; only a declaration already typed `MotorAngle` (constructed under its own grant) can | `output_binding_preserves_semantic_identity_and_dimension` | formally proved |
| a sink that accepts a *representation* is legitimate and needs an explicit `rep` declaration first: semantic target vs hardware representation stays visible | `representation_sink_needs_explicit_rep` | formally proved |
| **Counterexample G / `output_binding_respects_clock_domain`**: a fast driver cannot drive a slow sink; a slow driver reading a fast value must `sync` it first; the binding never synchronizes | `output_binding_respects_clock_domain` | formally proved |
| **`first_output_binding_is_monotone`**: binding an unbound declaration to an undriven sink is a refinement (preserves `SingleDriver`) | `first_output_binding_is_monotone` | formally proved |
| a second binding to a driven sink is *invalid* | `second_binding_invalid` | formally proved |
| **Counterexample F**: retargeting a sink's accepted type, renaming the sink, or detaching the edge invalidates an unchanged design | `rebinding_invalidates_design` | formally proved |
| **`partial_design_allows_unbound_output`** / **`executable_design_requires_complete_outputs`** | as named | formally proved |
| **`effect_rows_add_no_new_rejection`**: single-driver is *exactly* disjointness of direct effect rows; propagated rows flag a valid design (a display that reads the driver) | `single_driver_iff_direct_rows_disjoint`, `propagated_effect_rows_false_positive` | equivalence by proof; false positive by counterexample |
| action values relocate the conflict into the collector, which must then be a policy (= C) | `action_values_relocate_conflict` | formally proved (toy) |
| StateHandler remainder: event-latched activation with exit-wins, state-local output choice, nested choice — all ordinary declarations with one driver | `statehandler_output_cases` | formally proved by execution on the tested cases |

### 6.3 Output identity (§5, §20)

| Candidate | Verdict |
|---|---|
| A — by type | rejected: `type_keyed_binding_collides` (two servos, one type) |
| B — `SemanticId` | rejected: one concept feeds several devices; conflates concept and hardware |
| C — `DeclId` | rejected: two declarations that both mean the steering motor become two "sinks", and Counterexample A cannot even be *stated* |
| D — nominal `OutputId` | **kept**: the only one under which both A and D are expressible |
| E — external deployment only | rejected: completeness and single-driver are design-time acceptance conditions (paper §7.6 "executable") |

What `OutputId` names: a logical actuator channel / device command endpoint
— a *resource*.  "Desired steering angle" is a value (`MotorAngle`); "the
steering motor" is a sink.  The kernel keeps them in different sorts.

### 6.4 Where the binding lives (§7, §26)

Per-declaration projection `β` + a global predicate — the same shape as
clocks (Phase 5) and representations (Phase 3).  It participates in *no*
typing rule.  It must be knowable before realization (a sink can be declared
and left undriven), and client validity does not depend on it — only
completeness does.  Single-driver joins commitment validity, causality and
clock consistency as the fourth global property beyond STLC typing.

### 6.5 Semantic target vs hardware representation (§14)

The sink's `accepts` is ordinary `Ty`.  A sink accepting `MotorAngle` takes
a declaration typed `MotorAngle` — which had to construct it under its own
grant.  A sink accepting `q Angle` (a raw servo) needs an explicit
`rep`-typed declaration in between.  A device-command concept
(`PWMCommand`) would be another `SemanticId` reached by an explicit mapping.
The kernel does not distinguish these; the deployment declares, and the
path is visible either way.

### 6.6 Refinement vs edit (§27)

| Operation | Kind | Witness |
|---|---|---|
| unbound → bound once, sink undriven | refinement | `first_output_binding_is_monotone` |
| bind to an already-driven sink | **invalid** | `second_binding_invalid` |
| output A → output B | edit (A becomes undriven; completeness may break) | `rebinding_invalidates_design` (c) |
| detach binding | edit | `rebinding_invalidates_design` (c) |
| replace driver | edit (write-once per declaration) | D-16 |
| rename `OutputId` | edit of `Ω` and `β` together; a stale edge dangles | `rebinding_invalidates_design` (b) |
| retarget a sink's accepted type | edit | `rebinding_invalidates_design` (a) |

The drive edge has the Phase-0/1 write-once shape (`DriveRefines`), with one
extra global side condition — the sink must be undriven — which is exactly
the single-driver invariant.

### 6.7 Answers to §38

| Question | Answer |
|---|---|
| 1. What is a physical output? | A nominal sink `OutputId` with an accepted `Ty` and a `ClockId` (`OutputSpec` in `Ω`). |
| 2. Independent nominal identity? | Yes (Counterexample D; `SemanticId`/`DeclId` conflate). |
| 3. How is a value bound? | A drive edge `β d = some o`, well formed iff types equal and clocks equal. |
| 4. Typing, global WF, or deployment? | Global well-formedness (`DriveWF`, `SingleDriver`); `Ω` is deployment-declared data. Not typing. |
| 5. Single-driver formally? | `∀ d₁ d₂ o, β d₁ = some o → β d₂ = some o → d₁ = d₂`. |
| 6. Partial designs with unbound outputs? | Yes (`partial_design_allows_unbound_output`). |
| 7. Executable condition? | `CompleteOutputs β req` on top of `PartialOutputWF` (plus Phases 4–5: causal, well-clocked, realized). |
| 8. Multiple direct drivers rejected? | Yes, globally; and semantically the output is not a function without it. |
| 9. Multiple contributors still possible? | Yes — as ordinary computation upstream of one edge (Counterexample B). |
| 10. Effect rows necessary? | Not in the tested formulation: direct rows duplicate `β`, propagated rows false-positive. |
| 11. Runtime arbitration necessary? | No in the tested architecture: hidden policies are observable (C) and composition is expressible explicitly. |
| 12. Priority/selection? | `ite`, `max`, blend, clamp — ordinary declarations of the target type. |
| 13. Preserves semantic identity/provenance? | Yes: the binding is a type equality; the driver's `MotorAngle` came from its own grant (E). |
| 14. Preserves dimensions? | Yes, same mechanism (E). |
| 15. Clocks and sync? | Driver clock must equal sink clock; synchronization happens explicitly upstream (G). |
| 16. Refinement vs edit? | §6.6. |
| 17. StateHandler cases eliminable? | Event-latched activation with exit-wins, state-local output choice, nested choice with output — tested and elaborated. Not tested: per-handler action *policies* (they no longer exist as a mechanism). |
| 18. Phase-7 validation? | Range/travel/torque/thermal/current limits, PWM/bus compatibility, deadlines, saturation safety, collisions. |

### 6.8 Critical remarks

* The whole phase is one global predicate over a projection.  That is the
  point: the paper's "resolve" phase, effect rows, and arbitration policies
  all dissolved once the design principle became *one final driver, all
  composition explicit*.  Nothing here is a new PL mechanism; the
  contribution is negative (C, the effect-row toys) and structural (the
  invariant is global, like the three before it).
* `SingleDriver` on `DriveEnv : DeclId → Option OutputId` is not trivially
  true — that is why `β` is keyed by declaration and not by sink.  Keying by
  sink would make uniqueness definitional and hide Counterexample A.
* The StateHandler evidence is now three tested behaviours across Phases
  4 and 6.  "StateHandler is surface syntax" remains a claim about tested
  cases; nesting with *independent* clocks and handler-scoped clocks were
  not tested.

### 6.9 The Phase-6 result (§41)

> The smallest mechanism is: a nominal sink identity with a declared
> accepted type and clock (`Ω`), a write-once drive edge per declaration
> (`β`), a well-formedness condition that is plain type and clock
> *equality*, and one global invariant — at most one driver per sink — with
> completeness added only for executable designs.  Every combination of
> behaviours is an ordinary declaration upstream of the single edge; hidden
> arbitration is observable and unnecessary; effect rows and action values
> either duplicate the edge or relocate the conflict.

Among tested designs.

## Open items carried to later phases

* Interface-level references (commitments that mention other declarations)
  — needed before a full dependency graph is meaningful.
* ~~Delay/temporal boundaries~~ — resolved in Phase 4 (`Causal`).
* Lambda-guarded instantaneous cycles: rejected conservatively by `Causal`;
  the negative theorem does not cover them.
* Higher-order `unfolds_preserves_eval` (closure equivalence).
* Reusable stateful components (function abstraction over `delay`) — Phase 8
  elaboration by instantiation.
* ~~Event multiplicity~~ — resolved in Phase 5 (window model); merging two event *sources* is ordinary computation over the two windows (Phase 6 principle), not a kernel policy.
* StateHandler with handler-scoped clocks / independently clocked nesting — untested.
* `Ty.list` and list operators, to write the buffer in the object language.
* Folding `ClockEnv` into the `DeclInterface` record (churn only).
* Whether "several candidate definitions with one active" (§3.2) is a
  surface convenience over a write-once kernel realization.
* Environment-sensitive evidence and invalidation tracking for edits.
* ~~Representation binding for concepts~~ — resolved in Phase 3 (§3.3); the
  D-25 warning was confirmed by counterexample and answered by the grant
  mechanism.
* Affine units (°C/K) and the concept display-name table — surface, not
  modelled.
* Grants are per-signature; whether a realization may *delegate* its grant
  (higher-order mappings taking a constructor as argument) is untested.
* Display-name table for concepts — surface; not modelled in core.
