# REPORT — formal results so far

Project state: **Phase 3 complete** (representation binding and physical
dimensions).  Phases 4–13 not started.  Everything builds
with `lake build`; no `sorry`; axioms used are `propext` and `Quot.sound`
(the latter only through `funext` in `DeclEnv.update_update_same` and
standard `simp` lemmas).  No `Classical.choice` anywhere.

## The kernel in one paragraph

```
DeclEnv         maps DeclId ↦ DesignDecl
DesignDecl      = id : DeclId  ×  interface : DeclInterface  ×  realization : Option Expr
DeclInterface   = expectedType : Ty  ×  commitments : List PropertyId      (monotone, public)
Ty              = bool | nat | arr Ty Ty | sem SemanticId | q Dim           (Phase 2: nominal concepts; Phase 3: quantities)
ConceptEnv Θ    maps SemanticId ↦ Option Ty                                 (Phase 3: representation binding, write-once)
Prim            registered operators; dimension algebra lives in Prim.ty     (Phase 3)
declRef d       refers to a declaration by stable identity
rep e / mk s e  observe / construct a semantic value                        (Phase 3; mk only under a grant)
typing          HasType Θ Δ G Γ e τ: sees Δ.tyView, the binding Θ s = some R, and the grant G — nothing else
realizations    are typed under Grant.of their own signature: a value of sem s is built only inside a
                declaration that announces sem s
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
| `BDL/Core/Dependency.lean` | `DependsOn`, `Reaches`, `Cyclic`/`Acyclic`, unfolding semantics `Unfolds`, determinism, type preservation, cycle theorems |
| `BDL/Experiments/DeclCounterexamples.lean` | Phase-0 examples; Phase-1 probes 1–6; cycle examples |
| `BDL/Experiments/SemanticTypeAlternatives.lean` | Phase 2: baseline, Models A/B/C, erasure, denotation, counterexamples A–D |
| `BDL/Experiments/RepresentationBindingAlternatives.lean` | Phase 3.1: policies free/none/grant over a local `RExpr`; bypass counterexample; provenance theorem; the surviving grant model |
| `BDL/Experiments/DimensionAlternatives.lean` | Phase 3.2: dimension mismatch, erasure baseline, units as elaboration, semantic ⟂ dimension, rebinding is an edit |

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

## Open items carried to later phases

* Interface-level references (commitments that mention other declarations)
  — needed before a full dependency graph is meaningful.
* Delay/temporal boundaries — needed to revisit which cycles are harmless.
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
