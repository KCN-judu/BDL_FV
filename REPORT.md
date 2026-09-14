# REPORT — formal results so far

Project state: **Phase 2 complete** (semantic identity).  Phases 3–13 not
started.  Everything builds
with `lake build`; no `sorry`; axioms used are `propext` and `Quot.sound`
(the latter only through `funext` in `DeclEnv.update_update_same` and
standard `simp` lemmas).  No `Classical.choice` anywhere.

## The kernel in one paragraph

```
DeclEnv         maps DeclId ↦ DesignDecl
DesignDecl      = id : DeclId  ×  interface : DeclInterface  ×  realization : Option Expr
DeclInterface   = expectedType : Ty  ×  commitments : List PropertyId      (monotone, public)
Ty              = bool | nat | arr Ty Ty | sem SemanticId                   (Phase 2: nominal concepts)
declRef d       refers to a declaration by stable identity
typing          sees only  Δ.tyView d = (Δ d).map (·.interface.expectedType)
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
| `BDL/Core/Base.lean` | `Ty` (with `sem`), `SemanticId`, `DeclId`, `Expr` (with `declRef`), `refs`, `RefFree` |
| `BDL/Core/Interface.lean` | `DeclInterface` (expected type + commitments), `InterfaceRefines` preorder |
| `BDL/Core/Decl.lean` | `DesignDecl`, `DeclEnv`, `tyView`, structural order `DeclLeq` / `EnvRefines`, `EnvRefines_update` |
| `BDL/Core/Typing.lean` | `HasType Δ Γ e τ`, decidable `infer`, weakening, **factoring lemma** `HasType.mono_env` |
| `BDL/Core/Satisfaction.lean` | env-dependent `Evidence`, `Evidence.Monotone`, `Satisfies`, `WellFormedDecl`, `DeclRefines`, Theorems 1–6 |
| `BDL/Core/Env.lean` | `GlobalWF`, **`local_refinement_preserves_global_typing`**, **`local_refinement_preserves_global_wf`**, multi-step version |
| `BDL/Core/Dependency.lean` | `DependsOn`, `Reaches`, `Cyclic`/`Acyclic`, unfolding semantics `Unfolds`, determinism, type preservation, cycle theorems |
| `BDL/Experiments/DeclCounterexamples.lean` | Phase-0 examples; Phase-1 probes 1–6; cycle examples |
| `BDL/Experiments/SemanticTypeAlternatives.lean` | Phase 2: baseline, Models A/B/C, erasure, denotation, counterexamples A–D |

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
| explicit mapping `tiltToMotor : Tilt → MotorAngle` (itself unresolved) makes the connection well typed; the conversion is visible in the term | `explicit_mapping_allows_cross_semantic_conversion` |
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
| a compositional checker must assign roles to every subterm, so needs role arrows, so *is* `HasType` over `Ty`-with-`sem`; B-strong = A + a redundant erased pass (`HasType.erase`) | argued in §B.2; no new definition needed because it would be `HasType` verbatim |

Model B is rejected: the weak form is unsound, the strong form is Model A
plus duplication, and its one distinctive feature — a "type-correct but
semantically pending" state — is bought by making structural typing no
longer a guarantee of connectability.

**Model C — concepts as `DesignDecl`s, identity = `DeclId`.**

| Result | Lean |
|---|---|
| category error 1: the concept is usable as a *value* (`declRef Tilt : nat`) | `conceptC_usable_as_value` |
| category error 2: the concept can be realized by a number, as a legal refinement step | `conceptC_realizable_by_a_number` |

Model C is rejected as stated.  Its repair — a *separate sort* of
declaration `ConceptDecl = id × name × Option representation` — is Model A's
`SemanticId` plus a deferred representation binding, i.e. the Phase-1
declaration pattern lifted to types.  The representation binding is not
needed for distinctness (§2.3) and is deferred to Phase 3.

### 2.3 The surviving model and the answer to §18

> **The smallest mechanism is one nominal type constructor,
> `Ty.sem : SemanticId → Ty`, over an internal identity distinct from
> declaration identity and from display names, with no introduction or
> elimination forms.**

Why this is minimal and sufficient:

* *Non-interchangeable by default:* `sem s₁ = sem s₂ ↔ s₁ = s₂`
  (`sem_injective`), so two concepts with the same representation are
  distinct types, and the ordinary STLC rules reject the wire.
* *Explicit mappings still allowed:* a mapping is an ordinary declaration of
  arrow type `sem a → sem b`.  No conversion relation, coercion, or
  subtyping is needed in the kernel; the mapping is visible in the term and
  is itself a signature-first declaration that may remain unresolved.
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
| How are explicit mappings represented? | As declarations of type `sem a → sem b`.  No kernel relation. |
| What does this mean for the paper's `Sem[n, d]`? | The nominal half is right and is the whole of the Phase-2 result, with one correction: `n` must be an internal identity, not the display name (Counterexample C).  The `d` component is Phase 3.  `mk_n`/`rep` are representation binding: needed to attach formulas, not for distinctness.  The paper's "no global `Real → Brightness` coercion" is exactly `erase_not_injective` + nominal typing. |

### 2.5 Classification (§13)

| Candidate construct | Verdict | Reason |
|---|---|---|
| `SemanticId` | KEEP_IN_KERNEL | the identity `Ty.sem` refers to; distinct from `DeclId` (Model C) and from names (Counterexample C) |
| nominal `Ty.sem` constructor | KEEP_IN_KERNEL | the whole mechanism |
| interface semantic field (`semanticRole`) | REMOVE | Model B: would have to be frozen like the type; strictly dominated by putting it in the type |
| separate semantic-compatibility judgment | REMOVE | weak: η-evaded; strong: `HasType` verbatim |
| explicit conversion relation | KEEP_IN_SURFACE_AND_DESUGAR | desugars to a declared arrow `sem a → sem b`; `mk`/`rep` at the representation level pending Phase 3 |
| semantic concept declaration (`decl Tilt`) | KEEP_IN_SURFACE_AND_DESUGAR | allocates a `SemanticId`; the name table is surface; the representation binding is pending Phase 3 and may enter the kernel then |

### 2.6 Critical remarks

* Model A is, once again, a standard construction: `Ty.sem` is a nominal
  abstract type (a `newtype` with no unwrapping in the pure fragment).  The
  Phase-2 contribution is the *negative* result — that the two plausible
  ways to keep semantic identity out of the type system (interface metadata,
  concept-as-declaration) each fail for a concrete, mechanized reason — not
  the positive one.
* `no_semantic_value_without_declaration` is the sharpest statement of what
  the pure kernel now is: a language in which semantic quantities are
  *opaque* and flow only through declared relationships.  That matches the
  paper's intent, but it also means Phase 3 cannot avoid a representation
  binding if formulas are to realize mappings — and that binding will be the
  first place where the kernel's "typing sees only `tyView`" invariant is
  tested by something other than a rename.

---

## Open items carried to later phases

* Interface-level references (commitments that mention other declarations)
  — needed before a full dependency graph is meaningful.
* Delay/temporal boundaries — needed to revisit which cycles are harmless.
* Whether "several candidate definitions with one active" (§3.2) is a
  surface convenience over a write-once kernel realization.
* Environment-sensitive evidence and invalidation tracking for edits.
* Representation binding for concepts (`ConceptDecl.representation`,
  `mk`/`rep`) — Phase 3, together with dimensions.
* Display-name table for concepts — surface; not modelled in core.
