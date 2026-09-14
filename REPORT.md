# REPORT — formal results so far

Project state: **Phase 1 complete** (cross-hole references and dependency).
Phases 2–13 not started.  Everything builds with `lake build`; no `sorry`;
axioms used are `propext` and `Quot.sound` (the latter only through `funext`
in `HoleEnv.update_update_same` and standard `simp` lemmas).  No
`Classical.choice` anywhere.

Layout:

| File | Contents |
|---|---|
| `BDL/Core/Base.lean` | `Ty`, `HoleId`, `Expr` (with `holeRef`), `refs`, `HoleFree` |
| `BDL/Core/Spec.lean` | `Spec`, `Refines` preorder (Phase 0) |
| `BDL/Core/Hole.lean` | `DesignHole`, `HoleEnv`, `tyView`, structural order `HoleLeq` / `EnvRefines`, `EnvRefines_update` |
| `BDL/Core/Typing.lean` | `HasType Δ Γ e τ`, decidable `infer`, weakening, **factoring lemma** `HasType.mono_env` |
| `BDL/Core/Satisfaction.lean` | env-dependent `Evidence`, `Evidence.Monotone`, `Satisfies`, `WellFormedHole`, `HoleRefines`, Theorems 1–6 (Phase 0, ported) |
| `BDL/Core/Env.lean` | `GlobalWF`, **`local_refinement_preserves_global_typing`**, **`local_refinement_preserves_global_wf`**, multi-step version |
| `BDL/Core/Dependency.lean` | `DependsOn`, `Reaches`, `Cyclic`/`Acyclic`, unfolding semantics `Unfolds`, determinism, type preservation, cycle theorems |
| `BDL/Experiments/HoleCounterexamples.lean` | Phase-0 examples; Phase-1 probes 1–6; cycle examples |

---

## Phase 0 (preserved) — a single persistent hole

Conclusions carried forward unchanged:

1. A persistent hole is a stable name + a fixed type + a monotonically
   growing obligation set + a write-once realization.  The lifecycle closure
   is exactly this preorder (`HoleRefinesStar_iff`).
2. Strengthening a realized hole must re-verify the realization
   (`HoleRefines.strengthen` carries the premise; `naive_breaks_wellformedness`).
3. Identity alone contributes nothing beyond a declaration name to the
   single-hole theorems.
4. Theorem 4 (`preserves_wellFormed`) has no independent content: its
   hypothesis is unused because the invariant was moved into the definition.
   This is reported, not hidden (`HoleRefines.wellFormed_target`).

---

## Phase 1 — cross-hole references

### 1.1 The model

* `Expr.holeRef : HoleId → Expr`.
* `HoleEnv := HoleId → Option DesignHole`; `Δ.tyView h := (Δ h).map (·.spec.expectedType)`.
* Typing rule: `Δ.tyView h = some τ ⟹ HasType Δ Γ (holeRef h) τ`.  This is the
  only rule that reads `Δ`, and it reads only `tyView`.
* `Evidence : HoleEnv → Expr → PropertyId → Prop` — evidence may consult the
  environment (needed for compositional discharge: "`A` is monotone because
  `B` is committed to be monotone").
* The **order** is separated from the **invariant**:
  * `HoleLeq h₁ h₂` (structural): same id, `Refines` on specs, realization
    write-once.  `EnvRefines Δ₁ Δ₂`: pointwise `HoleLeq`, new holes allowed.
  * `GlobalWF ev Δ`: every stored hole is under its own id and its realization
    satisfies its spec *in `Δ`*.

### 1.2 The main theorem, in two halves

**Typing half** — `local_refinement_preserves_global_typing`:

```
Δ B.id = some B  →  HoleLeq B B'  →  ∀ Γ e τ, HasType Δ Γ e τ → HasType (Δ.update B') Γ e τ
```

Hypotheses are purely structural: no evidence, no well-formedness of `B`,
`B'`, or anything else.  In fact only `B'.spec.expectedType = B.spec.expectedType`
is used.  **This theorem is a one-liner and it should be reported as such**:
it is true because typing was *defined* to factor through `tyView`
(`HasType.mono_env`).  Its content is that the "signature-first" design
decision — clients see signatures, never bodies — is *sufficient* for client
stability.  Probe 4 shows `tyView` preservation is also *necessary*.

**Commitment half** — `local_refinement_preserves_global_wf`:

```
ev.Monotone → GlobalWF ev Δ → Δ B.id = some B → HoleRefines ev Δ [] B B' → GlobalWF ev (Δ.update B')
```

and the multi-step version `local_lifecycle_preserves_global_wf`.  This one
needed a hypothesis that was **not** in the brief and was discovered by
trying to make the theorem fail: `Evidence.Monotone` — evidence must be
stable under `EnvRefines`.  Probe 6 shows the theorem is false without it.

### 1.3 The five probes ("try hard to make it fail")

`A : nat → bool`, `A := λx. f (B x)`, `B : nat → nat` unresolved.  Then:

| Probe | Operation on `B` | `A`'s typing | `A`'s commitments | Result |
|---|---|---|---|---|
| 1 | strengthen spec | preserved | preserved | theorem instance `probe1_*` |
| 2 | realize | preserved | preserved; `A` now unfolds to a hole-free program of the same type | `probe2_*` |
| 3a | re-identify **replacing** `B` | **broken** — dangling reference | — | `probe3a_breaks_typing` |
| 3b | re-identify **beside** `B` | preserved | vacuous | `A` still depends on the stale `B`; design can never become executable (`probe3b_*`) |
| 4 | change expected type (id kept) | **broken** | — | `probe4_breaks_typing`; `probe4_id_alone_insufficient` |
| 5 | drop an obligation | **preserved** | **broken** | `probe5_typing_kept`, `probe5_breaks_commitment` |
| 6 | (valid realize, but evidence non-monotone) | preserved | **broken** | `probe6_breaks`, `badEv_not_mono` |

Two of these deserve comment.

**Probe 5 is the important negative result.**  Dropping `B`'s `monotone`
obligation does not change a single type; the type checker is silent.  But
`A`'s own `monotone` commitment was discharged *through* `B`'s commitment
(`compEv`), so `A` is now ill-formed without having been edited.  Consequence
for the design: **obligations are part of the interface**.  The "signature"
that clients depend on is `expectedType × obligations`, and both must be
monotone for client stability.  The paper says properties "attach to the
name" (§3.2); this shows they are load-bearing for dependents, which is a
stronger claim than the paper makes.

**Probe 6 is the discovered invariant.**  Any discharge mechanism that
consults the *absence* of information (an unresolved hole, a missing
obligation) produces evidence that valid refinement destroys.  So the
validation layer is constrained by the kernel: every `DischargedBy` must be
positive/monotone in the environment.  This is not a decoration on the
theorem; `badEv_not_mono` derives non-monotonicity of the bad evidence from
the theorem's failure.

### 1.4 Dependency graph and cycles

* `DependsOn Δ a b` iff `a`'s realization refers to `b`.  Specs contain no
  references in this model, so there is no spec-level dependency; a cycle
  can therefore never pass through an unresolved hole (`DependsOn.realized`).
* Semantics at this phase is **unfolding** (`Unfolds Δ e e'`): inline
  realized references recursively, stop at unresolved ones.  It is
  deterministic (`Unfolds.det`), type-preserving under `GlobalWF`
  (`Unfolds.preserves_typing`, which needs closed-term weakening), and in a
  fully realized environment produces a hole-free term whose typing no longer
  depends on any environment (`Unfolds.holeFree_of_fullyRealized`,
  `HasType.holeFree_env_irrelevant`).  This is the formal content of the
  paper's "executable" acceptance level.
* **Every cycle blocks unfolding** (`Unfolds.not_of_cyclic`): a self-reference
  `S := S` and a mutual recursion `P := Q, Q := P` are both *well typed*
  (references are typed by signature) yet have no unfolding.  Conversely
  acyclic environments (rank-witnessed) unfold every term
  (`Unfolds.exists_of_acyclic`).
* There is **no harmless cycle** in this fragment: the pure language has no
  fixpoint, so a cyclic definition denotes nothing.  The distinction
  "structural cycle vs instantaneous computational cycle" cannot yet arise;
  it requires a delay operator (Phase 5/8).  Deferred, not dismissed.
* Classification: realization-acyclicity is a **kernel** well-formedness
  condition beyond typing (the semantic function is undefined otherwise),
  not a validation obligation.

### 1.5 Is persistent identity now formally non-trivial?

**No.  It is still exactly a declaration name.**  Precisely:

* Every Phase-1 theorem that mentions `id` uses it in one way only: to make
  `Δ.update B'` land on the slot `holeRef B` resolves to
  (`EnvRefines_update`).  That is what a name does in any environment-based
  semantics.
* What *is* non-trivial is not identity but the **environment order**
  `EnvRefines` and the two facts that clients depend on it only through
  (a) `tyView` for typing and (b) monotone evidence for commitments.  This is
  the standard interface/implementation separation: clients are typed
  against signatures; definitions can be supplied or refined later.  It is
  the same structure as ML signatures / Coq `Parameter` later given a
  `Definition` / Lean's metavariable context (assignment write-once, types
  fixed), and `Evidence.Monotone` is the familiar "stable under world
  extension" condition of Kripke-style models.
* Two aspects are *slightly* non-standard, and they are where the design
  content sits: (i) the signature includes a growable obligation set, and
  the growth is a first-class operation on a declared-but-undefined name;
  (ii) the kernel imposes positivity on the validation layer's evidence.
  Neither is a new PL abstraction.

So the answer to the Phase-1 question is: identity is a name; the model is
"a module of named declarations with monotone signatures and write-once
bodies"; the non-trivial invariants live in the order on environments, not
in identity.

### 1.6 Theorems that became trivial by definition (reported per §21)

* `HoleRefines.preserves_wellFormed` (Phase 0) — hypothesis unused.
* `local_refinement_preserves_global_typing` — a one-line consequence of
  making the `holeRef` rule read `tyView` only.  Its necessity direction
  (probe 4) is the non-trivial half.

### 1.7 Tension with the paper, recorded

The paper allows *detaching* a definition ("retracts an implementation while
retaining the claim that the relationship exists", §3.2).  In this model a
realization is write-once; detaching is not a `HoleLeq` step.  The formal
reason: detaching `B` does not affect typing of clients (`tyView` unchanged)
but destroys any client evidence that consulted `B`'s realization, i.e. it
is a non-monotone edit.  It can be supported as an *edit* that re-opens
validation of all transitive dependents, but not as a *refinement*.  See
`DESIGN_DECISIONS.md` D-07.

---

## Open items carried to later phases

* Spec-level references (obligations that mention other holes) — needed
  before a full dependency graph is meaningful.
* Delay/temporal boundaries — needed to revisit which cycles are harmless.
* Whether "several candidate definitions with one active" (§3.2) is a
  surface convenience over a write-once kernel realization.
