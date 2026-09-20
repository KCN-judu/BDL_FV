---
kind: report
phase: 1
area: core
date: 2026-09-14
status: current
---

# Phase 1 — cross-declaration references

## 1.1 The model

- `Expr.declRef : DeclId → Expr`.
- `DeclEnv := DeclId → Option DesignDecl`;
  `Δ.tyView d := (Δ d).map (·.interface.expectedType)`.
- Typing rule: `Δ.tyView d = some τ ⟹ HasType Δ Γ (declRef d) τ`. This is the
  only rule that reads `Δ`, and it reads only `tyView`. **Typing depends on the
  type view of the interface; validation depends on commitments and evidence.**
  This separation is a deliberate invariant.
- `Evidence : DeclEnv → Expr → PropertyId → Prop` — evidence may consult the
  environment (needed for compositional discharge: "`A` is monotone because `B`
  is committed to be monotone").
- The **order** is separated from the **invariant**:
  - `DeclLeq h₁ h₂` (structural): same id, `InterfaceRefines` on interfaces,
    realization write-once. `EnvRefines Δ₁ Δ₂`: pointwise `DeclLeq`, new
    declarations allowed.
  - `GlobalWF ev Δ`: every stored declaration is under its own id and its
    realization satisfies its interface _in `Δ`_.

## 1.2 The main theorem, in two halves

**Typing half** — `local_refinement_preserves_global_typing`:

```text
Δ B.id = some B  →  DeclLeq B B'  →  ∀ Γ e τ, HasType Δ Γ e τ → HasType (Δ.update B') Γ e τ
```

Hypotheses are purely structural: no evidence, no well-formedness of `B`, `B'`,
or anything else. In fact only
`B'.interface.expectedType = B.interface.expectedType` is used. **This theorem
is a one-liner and it should be reported as such**: it is true because typing
was _defined_ to factor through `tyView` (`HasType.mono_env`). Its content is
that the "signature-first" design decision — clients see interfaces, never
bodies — is _sufficient_ for client stability. Probe 4 shows `tyView`
preservation is also _necessary_.

**Commitment half** — `local_refinement_preserves_global_wf`:

```text
ev.Monotone → GlobalWF ev Δ → Δ B.id = some B → DeclRefines ev Δ [] B B' → GlobalWF ev (Δ.update B')
```

and the multi-step version `local_lifecycle_preserves_global_wf`. This one
needed a hypothesis that was **not** in the brief and was discovered by trying
to make the theorem fail: `Evidence.Monotone` — the stability condition for
evidence that is meant to survive monotone environment refinement. Probe 6 shows
the theorem is false without it.

## 1.3 The five probes ("try hard to make it fail")

`A : nat → bool`, `A := λx. f (B x)`, `B : nat → nat` unresolved. Then:

| Probe | Operation on `B`                           | Kind       | `A`'s typing                    | `A`'s commitments                                                       | Result                                                                               |
| ----- | ------------------------------------------ | ---------- | ------------------------------- | ----------------------------------------------------------------------- | ------------------------------------------------------------------------------------ |
| 1     | strengthen interface                       | refinement | preserved                       | preserved                                                               | theorem instance `probe1_*`                                                          |
| 2     | realize                                    | refinement | preserved                       | preserved; `A` now unfolds to a reference-free program of the same type | `probe2_*`                                                                           |
| 3a    | re-identify **replacing** `B`              | edit       | **broken** — dangling reference | —                                                                       | `probe3a_breaks_typing`                                                              |
| 3b    | re-identify **beside** `B`                 | edit       | preserved                       | vacuous                                                                 | `A` still depends on the stale `B`; design can never become executable (`probe3b_*`) |
| 4     | change expected type (id kept)             | edit       | **broken**                      | —                                                                       | `probe4_breaks_typing`; `probe4_id_alone_insufficient`                               |
| 5     | drop a commitment                          | edit       | **preserved**                   | **broken**                                                              | `probe5_typing_kept`, `probe5_breaks_commitment`                                     |
| 6     | (valid realize, but evidence non-monotone) | refinement | preserved                       | **broken**                                                              | `probe6_breaks`, `badEv_not_mono`                                                    |

The "Kind" column is the refinement-vs-edit distinction made explicit by the
migration: probes 3–5 are not refinements and are not covered by any
preservation theorem; they are edits that require rechecking dependents.

Two of these deserve comment.

**Probe 5 is the important negative result.** Dropping `B`'s `monotone`
commitment does not change a single type; the type checker is silent. But `A`'s
own `monotone` commitment was discharged _through_ `B`'s commitment (`compEv`),
so `A` is now ill-formed without having been edited. Consequence for the design:
**commitments are part of the interface**. The interface that clients depend on
is `expectedType × commitments`, and both must be monotone for client stability.
The paper says properties "attach to the name" (§3.2); this shows they are
load-bearing for dependents, which is a stronger claim than the paper makes.

**Probe 6 is the discovered invariant.** Any discharge mechanism that consults
the _absence_ of information (an unresolved declaration, a missing commitment)
produces evidence that valid refinement destroys. So evidence that is intended
to survive refinement must be positive/monotone in the environment. This is not
a decoration on the theorem; `badEv_not_mono` derives non-monotonicity of the
bad evidence from the theorem's failure. (Evidence that is _not_ meant to
survive refinement — environment-sensitive evidence that is rechecked on every
change — is a legitimate future category; it is documented, not implemented.)

## 1.4 Dependency graph and cycles

- `DependsOn Δ a b` iff `a`'s realization refers to `b`. Interfaces contain no
  references in this model, so there is no interface-level dependency; a cycle
  can therefore never pass through an unresolved declaration
  (`DependsOn.realized`).
- Semantics at this phase is **unfolding** (`Unfolds Δ e e'`): inline realized
  references recursively, stop at unresolved ones. It is deterministic
  (`Unfolds.det`), type-preserving under `GlobalWF` (`Unfolds.preserves_typing`,
  which needs closed-term weakening), and in a fully realized environment
  produces a reference-free term whose typing no longer depends on any
  environment (`Unfolds.refFree_of_fullyRealized`,
  `HasType.refFree_env_irrelevant`). This is the formal content of the paper's
  "executable" acceptance level.
- **Every cycle blocks unfolding** (`Unfolds.not_of_cyclic`): a self-reference
  `S := S` and a mutual recursion `P := Q, Q := P` are both _well typed_
  (references are typed by interface) yet have no unfolding. Conversely acyclic
  environments (rank-witnessed) unfold every term (`Unfolds.exists_of_acyclic`).
- There is **no harmless cycle** in this fragment: the pure language has no
  fixpoint, so a cyclic definition denotes nothing. The distinction "structural
  cycle vs instantaneous computational cycle" cannot yet arise; it requires a
  delay operator (Phase 5/8). Deferred, not dismissed.
- Classification: realization-acyclicity is a **kernel** well-formedness
  condition beyond typing (the semantic function is undefined otherwise), not a
  validation concern.

## 1.5 Is persistent identity formally non-trivial?

**No. It is exactly a declaration name — and Phase 1 falsified the idea that
persistent identity is itself a new abstraction.** Precisely:

- Every Phase-1 theorem that mentions `id` uses it in one way only: to make
  `Δ.update B'` land on the slot `declRef B` resolves to (`EnvRefines_update`).
  That is what a name does in any environment-based semantics.
- What _is_ non-trivial is not identity but the **environment order**
  `EnvRefines` and the two facts that clients depend on it only through (a)
  `tyView` for typing and (b) monotone evidence for commitments. This is the
  standard interface/implementation separation: clients are typed against
  interfaces; bodies can be supplied or refined later. It is the same structure
  as ML signatures / Coq `Parameter` later given a `Definition` / Lean's
  metavariable context (assignment write-once, types fixed), and
  `Evidence.Monotone` is the familiar "stable under world extension" condition
  of Kripke-style models.
- Two aspects are _slightly_ non-standard, and they are where the design content
  sits: (i) the interface includes a growable commitment set, and the growth is
  a first-class operation on a declared-but-undefined name; (ii) the kernel
  imposes a stability condition on the validation layer's refinement-surviving
  evidence. Neither is a new PL abstraction.

This is why the kernel is now declaration-centric (§M): the model is "an
environment of named declarations with monotone interfaces and write-once
bodies"; the non-trivial invariants live in the order on environments, not in
identity.

## 1.6 Theorems that became trivial by definition (reported per §21)

- `DeclRefines.preserves_wellFormed` (Phase 0) — hypothesis unused.
- `local_refinement_preserves_global_typing` — a one-line consequence of making
  the `declRef` rule read `tyView` only. Its necessity direction (probe 4) is
  the non-trivial half.

## 1.7 Tension with the paper, recorded

The paper allows _detaching_ a definition ("retracts an implementation while
retaining the claim that the relationship exists", §3.2). In this model a
realization is write-once; detaching is not a `DeclLeq` step. The formal reason:
detaching `B` does not affect typing of clients (`tyView` unchanged) but
destroys any client evidence that consulted `B`'s realization, i.e. it is a
non-monotone edit. It can be supported as an _edit_ that re-opens validation of
all transitive dependents, but not as a _refinement_. See `docs/decisions/`
FVD-0007 and FVD-0016.
