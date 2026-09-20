---
kind: report
phase: 2
area: core
date: 2026-09-15
status: current
---

# Phase 2 — where does semantic identity live?

## 2.1 The baseline failure (Counterexample A)

With concepts represented only by representation types (`Tilt ↦ nat`,
`MotorAngle ↦ nat`), the direct wire `motorTarget := declRef tiltSensor` is well
typed and the design is globally well formed
(`counterexampleA_baseline_accepts_invalid_wire`). Nothing in the model can
reject it because nothing in the model records the distinction.

## 2.2 Models tried

**Model A — nominal semantic types.** `SemanticId` (internal, distinct from
`DeclId` and from display names) and one constructor `Ty.sem : SemanticId → Ty`
with _no_ introduction or elimination forms in the pure fragment.

| Result                                                                                                                                                                              | Lean                                                                                   |
| ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------- |
| mismatch rejected statically                                                                                                                                                        | `semantic_identity_mismatch_rejected`                                                  |
| like-to-like sharing of a concept by several declarations                                                                                                                           | example after it                                                                       |
| explicit semantic mapping `tiltToMotor : Tilt → MotorAngle` (a declared design relationship, itself unresolved) makes the connection well typed; the mapping is visible in the term | `explicit_semantic_mapping_accepted`                                                   |
| identity established before realization                                                                                                                                             | example: every declaration in `ΔA_good` except the wire is unresolved                  |
| **erasure soundness**: semantic typing ⇒ representation typing                                                                                                                      | `HasType.erase`                                                                        |
| erasure is not injective, and **the baseline is erased Model A**                                                                                                                    | `erase_not_injective`, `baseline_is_erased_modelA`                                     |
| conservativity: sem-free programs get only sem-free types                                                                                                                           | `semantic_extension_preserves_structural_typing`                                       |
| refinement preservation inherited unchanged from Phase 1                                                                                                                            | `semantic_check_preserved_under_interface_refinement`                                  |
| identity change is not a refinement and breaks clients (**Counterexample B**)                                                                                                       | `semantic_identity_change_is_not_refinement`, `semantic_identity_change_breaks_client` |
| rename preserves identity; name-as-identity makes rename destructive (**Counterexample C**)                                                                                         | `semantic_rename_preserves_identity`, `rename_under_name_identity_breaks_client`       |
| semantic values originate only from declarations (denotational proof, `sem ↦ Empty`)                                                                                                | `no_semantic_value_without_declaration`                                                |

**Model B — semantic role as interface data, typing unchanged.**
`InterfaceB = expectedType × semanticRole : Option SemanticId × commitments`;
typing sees the representation type; a separate judgment checks roles.

| Result                                                                                                                                                                                                                                                                                                                                                                                                                                                | Lean                                                                                                                   |
| ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------- |
| **Counterexample D**: typing accepts the invalid wire; only the second judgment rejects it                                                                                                                                                                                                                                                                                                                                                            | `counterexampleD_typing_accepts_semantic_check_rejects`                                                                |
| the direct-wire checker is **evaded by η-expansion** `(λx. x) tilt` — same flow, no direct wire, both checkers silent                                                                                                                                                                                                                                                                                                                                 | `bweak_evaded_by_eta`                                                                                                  |
| role change keeps every type but flips the verdict on _unchanged_ clients — an edit, exactly like a type change                                                                                                                                                                                                                                                                                                                                       | `role_change_flips_unchanged_clients`                                                                                  |
| a checker that enforces identity through arbitrary term structure must reason compositionally about semantic flow (variables, lambdas, applications, references); the tested strong formulation — a role per subterm with role arrows — has the rule shapes of `HasType` over `Ty`-with-`sem` and runs alongside representation typing, which it implies (`HasType.erase`); in that formulation it duplicates nominal typing with no observed benefit | argued in §B.2, **not proved**; no definition was written because the tested formulation would coincide with `HasType` |

Conclusion for Model B, with claim strength:

- _B-weak (direct-wire metadata checker)_: **formally rejected by
  counterexample** (`bweak_evaded_by_eta`, Counterexample D).
- _B-strong (compositional role judgment)_: **tested formulation redundant with
  nominal typing; the broader family not universally ruled out.**
  Flow-sensitive, indexed/effect-like, abstract-interpretation, or relational
  semantic analyses were not formalized and no theorem here excludes them. What
  the mechanized evidence does establish is that any sound checker must be
  compositional over terms, i.e. of type-system strength, and that the one
  tested has no benefit over putting identity in the type. Its one distinctive
  feature — a "type-correct but semantically pending" state — costs the
  guarantee that structural typing implies connectability.

**Model C — concepts as _ordinary_ `DesignDecl`s, identity = `DeclId`.**

| Result                                                                                | Lean                              |
| ------------------------------------------------------------------------------------- | --------------------------------- |
| category error 1: the concept is usable as a _value_ (`declRef Tilt : nat`)           | `conceptC_usable_as_value`        |
| category error 2: the concept can be realized by a number, as a legal refinement step | `conceptC_realizable_by_a_number` |

Conclusion for Model C, with claim strength:

- _Concept = ordinary `DesignDecl` in the value sort_: **formally rejected by
  the two category-error counterexamples.**
- _Stratified concept-declaration family_
  (`ConceptDecl = id × displayName × Option representation` in a distinct sort):
  **not rejected.** But once concepts inhabit a distinct category with
  independent identity, the Phase-2 kernel requirement is again an independent
  `SemanticId` — Model A's core — and the remaining fields are representation
  metadata, deferred to Phase 3. So this family does not offer a _smaller_
  Phase-2 kernel; it offers a home for Phase-3 data.

## 2.3 The surviving model and the answer to §18

> **Among the tested designs, the smallest mechanism that enforces semantic
> non-interchangeability compositionally, without a second semantic analysis, is
> one nominal type constructor `Ty.sem : SemanticId → Ty`, over an internal
> identity distinct from declaration identity and from display names, with no
> introduction or elimination forms.**

This is a claim about the tested designs, not a proof that nominal typing is the
only possible mechanism in principle (see §2.7). Why it is minimal among them
and sufficient:

- _Non-interchangeable by default:_ `sem s₁ = sem s₂ ↔ s₁ = s₂`
  (`sem_injective`), so two concepts with the same representation are distinct
  types, and the ordinary STLC rules reject the wire.
- _Explicit semantic mappings still allowed:_ a mapping is an ordinary
  declaration of arrow type `sem a → sem b` — a design relationship between
  concepts, not a coercion, cast, or representation conversion. No such
  mechanism exists in the kernel; the mapping is visible in the term and is
  itself a signature-first declaration that may remain unresolved.
- _Nothing else changed:_ `DeclInterface` unchanged, `tyView` unchanged, all
  Phase 0/1 theorems unchanged. The only proof that had to change was
  `InterfaceRefines_iff_semantic`, which used a canonical closed inhabitant of
  every type; opaque semantic types have none, and the replacement — inhabit any
  type by an _unresolved declaration_ (`DeclEnv.single_hasType`) — is itself a
  signature-first observation.
- _Erasure:_ `HasType.erase` shows Model A is conservative over the
  representation language (generated code is well typed after erasing concepts),
  and `baseline_is_erased_modelA` shows the baseline is exactly what erasure
  leaves behind.

What was deliberately _not_ added: representation binding (`mk`/`rep`).
`no_semantic_value_without_declaration` proves that without it a semantic value
can only come from a declaration of semantic type. That is the correct Phase-2
state: it separates _distinctness_ (needs only the nominal constructor) from
_realizing a mapping by a formula_ (needs a representation binding, which is
Phase-3 material where the representation is `Q[d]`).

## 2.4 Answers to §15

| Question                                         | Answer                                                                                                                                                                                                                                                                                                                                                                                            |
| ------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Did `Ty` change?                                 | Yes: one constructor `sem SemanticId`. This was the only acceptable kernel change; §2.2 shows both alternatives fail or reduce to it.                                                                                                                                                                                                                                                             |
| Did `DeclInterface` change?                      | No.                                                                                                                                                                                                                                                                                                                                                                                               |
| Did `tyView` change?                             | No. Semantic identity rides inside `expectedType`; typing still consults `tyView` only.                                                                                                                                                                                                                                                                                                           |
| Is semantic identity change refinement or edit?  | **Edit**, in every model. In A it is a type change (`InterfaceRefines` fails, clients break); in B a role change flips verdicts on unchanged clients while keeping every type. So a semantic role field would have to be frozen exactly like the type — which is the argument for putting it _in_ the type.                                                                                       |
| How are explicit semantic mappings represented?  | As ordinary declarations of type `sem a → sem b`. No kernel relation, coercion, or cast.                                                                                                                                                                                                                                                                                                          |
| What does this mean for the paper's `Sem[n, d]`? | The nominal half is right and is the whole of the Phase-2 result, with one correction: `n` must be an internal identity, not the display name (Counterexample C). The `d` component is Phase 3. `mk_n`/`rep` are representation binding: needed to attach formulas, not for distinctness. The paper's "no global `Real → Brightness` coercion" is exactly `erase_not_injective` + nominal typing. |

## 2.5 Classification (§13)

| Candidate construct                       | Verdict                                                                                    | Reason                                                                                                         |
| ----------------------------------------- | ------------------------------------------------------------------------------------------ | -------------------------------------------------------------------------------------------------------------- |
| `SemanticId`                              | KEEP_IN_KERNEL                                                                             | the identity `Ty.sem` refers to; distinct from `DeclId` (Model C) and from names (Counterexample C)            |
| nominal `Ty.sem` constructor              | KEEP_IN_KERNEL                                                                             | the whole mechanism                                                                                            |
| interface semantic field (`semanticRole`) | REMOVE (for the tested design)                                                             | Model B: would have to be frozen like the type; the tested design is dominated by putting identity in the type |
| separate semantic-compatibility judgment  | tested weak form: REMOVE; general compositional-analysis family: NOT universally ruled out | weak: η-evaded (formal); strong: tested formulation redundant (argued)                                         |
| explicit semantic mapping                 | KEEP_IN_SURFACE; represented as an ordinary declared arrow `sem a → sem b`                 | a design relationship, not a conversion; representation-level `mk`/`rep` pending Phase 3                       |
| concept as ordinary `DesignDecl`          | REMOVE                                                                                     | two category errors (formal)                                                                                   |
| stratified `ConceptDecl`                  | NOT REQUIRED IN PHASE 2; may reappear as surface/representation metadata in Phase 3        | not rejected; reduces the Phase-2 identity requirement to an independent `SemanticId`                          |

## 2.6 Critical remarks

- Model A is, once again, a standard construction: `Ty.sem` is a nominal
  abstract type (a `newtype` with no unwrapping in the pure fragment). The
  Phase-2 contribution is the _negative_ result — that the two tested ways to
  keep semantic identity out of the type system (a metadata field with a
  direct-wire checker; concept as ordinary value declaration) each fail for a
  concrete, mechanized reason — not the positive one.
- `no_semantic_value_without_declaration` is the sharpest statement of what the
  pure kernel now is: a language in which semantic quantities are _opaque_ and
  flow only through declared relationships. That matches the paper's intent, but
  it also means Phase 3 cannot avoid a representation binding if formulas are to
  realize mappings — and that binding will be the first place where the kernel's
  "typing sees only `tyView`" invariant is tested by something other than a
  rename.

## 2.7 Claim strength (methodological note)

Formal counterexamples reject the _specific tested design_, not every
conceivable design in the same informal family. This project distinguishes four
strengths of conclusion and labels each rejected model with one:

| Strength                           | Meaning                                                     |
| ---------------------------------- | ----------------------------------------------------------- |
| **proven impossibility**           | a theorem excludes the whole family                         |
| **tested design failure**          | a mechanized counterexample breaks the specific formulation |
| **reduction/equivalence by proof** | a theorem shows one design is a special case of another     |
| **engineering preference**         | argued, not proved                                          |

Phase-2 labels:

| Rejected design                              | Strength                                                                                                                                        |
| -------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------- |
| Model B weak (direct-wire metadata checker)  | tested design failure (`bweak_evaded_by_eta`, `counterexampleD_*`)                                                                              |
| Model B strong (compositional role judgment) | engineering preference: tested formulation redundant with nominal typing; broader class of compositional analyses **not** universally ruled out |
| Model C as ordinary `DesignDecl`             | tested design failure (`conceptC_usable_as_value`, `conceptC_realizable_by_a_number`)                                                           |
| Model C stratified declaration family        | **not rejected**; reduces the Phase-2 identity requirement to an independent `SemanticId`                                                       |
| baseline = erased Model A                    | reduction by proof (`HasType.erase`, `baseline_is_erased_modelA`)                                                                               |

Nothing in Phase 2 is a proven impossibility. The same discipline applies to
later phases.

## 2.8 Phase 2 claim audit

1. **Which claims were too strong?** (a) That a compositional Model-B checker
   "is `HasType` verbatim", hence that Model B "collapses exactly" to Model A.
   (b) That Model C — "semantic concepts as declarations" — is rejected as a
   family. (c) The word "conversion" for `Tilt → MotorAngle`, which suggested a
   coercion the kernel does not have. (d) The §18 answer as originally phrased
   read as "the smallest mechanism" simpliciter.
2. **What was formally established instead?** (a) The weak checker is unsound
   (η-evasion); semantic-role changes invalidate unchanged clients; any sound
   checker must be compositional over terms; the one strong formulation tested
   duplicates nominal typing. (b) Concepts cannot be ordinary `DesignDecl`s in
   the value sort (two category errors). (c) The only cross-concept path in the
   kernel is a declared arrow; there is no conversion mechanism at all. (d)
   `Ty.sem` is the smallest mechanism _among the tested designs_.
3. **Which model families remain logically possible?** Compositional semantic
   analyses other than the role-per-subterm formulation (flow-sensitive,
   indexed/effect-like, abstract-interpretation, relational); stratified
   concept-declaration sorts with independent identity. Neither has a mechanized
   argument for or against it here.
4. **Why does `Ty.sem` still survive as the minimal tested solution?** It is one
   constructor, changes neither `DeclInterface` nor `tyView`, leaves every Phase
   0/1 theorem untouched, rejects the invalid wire by ordinary STLC rules,
   admits explicit mappings as ordinary declarations, and is conservative over
   the baseline by `HasType.erase`. Every tested alternative either fails
   formally or contains an independent `SemanticId` anyway.
5. **What new obligation does Phase 2 impose on Phase 3?** Representation
   binding must not destroy the nominal distinction. See "Open items" below and
   FVD-0025.
6. **How could representation binding accidentally defeat semantic identity?**
   With unrestricted `rep : sem s → R` and `mk : R → sem s` available to every
   term, `mkMotor (repTilt x)` is a well-typed `Tilt → MotorAngle` path with no
   declared semantic mapping. `no_semantic_value_without_declaration` would
   become false and the nominal distinction ceremonial: the type checker would
   enforce only that the two words `mk`/`rep` appear, not that a design
   relationship was declared.
