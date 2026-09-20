---
kind: report
phase: 3
area: core
date: 2026-09-15
status: current
---

# Phase 3 — representation binding and physical dimensions

## 3.1 First task: try to break Phase 2

The obvious dangerous model — global `rep_s : sem s → R` and `mk_s : R → sem s`
for every concept — was built (`Policy.free`) and attacked. It breaks
immediately:

| Attack                                                                                                    | Lean                                                             | Strength                                |
| --------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------- | --------------------------------------- |
| `λx. mkMotor (repTilt x) : Tilt → MotorAngle` in the **empty** environment — no declaration, no mapping   | `unrestricted_representation_binding_bypasses_semantic_identity` | **formally rejected by counterexample** |
| `mkMotor 0 : MotorAngle` from nothing                                                                     | `unrestricted_mk_creates_semantic_values_from_nothing`           | formal                                  |
| the crossing hides inside `brightnessCtrl : Tilt → Brightness`, whose signature says nothing about motors | `hidden_crossing_inside_unrelated_body`                          | formal                                  |
| Phase-2 provenance (`no_semantic_value_without_declaration`) becomes false                                | `modelA_breaks_phase2_provenance`                                | formal                                  |

So **yes: unrestricted `mk`/`rep` breaks semantic isolation**, and the Phase-2
nominal distinction would be ceremonial under it. Model A is rejected.

A second, less obvious hazard surfaced while setting this up: if a concept may
be _represented by_ another semantic type (`Θ tilt = some MotorAngle`), then
`rep` itself is a hidden mapping — under every policy, even observation-only
(`binding_to_semantic_type_is_hidden_mapping`). Hence `ConceptEnv.WF`:
representation types are sem-free. This is a constraint the brief did not
anticipate.

## 3.2 Models tried (representation binding)

All four are one judgment `RHasType Θ Δ P` with a _construction policy_
`P ∈ {free, none, grant G}`; the binding witness (Model D) is `Θ s = some R`,
required by both `rep` and `mk` in every model.

| Model                                   | Policy                                                                      | Verdict                                                                                                                                                                                                                 | Strength                                             |
| --------------------------------------- | --------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------- |
| A symmetric unrestricted                | `.free`                                                                     | bypass (§3.1)                                                                                                                                                                                                           | formally rejected                                    |
| B observation only                      | `.none`                                                                     | safe — `provenance` holds for every concept — but **no mapping can be realized by a formula**: in an environment with only a tilt sensor, no closed term has type `Tilt → Brightness` (`modelB_cannot_realize_mapping`) | formally proved limitation                           |
| C realization-local construction        | `.grant (Ty.grant τ)` where `τ` is the realized declaration's own signature | survives every attack; see §3.3                                                                                                                                                                                         | formally proved                                      |
| D explicit witness                      | `Θ s = some R`                                                              | is the binding _in_ every model; on its own permits nothing — operations are governed by the policy                                                                                                                     | reduction: D is a component of C, not an alternative |
| E "mappings are the only cross-id path" | —                                                                           | holds in the _occurrence_ form: `constructs_granted`                                                                                                                                                                    | formally proved                                      |

The distinction the brief asked for — _observing_ representation vs _creating_
semantic identity — is exactly the asymmetry Model B exposes: observation is
safe everywhere (`observation_is_available`, `modelB_provenance`); creation is
what must be controlled. Model C controls it by the smallest possible authority:
the signature of the declaration being realized.

## 3.3 The surviving model (promoted to core)

- `ConceptEnv Θ : SemanticId → Option Ty` — write-once representation binding
  (`ConceptRefines`; `ConceptEnv.bind`), sem-free (`ConceptEnv.WF`).
- `Expr.rep e` — typed `R` when `e : sem s` and `Θ s = some R`; available
  everywhere.
- `Expr.mk s e` — typed `sem s` when `e : R`, `Θ s = some R`, **and the grant
  permits `s`**.
- `Grant := SemanticId → Prop`; client code is typed under `Grant.none`; a
  realization under `Grant.of τ = (· ∈ τ.grant)`, the concepts in result
  position of its own signature (`Satisfies`).
- `Prim` — registered operators with dimensioned types (§3.5).

Results, all formally proved unless marked:

| Result                                                                                                                                                     | Lean                                                                   |
| ---------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------- |
| the global bypass, written with explicit `rep`/`mk`, is ill-typed in client code                                                                           | `representation_binding_does_not_enable_hidden_semantic_mapping`       |
| a declared mapping's body may observe its input and construct its output                                                                                   | `explicit_semantic_mapping_can_use_representation_formula`             |
| the hidden crossing of §3.1 is rejected under `brightnessCtrl`'s own grant; declaring `tiltToMotor` makes it legal and visible                             | `hidden_crossing_rejected_under_grant`, `declared_crossing_realizable` |
| **provenance** (per-concept denotation, `sem t ↦ ∅`, others `↦ Unit`): if `t` is not granted and no declaration has a `t`-source type, no closed term does | `provenance`, `grant_provenance`                                       |
| **occurrence invariant** (Model E): a well-typed term constructs `s` only if granted `s`; under `Grant.of τ`, only inside a realization announcing `sem s` | `HasType.constructs_granted`                                           |
| binding a representation is monotone: typing, satisfaction, global WF all survive                                                                          | `HasType.mono_concept`, `GlobalWF.of_conceptRefines`                   |
| unbound concepts still wire (signature-first at the type level); only `rep`/`mk` wait for the binding                                                      | `unbound_concept_still_wires`                                          |
| **Counterexample D**: rebinding `Tilt ↦ nat` to `Tilt ↦ bool` breaks an existing realization and is not `ConceptRefines`                                   | `representation_change_is_edit_not_refinement`                         |
| erasure soundness survives: `rep`/`mk` erase to their argument, generated code is well typed                                                               | `HasType.erase` (Phase-3 form)                                         |
| unfolding preserves typing **under the universal grant**                                                                                                   | `Unfolds.preserves_typing`                                             |

The last line deserves a remark rather than a footnote. Each inlined body was
typed under the grant of _its own_ signature, so the flattened program contains
`mk`s that were individually authorized at their declarations. The unfolded
program is the implementation, where design-time isolation has been
_discharged_, not violated: `constructs_granted` holds for every body
separately, and the flattened term is checked under `Grant.all` because the
authorization already happened. Semantic isolation is a property of the design
graph, not of the executable.

**Did `tyView` change?** No. **Did a new judgment become necessary?** Not a
separate one: typing gained two parameters — the concept environment (read only
through `Θ s = some R`) and the grant. The brief's suggested split (`HasType`
for structure, `Realizes` for bodies) is realized as one judgment family indexed
by the grant, with client code at `Grant.none` and realizations at `Grant.of`
their signature. This is reported as the major Phase-3 design result: **typing
now consults a second, concept-level projection**. The Phase-1 declaration-level
invariant (`tyView` only) is intact.

## 3.4 Answers to the provenance test (§7)

The desired stronger property — a value of `sem t` either originates from a
declaration typed as a `t`-source or is produced inside an explicit mapping
whose codomain is `sem t` — holds in two complementary forms:

- _denotational_: `provenance` / `grant_provenance` (closed terms outside a
  `t`-granted realization have no `t`-source type unless a declaration does);
- _syntactic_: `constructs_granted` (`mk t` occurs only under a `t` grant, i.e.
  inside a realization announcing `sem t`).

"A MotorAngle cannot arise from a Tilt solely through erasure and
reconstruction" is
`representation_binding_does_not_enable_hidden_semantic_mapping` together with
`shared_dimension_no_hidden_mapping` (with dimensions present).

## 3.5 Dimensions

`Ty.q d`, `d : Dim` an exponent vector over Length/Time/Angle; the algebra is in
the types of registered operators:

    add d : q d → q d → q d      mul d₁ d₂ : q d₁ → q d₂ → q (d₁+d₂)      div d₁ d₂ : … → q (d₁−d₂)

No dimension-specific typing rule exists; an application is checked by ordinary
STLC against `Prim.ty`.

| Result                                                                                                                                                                                                                                              | Lean                                                                                                                                  | Strength                                                                                                                                                                                          |
| --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Counterexample B**: erasing every dimension to `q 0` (the numeric baseline) accepts `length + time`, and can no longer tell the two sensors apart; the erasure is sound                                                                           | `counterexampleB_baseline_accepts_length_plus_time`, `HasType.eraseDim`                                                               | reduction by proof: the baseline _is_ erased dimensional typing                                                                                                                                   |
| `length + time` rejected; `length / time : q ⟨1,−1,0⟩`                                                                                                                                                                                              | `dimension_mismatch_rejected`, `velocity_typed`                                                                                       | formal                                                                                                                                                                                            |
| addition requires equal dimensions (by inversion)                                                                                                                                                                                                   | `dimensional_addition_requires_equal_dimensions`                                                                                      | formal                                                                                                                                                                                            |
| **units are surface**: a literal `n u` elaborates to `prim (lit u.dim (n·u.scale))`; typed by the unit's dimension in any environment; changing the unit changes the value, never the type; mixed-unit addition works after elaboration             | `unit_scaling_preserves_dimension`, `unit_change_is_value_not_type`                                                                   | formal                                                                                                                                                                                            |
| **Counterexample C**: Tilt and MotorAngle both bound to `q Angle` remain distinct types; the direct wire is still rejected                                                                                                                          | `same_dimension_does_not_imply_same_semantic_identity`                                                                                | formal                                                                                                                                                                                            |
| a mapping realized by a dimensioned formula `λx. mk bright (rep x · gain)` with `gain : q (0−Angle)`; a dimension error _inside_ the formula is caught by the same typing; the formula cannot manufacture a MotorAngle despite the shared dimension | `explicit_semantic_mapping_uses_dimensioned_formula`, `dimension_error_inside_mapping_rejected`, `shared_dimension_no_hidden_mapping` | formal                                                                                                                                                                                            |
| **Counterexample D**: rebinding `Tilt ↦ q Angle` to `q Length` breaks the realization; not a `ConceptRefines`                                                                                                                                       | `representation_change_is_edit_not_refinement'`                                                                                       | formal                                                                                                                                                                                            |
| dimensions as metadata / validation                                                                                                                                                                                                                 | not formalized                                                                                                                        | engineering preference: `mul`/`div` _produce_ dimensions, so any checker recomputes `Prim.ty`-driven inference; the tested alternative (erasure) cannot distinguish; broader family not ruled out |

Affine units (°C vs K) are not modelled; the elaboration here is linear scaling
only, matching the paper's own restriction.

## 3.6 Answers to §22

| Question                                                       | Answer                                                                                                                                                                                                                                                                                                                                                          |
| -------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 1. Does unrestricted `mk`/`rep` break semantic isolation?      | Yes — three formal counterexamples (§3.1).                                                                                                                                                                                                                                                                                                                      |
| 2. Surviving representation-binding model?                     | Write-once witness `Θ s = some R` (sem-free) + `rep` everywhere + `mk s` only under the realized declaration's own grant (§3.3).                                                                                                                                                                                                                                |
| 3. Can formulas implement explicit semantic mappings?          | Yes, inside the mapping's realization (`explicit_semantic_mapping_can_use_representation_formula`, dimensioned form in §3.5).                                                                                                                                                                                                                                   |
| 4. Can cross-identity changes occur without declared mappings? | Not in client code (provenance), and `mk s` occurs only inside a realization announcing `sem s` (`constructs_granted`). A declaration _of_ `sem s` (e.g. `motorTarget : MotorAngle := mk motor (rep tilt)`) is itself the declared source — the crossing is visible in its signature.                                                                           |
| 5. Do dimensions belong in the type system?                    | Among tested designs, yes: `Ty.q d` with the algebra in `Prim.ty`; the numeric baseline is its erasure.                                                                                                                                                                                                                                                         |
| 6. Units kernel or surface?                                    | Surface: elaborated to scaled dimensioned literals; never in `Ty`.                                                                                                                                                                                                                                                                                              |
| 7. Is semantic identity independent of dimension?              | Yes (Counterexample C); `Ty.sem s` is not indexed by `d`; the dimension is the concept's _representation_, stored in `Θ`.                                                                                                                                                                                                                                       |
| 8. Where is the semantic-to-representation association stored? | In `ConceptEnv Θ`, a concept-level environment separate from `DeclEnv` and from `DeclInterface`; it is typing-visible (through `Θ s = some R` only).                                                                                                                                                                                                            |
| 9. Is changing the binding a refinement or an edit?            | Binding an unbound concept is a refinement (`ConceptRefines`, monotone). Rebinding is an edit (Counterexample D, both forms).                                                                                                                                                                                                                                   |
| 10. Did `tyView` remain unchanged?                             | Yes.                                                                                                                                                                                                                                                                                                                                                            |
| 11. Did a new realization-level judgment become necessary?     | Typing gained a grant parameter; realizations and client code are the same judgment at different grants. Typing also gained the concept environment — the major design change.                                                                                                                                                                                  |
| 12. Implication for `Sem[name, dimension]`?                    | Phase 2 + 3 yield `Ty.sem s` + `Θ s = some (q d)`, not a two-index constructor. The paper's `mk_n`/`rep` are right in kind but must not be global: `mk` is licensed by the signature of the declaration being realized. The paper's "units live at the boundary, not in the kernel" is confirmed; "dimensions in the kernel" is confirmed among tested designs. |

## 3.7 Q1 and Q2 (the Phase-3 result)

**Q1.** Among the tested designs, the smallest representation-binding mechanism
that lets formulas implement semantic mappings without permitting implicit
cross-semantic reconstruction is: a write-once, sem-free binding witness
`Θ s = some R`; an unrestricted observation `rep : sem s → R`; and a
construction `mk s : R → sem s` licensed **only by the signature of the
declaration being realized** (`Grant.of`). Observation is safe (Model B);
construction is the whole hazard (Model A); the signature is the smallest
authority that makes construction visible at the design level (Model C).

**Q2.** Among the tested designs, the smallest dimensional mechanism that
rejects dimensionally invalid computation while keeping semantic identity
independent of representation is: a quantity type `q d` over an exponent-vector
`Dim`, with the algebra placed in the types of registered operators and _no_
dimension-specific typing rule; semantic concepts are bound to `q d` through
`Θ`, never indexed by `d`; units are elaborated away.

Neither answer is a proof that no other mechanism could work (§2.7 discipline):
the metadata/validation families were argued against, not excluded.

## 3.8 Critical remarks

- The grant mechanism is, once again, a known shape — it is a _capability_
  attached to a definition site, or equivalently the private constructor of an
  abstract type exported only to the module that declares it. Its contribution
  here is _where_ the capability comes from: the signature the designer already
  wrote, so no new annotation is needed.
- `Unfolds.preserves_typing` had to move to `Grant.all`. That is the honest
  price of the design: isolation is a design-graph property and does not survive
  inlining as a _type_ property. It survives as provenance (each `mk` in the
  flattened term was authorized somewhere), which is what one wants of generated
  code, but a reader expecting "the executable is semantically typed" should not
  be told that.
- Typing now reads two environments. The Phase-1 slogan "typing sees only
  `tyView`" is true of declarations and false of concepts; the accurate slogan
  is "typing sees the type view of declarations and the representation view of
  concepts, and nothing else."
