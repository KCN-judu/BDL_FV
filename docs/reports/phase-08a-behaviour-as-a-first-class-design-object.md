---
kind: report
phase: 8a
area: behavior
date: 2026-09-15
status: current
---

# Phase 8a — Behaviour as a first-class design object

## 8.1 The research claim, made formal

"Behaviour is a first-class design object" is read operationally: a behaviour
can be **named and referenced**, **abstracted** behind an interface,
**instantiated** with fresh identity, **reused** in several instances, **bound**
to other behaviours through explicit port bindings, **nested** hierarchically,
and **flattened** into the same small kernel without change of meaning. Each
word is a definition or a theorem below. The kernel (`BDL/Core`) was **not
modified**: every construct of the behaviour layer (`BDL/Behavior`) is a surface
object plus elaboration machinery, and every theorem is about the _existing_
kernel judgments applied to the flattened design.

| Word                    | Formal object / result                                                                                                                                                                       |
| ----------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| namable, referenceable  | a port is a `DeclId` of the template with a public `DeclInterface` and clock (`Port`); a binding refers to `(instance, port)`, never to a display name                                       |
| abstractable            | `BehaviorInterface` (required/provided/parameter ports, clock parameters) and `BehaviorComponent.Realizes` — the template design realizes its interface; internal declarations are invisible |
| instantiable            | `Ren.inst`, `fresh`/`decode`: every internal identity (declarations, private concepts, private sinks, internal clocks) is freshened per instance; **Theorem A** `inst_decl_disjoint` etc.    |
| composable              | `BehaviorSystem` (instances + bindings), `ComposeWF`                                                                                                                                         |
| reusable                | one template, many instances; `union_globalWF` shows every instance is well formed for every index, given `Evidence.Equivariant`                                                             |
| interface-bound         | `BindingWF`: type, commitment, clock compatibility stated on the two interfaces; binding elaborates to a Phase-1 `realize` step (`binding_satisfies`)                                        |
| hierarchically nestable | `toComponent`: a flattened system is again a template over identities `< flatWidth`; nesting is packaging, not a new construct                                                               |
| flattenable             | `flatten : BehaviorSystem → Design`; **Theorem D** `flatten_WF`; **Theorem J** (restricted) `modular_iff_flat`                                                                               |

## 8.2 The model

- `Design` — the five kernel environments bundled; `Design.WF` = the Phase 1–6
  acceptance conditions; `Design.Executable` adds completeness and closedness.
- `Port`, `BehaviorInterface` — the public boundary. Physical sinks are **not**
  ports (§8 of the brief): sinks are per-instance resources (private, freshened)
  or external (shared, subject to `ExternalSingleDriver`).
- `BehaviorComponent` — interface + `Design` over local identities `< width`
  - the partition of concepts and sinks into internal/global. `Realizes ev C` :
    the design is `WF`, bounded, and every port is a declaration with exactly
    the advertised interface and clock; required ports and parameters are
    unresolved.
- `Ren` and `Expr.rename`/`Ty.rename`/`Prim.rename`/`DesignDecl.rename` —
  identity renaming (meta-level).
- `Inst = (component, κ)`; `fresh W k n = W·(k+1)+n`; `decode`.
- `BehaviorSystem` — width `W`, instance list, bindings (`.port` or `.const`
  source, destination `(inst, port)`, optional `sync` transport with initial
  value), global `Θg`/`Ωg`.
- `unionΔ/Θ/Κ/Ω/β` — the disjoint union, defined by decoding identities;
  `applyBinding` realizes a destination port; `flatten`.
- `ComposeWF` — instances valid and fitting the width, shared-concept and
  external-sink agreement, every binding `BindingWF`, destinations bound at most
  once, `ExternalSingleDriver`.
- `InstDep`/`InstAcyclic` — the inter-instance instantaneous graph (direct port
  bindings; self-edges count).
- `OpenPorts`, `Design.Open` — openness.
- Semantics: `instΔ` (an instance alone, every port an input), `Consistent` (a
  modular input), Theorem J.
- `replace`, `IfaceRefines`, `Substitutable`, `substitute_composeWF`.

## 8.3 Theorem inventory

| #      | Statement                                                                                                                                                                                                          | Lean                                                                                                                                                                        | Status                                                                                                                                                  |
| ------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------- |
| A      | fresh-instance disjointness: declarations / private concepts / private sinks / internal clocks of distinct instances never coincide; fresh ids never coincide with globals                                         | `inst_decl_disjoint`, `inst_concept_disjoint`, `inst_out_disjoint`, `inst_clock_disjoint`, `inst_concept_not_global`, `inst_out_not_global`; concretely `lamp_ids_disjoint` | **proved**                                                                                                                                              |
| B      | freshening preserves typing (no injectivity needed; agreement of the three environments on the image suffices); satisfaction and well-formedness likewise, given `Evidence.Equivariant`                            | `HasType.rename`, `Satisfies.rename`, `WellFormedDecl.rename`                                                                                                               | **proved**                                                                                                                                              |
| C      | a compatible binding is a satisfying realization of the destination port in any environment refining the union (given `Evidence.PortSound`)                                                                        | `binding_satisfies`; the fold step `fold_step` is `local_refinement_preserves_global_wf`                                                                                    | **proved**                                                                                                                                              |
| D      | `ComposeWF S` ∧ `InstAcyclic S` ⇒ `(flatten S).WF` (typing + commitments, concept env, clocks, causality, drives, single-driver)                                                                                   | `flatten_WF`                                                                                                                                                                | **proved** (evidence: Monotone, Equivariant, PortSound)                                                                                                 |
| E      | composition typing preservation: every instance and every binding type-checks in the flattened environment with the _existing_ judgment                                                                            | `union_globalWF`, `flatten_globalWF`                                                                                                                                        | **proved**                                                                                                                                              |
| F      | each instance internally causal ∧ inter-instance direct-binding graph acyclic ⇒ flattened design causal; necessity by counterexample                                                                               | `flatten_causal`; `feedback_composition_not_causal`, `feedback_not_instAcyclic`; repair `feedbackSync_instAcyclic`                                                          | **proved**; conservative (self-edges rejected)                                                                                                          |
| G      | clock-parameter instantiation (any κ, including merging parameters) preserves `Clocked`; flattened design well clocked; clock mismatch rejected                                                                    | `Clock.Clocked.rename`, `flatten_wellClocked`; `clockMismatch_binding_rejected`, `clockMismatch_not_wellClocked`                                                            | **proved**                                                                                                                                              |
| H      | an unbound required port is an ordinary open declaration of the flattened design, not an error                                                                                                                     | `open_port_stays_open`; `lamp_source_open`                                                                                                                                  | **proved**                                                                                                                                              |
| I      | `DriveWF`, `SingleDriver`, `PartialOutputWF` hold of the flattened design; two instances driving one external sink are rejected                                                                                    | `flatten_driveWF`, `flatten_singleDriver`; `twoDrivers_not_singleDriver`, `twoDrivers_not_externalSingleDriver`, repair `twoLights_distinct_sinks`                          | **proved**                                                                                                                                              |
| J      | modular semantics (each instance alone under a consistent input) ⟺ flattened semantics, for `Ev` (single domain), wiring designs, direct/constant bindings; totality of the flattened design from `reactive_total` | `eval_flat_to_inst`, `eval_inst_to_flat`, `modular_iff_flat`, `flatten_total`; concretely `lamp_flat_trace` = `lamp_modular_trace`                                          | **proved for the fragment**; multi-domain `MEv` with `sync` bindings, higher-order terms, and constructive existence of a consistent input are **open** |
| §19    | parameters: a closed, delay-free constant typed at the port's type is a satisfying realization                                                                                                                     | `binding_satisfies` (`.const` case) via `HasType.refFree_env_irrelevant`                                                                                                    | **proved**                                                                                                                                              |
| §20    | reuse: template validity does not depend on instance identity                                                                                                                                                      | `union_globalWF` for every `k`; the condition it needs — `Evidence.Equivariant` — is the finding                                                                            | **proved**                                                                                                                                              |
| §21–22 | substitutability: replacing an instance by an interface-refining component preserves `ComposeWF`                                                                                                                   | `substitute_composeWF`, `IfaceRefines`, `Substitutable`                                                                                                                     | **proved** (structural; no behavioural equivalence claimed)                                                                                             |
| §11    | hierarchy: a flattened system packaged as a component                                                                                                                                                              | `toComponent`, `flatWidth`                                                                                                                                                  | **defined**; `Realizes` of the package for a chosen port selection **not proved**                                                                       |
| §17    | flattening does not touch `delay`/`sync` semantics: bodies are renamed only, `Expr.rename` maps `delay` to `delay` and `sync c` to `sync (r.c c)`; bindings add `declRef` or `sync` bodies                         | by definition of `Expr.rename`, `bindingBody`                                                                                                                               | by construction; agreement of `MEv` across flattening not proved (see J)                                                                                |

Three evidence conditions carry the theorems, all imposed on the validation
layer in the manner of Phase 1's `Evidence.Monotone`:

- `Evidence.Equivariant` — a discharged commitment survives renaming. Without it
  a component's validity could depend on the particular identities of one
  instance, which is exactly what "reusable" must exclude.
- `Evidence.PortSound` — a reference to a declaration (or a `sync` of it)
  inherits the declaration's public commitments. This is what makes
  binding-by-reference a refinement rather than an unverifiable edit.
- `Evidence.Monotone` (Phase 1) — bindings are realization steps.

## 8.4 Counterexamples (all in `Experiments/BehaviorAlternatives.lean`)

| #   | Statement                                                                                                                                                            | Lean                                                                                                                    | Strength                                                                       |
| --- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------ |
| 1   | two individually causal pass-through components in feedback: flattened design has a strict instantaneous cycle; inter-instance graph cyclic                          | `pass_causal`, `feedback_edges`, `feedback_composition_not_causal`, `feedback_not_instAcyclic`                          | formally rejected by counterexample (for "causal components compose causally") |
| 2   | direct binding across `fastClk`/`slowClk` without `sync`: `BindingWF` fails; flattened design not `WellClocked`                                                      | `clockMismatch_binding_rejected`, `clockMismatch_not_wellClocked`                                                       | formal                                                                         |
| 3   | identity renaming aliases every instance onto the first; a _private_ concept is freshened per instance, a _shared_ one is not                                        | `identity_renaming_aliases`, `internal_concept_not_shared`                                                              | formal                                                                         |
| 4   | `Tilt` port bound to a `MotorAngle` port: `BindingWF` fails; the forced body is ill-typed at the destination's interface                                             | `tiltToMotor_binding_rejected`, `tiltToMotor_forced_ill_typed`                                                          | formal                                                                         |
| 5   | two instances driving one external light: union violates `SingleDriver` though each template satisfies it; `ExternalSingleDriver` necessary; private sinks repair it | `driver_singleDriver`, `twoDrivers_not_singleDriver`, `twoDrivers_not_externalSingleDriver`, `twoLights_distinct_sinks` | formal                                                                         |

The positive example (`lamp`: one open source, two dimmer instances from one
template, two bindings) is checked by `decide`: disjoint identities, binding
bodies, open source port, shared concept preserved, clocks substituted, the
flattened declaration list globally well formed, well clocked and causal, and
the flattened and modular traces agree.

## 8.5 Minimality audit

| Construct                                    | Verdict                                                      | Reason                                                                                                       |
| -------------------------------------------- | ------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------ |
| `BehaviorInterface`, `Port`                  | SURFACE-DESUGAR (composition-time metadata)                  | ports are template `DeclId`s with their `DeclInterface`/clock; no kernel object                              |
| `BehaviorComponent`, `Realizes`              | SURFACE-DESUGAR                                              | a design over local ids + a predicate over existing judgments                                                |
| `Inst`, `Ren`, `fresh`/`decode`, `*.rename`  | elaboration / meta-level                                     | never appears in a kernel judgment                                                                           |
| `Binding`, `bindingBody`, `applyBinding`     | SURFACE-DESUGAR → Phase-1 `realize`                          | `binding_satisfies` + `local_refinement_preserves_global_wf`                                                 |
| `BehaviorSystem`, `flatten`                  | SURFACE-DESUGAR / elaboration                                | output is an ordinary `Design`                                                                               |
| `ComposeWF`                                  | validation rule (structural)                                 | conjunction of existing judgments on interfaces + two global conditions (`dstNodup`, `ExternalSingleDriver`) |
| `InstDep` / `InstAcyclic`                    | validation rule (sufficient condition for existing `Causal`) | Counterexample 1; conservative                                                                               |
| `Evidence.Equivariant`, `Evidence.PortSound` | constraints imposed by the composition layer on validation   | like `Evidence.Monotone`                                                                                     |
| `toComponent`                                | SURFACE-DESUGAR (hierarchy by packaging)                     | no inductive system tree needed                                                                              |
| clock parameters                             | elaboration (substitution by κ)                              | `Clocked.rename`; nominal identity untouched, no frequency                                                   |
| parameters (`.const` bindings)               | elaboration-time typed substitution                          | `HasType.refFree_env_irrelevant`                                                                             |
| **kernel changes**                           | **none**                                                     | `BDL/Core` untouched; `git diff` on core is empty                                                            |

## 8.6 Critical remarks

- The identity encoding (`W·(k+1)+n`) is a device; what the theorems use is
  injectivity, decodability, and disjointness from globals below `W`. A
  production implementation may use any generative identity supply with those
  three properties.
- `InstAcyclic` is coarse: it forbids an instance's provided port feeding its
  own required port even when the internal path is delayed. A port-level graph
  would be finer; not needed for the tested cases.
- Binding by reference inherits commitments only under `PortSound`; a validation
  layer in which "monotone" is a property of a _function_ would need `PortSound`
  restricted to the commitments that transfer through reference. The abstract
  labels of `PropertyId` do not distinguish.
- Theorem J is proved for the fragment where the paper's precedent
  (`unfolds_preserves_eval`) already lives. Extending to `MEv` needs the
  domain-indexed input for transported ports, which the current
  `Input : DeclId → Nat → Value` cannot express; that is the concrete obstacle,
  recorded rather than hidden.
- Hierarchy by packaging (`toComponent`) is minimal but the theorem that a
  package `Realizes` the interface chosen for it is not proved; it would require
  the chosen ports to be flattened declarations with the stated interfaces,
  which is a decidable side condition.

## 8.7 The Phase-8a result

> Behaviour is a compositional design material in BDL: a behaviour is a template
> design behind an interface of required and provided semantic ports and clock
> parameters; instantiation freshens every identity the template owns
> (declarations, private concepts, private sinks, internal clocks) and
> substitutes clock parameters; binding is a Phase-1 realization step whose side
> conditions are stated on the two interfaces; a system flattens to an ordinary
> design that is globally well formed, well clocked, causal under an acyclic
> inter-instance graph, and single-driver — with no change to the kernel — and,
> in the single-domain wiring fragment, evaluating the instances modularly under
> a consistent input agrees with evaluating the flattened design.
