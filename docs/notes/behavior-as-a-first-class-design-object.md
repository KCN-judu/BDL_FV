---
kind: note
phase: 8a
area: behavior
date: 2026-09-15
status: current
---

# Behavior as a First-Class Design Object

_A formal note on Phase 8a of the BDL development (`BDL/Behavior/`)._

## 1. The claim

The BDL paper argues that product behaviour should be a design material:
something a designer names, shapes, and combines, rather than a program that is
written. Phases 0–7 made that precise for one product: a design is an
environment of named declarations with frozen types, public commitments and
write-once realizations; semantic identity is nominal; time is a delay/transport
primitive over nominal clock domains; physical effect is a single explicit drive
edge per sink. This note extends the claim from one product to _behaviour
itself_:

> **Behaviour is first-class.** A behaviour can be named and referred to,
> abstracted behind an interface, instantiated with fresh identity, reused in
> several instances, connected to other behaviours through explicit bindings,
> nested hierarchically, and flattened into the same small verified kernel
> without change of meaning.

"First-class" is not read as "appears in the syntax". Each word in the sentence
is a definition or a theorem, listed in §3. The result that matters most is
negative in shape: **nothing was added to the kernel.** Every construct of the
behaviour layer is a surface object or elaboration machinery, and every theorem
is about the existing kernel judgments — `HasType`, `Satisfies`/`GlobalWF`,
`Clocked`, `Causal`, `DriveWF`, `SingleDriver`, `Ev` — applied to the flattened
design.

## 2. The objects

A **port** is a declaration of a template, by identity, with the public part of
its interface (expected type, commitments) and its clock parameter. A
**behaviour interface** lists required ports, provided ports, elaboration-time
parameters, and clock parameters. Nothing else of the template is visible.
Physical sinks are deliberately _not_ ports: a port connects a behaviour to
another behaviour; a sink connects a behaviour to the world, and a system
decides which sinks are private to an instance and which are shared.

A **behaviour component** is an interface together with an ordinary BDL design
over _local_ identities below a width, plus the partition of the concepts and
sinks it mentions into _internal_ (owned by the behaviour) and _global_ (shared
with the system). It **realizes** its interface when the design is structurally
well formed (the Phase 1–6 conditions), every identity it owns is bounded, and
every port is a declaration with exactly the advertised interface and clock,
unresolved if required.

An **instance** is a component with a clock-parameter assignment. In a system of
width `W`, instance `k` renames every identity it owns to `W·(k+1)+n`; global
concepts and external sinks stay as they are; clock parameters are substituted.
Two instances of one template share nothing they own and share everything global
— including, when the designer says so, nothing at all.

A **binding** takes a required port of one instance from a provided port of
another (or of itself), directly, through `sync` with an explicit initial value,
or from a closed constant. It is well formed when the two port _interfaces_
agree: equal type after renaming, the destination's commitments among the
source's, and a compatible clock — equal, agnostic, or bridged by the transport.

A **system** is a list of instances, a list of bindings, and the shared concept
and sink environments. **Flattening** is the disjoint union of the renamed
instances followed by one Phase-1 realization step per binding: the destination
port, an unresolved declaration, is realized with `declRef source` (or
`sync c init (declRef source)`, or the constant). Binding is refinement, not a
new mechanism.

Hierarchy is packaging: a flattened system is a design over identities below a
bound, hence again a template.

## 3. Each word, formally

| Word                              | Definition / theorem                                                                                                                                        |
| --------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------- |
| _namable, referenceable_          | `Port` carries a `DeclId`; `Binding` refers to `(instance, port)`; display names never enter (FVD-0065)                                                     |
| _abstractable_                    | `BehaviorInterface`; `BehaviorComponent.Realizes` hides every internal declaration                                                                          |
| _instantiable_                    | `Ren.inst`, `fresh`, `decode`; **Theorem A** `inst_decl_disjoint`, `inst_concept_disjoint`, `inst_out_disjoint`, `inst_clock_disjoint`, `inst_*_not_global` |
| _reusable_                        | `union_globalWF`: every instance of a valid template is well formed in the system, for every index, given `Evidence.Equivariant`                            |
| _composable_                      | `BehaviorSystem`, `ComposeWF`; **Theorem C** `binding_satisfies`; **Theorem D** `flatten_WF`                                                                |
| _interface-bound_                 | `BindingWF` is stated on the two interfaces; **Theorem E** `flatten_globalWF` uses the existing typing judgment only                                        |
| _hierarchically nestable_         | `toComponent`, `flatWidth`                                                                                                                                  |
| _flattenable, meaning-preserving_ | **Theorem J** (restricted) `modular_iff_flat`: an instance evaluated alone under a consistent input agrees with the flattened design                        |
| _temporally sound_                | **Theorem F** `flatten_causal` under `InstAcyclic`; **Theorem G** `flatten_wellClocked`, `Clocked.rename` for any clock assignment                          |
| _open_                            | **Theorem H** `open_port_stays_open`: an unbound required port is an ordinary unresolved declaration                                                        |
| _physically disciplined_          | **Theorem I** `flatten_singleDriver`, `flatten_driveWF`                                                                                                     |
| _substitutable_                   | `substitute_composeWF`: an interface-refining component may replace an instance                                                                             |

## 4. What the theorems needed

Three conditions on the validation layer's evidence emerged, in the manner of
Phase 1's `Evidence.Monotone`:

- **Equivariance** — a discharged commitment survives renaming. This is the
  exact content of "a template's validity does not depend on which instance it
  is". A validation procedure that inspected identities would fail it, and a
  component checked once could not be trusted twice.
- **Port-soundness** — a reference to a declaration, or a transport of it,
  inherits the declaration's public commitments. This is what makes a binding a
  refinement rather than an edit that must be re-verified.
- **Monotonicity** — from Phase 1; bindings are realization steps.

One condition on the composition emerged that is not in any single component:
the inter-instance graph of _direct_ bindings must be acyclic. Two components
that are each causal — `out := in` — compose in feedback into an instantaneous
cycle (`feedback_composition_not_causal`). The repair is the Phase-5 primitive:
one of the two bindings through `sync`.

One condition on physical outputs emerged that is not in any single component
either: at most one instance may drive an external sink
(`ExternalSingleDriver`). Two instances of a single-driver template each driving
the shared `light` violate `SingleDriver` after composition; the repair is the
Phase-6 principle — one final target — or private sinks.

## 5. What was not needed

- No kernel term for components, instances, or bindings.
- No second typing judgment for components: `HasType.rename` shows that typing
  is preserved by renaming under agreement of the environments on the image,
  without injectivity; composition typing is the ordinary judgment on the
  flattened design.
- No clock-indexed component types: clock parameters are nominal variables
  substituted at instantiation, and `Clocked` is preserved for _any_
  substitution, including one that merges two parameters into one system domain.
  Frequency never appears.
- No inductive system tree: hierarchy is packaging.
- No runtime parameter machinery: a parameter is a required data-typed port
  bound to a closed constant; typed substitution preserves typing by
  `HasType.refFree_env_irrelevant`.

## 6. What is not proved

- Theorem J is proved for the single-domain semantics `Ev` on wiring designs
  with direct and constant bindings. The multi-domain semantics with `sync`
  bindings is not covered: the modular input would have to be domain-indexed for
  transported ports, which `Input : DeclId → Nat → Value` cannot express.
  Higher-order designs are not covered. The _existence_ of a consistent modular
  input follows from totality by choice and is not proved constructively.
- That a packaged system `Realizes` an interface chosen for it is a decidable
  side condition not discharged here.
- `InstAcyclic` is coarse: it rejects an instance's provided port feeding its
  own required port even through a delayed internal path.

## 7. The position

The stronger research claim the paper makes is not that BDL supports components.
It is that _behaviour forms a compositional design material_: what a designer
packages behind an interface, instantiates twice, wires to something else, and
nests inside a larger behaviour is, after elaboration, the same environment of
declarations with the same five judgments that Phases 0–7 established for a
single product. The behaviour layer adds identity discipline, interface
discipline, and two global conditions; it adds no semantics. That is the sense
in which behaviour is first-class in BDL, and it is the sense the Lean
development makes precise.
