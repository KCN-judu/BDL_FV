---
kind: note
phase: 19
area: experiments
date: 2026-09-21
status: current
---

# Concepts and their producers

For production's authoring surface (the Concept/Output projection frozen pending
this audit) and for the two papers. It settles what a concept _is_ in the formal
kernel when several declarations produce values of it, and what a surface may
and may not say about "the producer" of a concept. Report:
[Phase 19](../reports/phase-19-may-several-declarations-produce-one-concept.md);
Lean: `BDL/Experiments/ProducerAlternatives.lean`.

## Amendment (2026-09-21, Phase 20)

§ 1, § 4 and § 5 below record Phase 19's result under FVD-0159/FVD-0160, which
FVD-0161 supersedes: a concept has **one** producer, as a global invariant, and
a formula may read a concept by name. The theorems of § 2 stand; the guidance is
replaced by [one-producer-per-concept.md](one-producer-per-concept.md) § 5.

## 1. The question and the answer

May several distinct declarations produce values of the same nominal concept in
one design? **Yes, and the kernel keeps it so** (FVD-0159). A concept is a
nominal type; a declaration is a value of it; "the value of `C`" has no
denotation, "the value of `d`" has. The two candidate uniqueness invariants were
defined and tested: signature-uniqueness is refuted by ordinary constructions (a
bound component, a named transport), and origin-uniqueness is not a kernel
invariant — it fails ordinary reuse and Phase 6's composition, and nothing in
the kernel would consume it (FVD-0160). Where a design has several candidates
for one concept, the resolution is an ordinary declaration over their
references; with intermediate concepts it is origin-unique, and on the executed
designs the two forms have the same downstream trace.

## 2. What is proved

Every theorem on `propext`/`Quot.sound`.

- `witness_two_values`, `witness_two_arrows`: two `C` values / two arrows into
  `C` are `GlobalWF` and `Causal`. `phase6_not_sigUnique`,
  `phase6_not_mkUnique`: Phase 6's correct design has several producers.
- `second_producer_invisible`: adding an unreferenced second producer changes no
  evaluation (`update_transparent`).
- `binding_makes_second_signature`, `transport_second_signature`:
  signature-uniqueness fails on Phase 8a's `lamp` and on a named transport.
- `SigUnique.toMkUnique`, `mkUnique_refine`: signature-uniqueness implies
  origin-uniqueness under `GlobalWF`; origin-uniqueness is preserved by
  refinement that adds no declaration.
- `lamp_two_origins`, `private_lamp_two_concepts`, `source_and_formula`,
  `rewrap_counts_as_origin`: where origin-uniqueness fails and why the count is
  syntactic.
- `sensorsC_mkUnique`, `driver_not_origin`: the intermediate-concept design and
  the one-origin-two-outputs design are origin-unique.
- `one_origin_two_outputs`: `DriveWF`, `SingleDriver`, origin-unique, and no
  driver is an origin — β is not derivable from producers.

Executed (finite ticks, concrete inputs): `two_C_values_coexist`,
`sensors_rewriting_same_trace`, `override_rewriting_same_trace`.

## 3. What is not established

A general trace-preservation theorem for the intermediate-concept rewriting; a
design-meaning notion of origin; a design that needs two origins of one concept
— FVI-0030. None of these bears on the kernel: no kernel judgment consumes a
producer count.

## 4. Verdicts

Nominal `Ty.sem`, many producers — keep in kernel. Producer uniqueness — not a
kernel invariant; `MkUnique` an optional authoring lint at most, with the
boundary rule (a shared concept provided by at most one instance, or
instance-private). Resolver primitive, lookup by concept — never added.
Intermediate concepts for alternatives that are different quantities — surface
guidance.

## 5. Production guidance

Every line is a _design recommendation_ unless marked; the theorems are about
the model, never about production code.

- **Semantics: change nothing.** The kernel, `bdl-core`'s notion of concept and
  ADR-0034's definition of _produces_ (the signature) are consistent with
  FVD-0159 (_informed by FV_: `second_producer_invisible`,
  `binding_makes_second_signature`).
- **The Concept/Output projection may resume** on ADR-0034 §4 as written: a
  concept node lists _every_ relationship whose output is the concept
  (`SigProduces`), and _Carried by_ lists the values and Sources. It must not
  present one of them as _the_ producer, and must not resolve a value by concept
  anywhere (a probe, a simulation column, a drive-edge suggestion): a drive edge
  names a declaration, and one origin may feed two outputs through two wires
  (`one_origin_two_outputs`).
- **Two notions, two words, if the surface wants the second.** _Produces_ (the
  signature) is many-to-one and includes a bound port and a transport;
  _originates_ (a `mk C` or a Source) is the stricter count. If a canvas shows
  the second it should call it something else and say that a re-wrap counts.
- **A lint, optional, never a diagnostic of the compiler**: "concept `C` has
  more than one origin: `d₁`, `d₂`" with the rewriting of §19.6 as its
  suggestion, under the component boundary rule. It is silent on Phase 6's
  base/correction pattern only if the designer accepts it; the kernel does not
  care.
- **Naming guidance in the library and the creation sheet**: alternatives that
  are different quantities get their own concepts (`SensorATemperature`,
  `SensorBTemperature`, resolved into `Temperature`); this is Phase 18's
  guidance, and it is now stated as the form that makes the design
  origin-unique, not as a requirement.
