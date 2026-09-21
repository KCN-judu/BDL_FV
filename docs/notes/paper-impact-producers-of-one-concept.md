---
kind: note
phase: 19
area: paper
date: 2026-09-21
status: current
---

# Paper impact — several producers of one concept

For whoever next revises `paper/core_calculus/paper.md` and
`paper/monograph/paper.md`. Phase 19 revised neither: the brief asked for the
formal result first and an impact note instead of edits. The result is
FVD-0159/FVD-0160 (Model A kept; explicit resolution as discipline; uniqueness
not a kernel invariant). Each entry names the sentence, what it says today, and
what it would need under each model — so that the revision, when made, is a
matter of prose and not of re-deciding.

## Amendment (2026-09-21, Phase 20)

FVD-0161 chose Model B at the design level: one producer per concept as a global
invariant (`ProducerUnique`), with explicit resolution through intermediate
concepts and a concept reference that elaborates to the producer (FVD-0162). The
operative column below is therefore **Under B**, read with Phase 20's definition
of a producer (a construction outside initial-value positions, or a Source;
relays excluded). Two entries change under that reading: §8.2's `base`, `corr`,
`final` are rewritten with `BaseAngle` and `Correction` (`composition_unique`),
and the statement "the desired steering angle is a value" is now literally true
of the concept. The papers are still not revised in this phase.

## Amendment (2026-09-21, Phase 21)

FVD-0163 supersedes FVD-0161/0162: the operative column is again **Under A** — a
concept is a nominal type, several declarations (Sem blocks) of it are ordinary
— with the projection corrected: the papers' "a declaration is a value; a
concept is its type" is exactly the Sem-block model, and the core-calculus
paper's §8.2 (`base`, `corr`, `final` sharing a concept) stands as written. The
only revision the papers need is vocabulary, when they are next revised: _Sem
block_ / _mapping block_ for the canvas objects (monograph Parts III and VI),
the concept as a template (III.1), and no concept node.

## 1. The core-calculus paper (`paper/core_calculus/paper.md`)

No theorem statement in the paper becomes false under the result; the changes
are in framing. Line numbers are those of HEAD `5f71710`.

| Where                                                                                                                                                                  | Today                                                              | Under A (the result)                                                                                                                                                                                                  | Under B                                                                                                                         | Under C-primitive                                                |
| ---------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------- |
| Abstract, l. 3: "the designer often knows _that_ one product quantity determines another"                                                                              | a concept read as a quantity                                       | keep; optionally "one product concept" — the sentence is about a relationship, not about how many declarations carry the concept                                                                                      | would need "the" quantity to be a declaration, not a concept                                                                    | unchanged                                                        |
| §2.1, l. 54–56: "a relationship with no inputs, `light : Brightness`, is a value the design computes … `tilt : Tilt` is an input"                                      | correct: a declaration is a value; a concept is its type           | keep; one sentence could add that several declarations may carry one concept and that a term names a declaration, never a concept (`second_producer_invisible`)                                                       | would need "the value of `Brightness`" to be well defined — it is not (`two_C_values_coexist`)                                  | unchanged                                                        |
| §5 opening, l. 303: "a **concept** is what the designer means, its **representation** is the data it is carried by"                                                    | the nominal-type reading                                           | keep verbatim; this is FVD-0159                                                                                                                                                                                       | would add "and one declaration produces it"                                                                                     | unchanged                                                        |
| §5.1, l. 309: "a value of `sem s` can originate only in a declaration of semantic type (`no_semantic_value_without_declaration`)"                                      | provenance: _where_ a `C` may come from                            | keep; if a reviewer reads it as uniqueness, add "in any declaration of that type — there may be several" — the paper never says "the declaration"                                                                     | would strengthen to "in the declaration"                                                                                        | unchanged                                                        |
| §5.1, l. 319: "semantic isolation … survives inlining as provenance (Theorem 12)"                                                                                      | provenance                                                         | keep; Phase 19 §19.1 makes explicit that Theorem 12 bounds sources, not their number — a footnote at most                                                                                                             | unchanged                                                                                                                       | unchanged                                                        |
| §6.4, l. 451–453 (Theorem 12): "a concept appears in a value only if some signature announces it or some input carries it"                                             | "some", correctly existential                                      | keep                                                                                                                                                                                                                  | unchanged                                                                                                                       | unchanged                                                        |
| §8 opening, l. 579: "'the desired steering angle' is a value, 'the steering motor' is a resource"                                                                      | reads as if the concept _is_ one value                             | rephrase to "the declaration `target : SteeringAngle` is a value" or "a desired steering angle is a value" — the sentence contrasts value against resource, and is true of the driver declaration, not of the concept | keep as is (it is the Model B reading)                                                                                          | unchanged                                                        |
| §8, l. 587: "A driver of a concept-accepting output is necessarily a value, not a function (`driver_is_unit_domain`)"                                                  | about the driver declaration                                       | keep; add, if the section is touched, that the driver is _a_ declaration of the accepted type, not derivable from "the producer" (`one_origin_two_outputs`, `driver_not_origin`)                                      | would invite "the producer of `C` drives the output", which is false even under B (`one_origin_two_outputs`)                    | unchanged                                                        |
| §8.2, l. 593: "many contributors, one explicit final driver … `base + corr -> final -> motor` … blend, maximum and clamp are ordinary declarations of the target type" | Model A with explicit resolution, contributors sharing the concept | keep; this paragraph _is_ the explicit-resolution discipline (FVD-0159); a clause could note the intermediate-concept form for contributors that are different quantities                                             | would forbid `base`, `corr`, `final` all of type `MotorAngle` — the paragraph would be rewritten with `BaseAngle`, `Correction` | a resolver construct would replace the conditional in the driver |
| Contributions, l. 41 and §5 l. 28: "the construction grant … is the authority a realization has to produce a concept"                                                  | authority per declaration                                          | keep; "authority" is per declaration and says nothing about how many hold it — no change                                                                                                                              | would add a uniqueness clause to the grant                                                                                      | unchanged                                                        |
| Related work, l. 639–645 (modules, nominal/abstract types)                                                                                                             | nominal identity ≈ abstract types                                  | optionally one sentence: an abstract type with a private constructor may be constructed at several sites that hold the constructor; the grant is per definition site, so the analogy already carries multiplicity     | would need the "one constructor site" variant                                                                                   | unchanged                                                        |

Under the result, the only sentence whose _reading_ should change is §8's "the
desired steering angle is a value" (a declaration is a value; a concept is a
type), and it changes by a few words. No figure, rule or theorem changes.
Optional additions: one sentence in §2.1 or §5 that a term names a declaration
and never a concept, and a clause in §8.2 about the intermediate-concept form.

## 2. The monograph (`paper/monograph/paper.md`)

| Where                                                                                                                                       | Today                                                 | Under A (the result)                                                                                                                                                      | Under B                                                                                   |
| ------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------- |
| III.1 "_Designer problem:_ … a stable fact about a value with no place to live. _Language concept:_ the named concept with its value form." | "a fact about a value" reads the concept as one value | "a stable fact about a kind of value" or "about a quantity the product is about"; the concept is the type the fact is stated over, and several relationships may carry it | keep                                                                                      |
| III.1 "The first-class object is a **concept**, not a raw scalar"                                                                           | fine                                                  | keep; a sentence may add that a concept names what values are about, and a relationship names one value of it                                                             | keep                                                                                      |
| III.5 the logical Output; IV.7 (drive edges)                                                                                                | "a value drives a sink"                               | keep; the driver is a declaration of the accepted concept, chosen by the designer, not "the" producer                                                                     | would tempt "the concept's producer drives the output" — false (`one_origin_two_outputs`) |
| IV.2 nominal concepts                                                                                                                       | the counterexample and the grant                      | keep; Phase 19 could be cited as the audit that considered and rejected one-producer-per-concept, with `binding_makes_second_signature` as the structural reason          | would be rewritten                                                                        |
| IV.7 "The Source side completed" (Phase 18 guidance `SensorATemperature`/`SensorBTemperature -> Temperature`)                               | the intermediate-concept form as guidance             | keep, now labelled as the origin-unique form (FVD-0159): recommended for candidates that are different quantities, optional otherwise                                     | would become mandatory                                                                    |
| VI.5 "_Produces_ is the signature; _carried by_ … is a value per tick"                                                                      | ADR-0034's definition                                 | keep; matches `SigProduces`; a sentence may say that _produces_ is many-to-one and that the canvas never names "the producer"                                             | would be "the producer"                                                                   |
| VI.12 what Studio does not decide                                                                                                           | —                                                     | a line: Studio does not resolve a value by concept; every reference, probe and drive edge names a declaration                                                             | —                                                                                         |

## 3. What not to write

Under the result, the papers must not claim: that two producers of one concept
are an error; that the intermediate-concept rewriting is always possible
(executed on two designs, no general theorem — FVI-0030); that origin is a
semantic notion (it is syntactic: `rewrap_counts_as_origin`); or that the driver
of an output follows from a concept's producer.
