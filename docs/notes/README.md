# Design notes

A design note is the phase's account for a reader outside the Lean sources: what
the question was, what is proved, what is not, the verdicts, and — where the
note was written for the production repository — the implementation guidance. A
note complements the phase report (the evidence) and the decisions (the
choices); it never carries a claim the report does not. Notes are edited only to
keep their claims true (a later phase's correction is recorded, not silently
applied).

Nine notes were top-level files until 2026-09-20
([migration report](../project/migration-report.md)). Start a new one from
[TEMPLATE.md](TEMPLATE.md).

| Note                                                                                                                                    | Phase | Area        | Date       |
| --------------------------------------------------------------------------------------------------------------------------------------- | ----- | ----------- | ---------- |
| [Behavior as a First-Class Design Object](behavior-as-a-first-class-design-object.md)                                                   | 8a    | behavior    | 2026-09-15 |
| [From Behavior Grouping to Reusable Behavior Components](behavior-grouping-and-component-extraction.md)                                 | 8b    | behavior    | 2026-09-16 |
| [Behavior-System Extension Requirements](behavior-system-requirements.md)                                                               | 8a    | behavior    | 2026-09-15 |
| [Lossless Buffered Cross-Domain Events with Ordinary List Data](lossless-buffered-cross-domain-events.md)                               | 9a    | core        | 2026-09-17 |
| [Minimal Data Abstraction and the Polymorphic Equation Language](polymorphic-equation-language.md)                                      | 9b    | surface     | 2026-09-17 |
| [Unit Coordinates and Formula-Assembly Semantics](unit-coordinates-and-formula-assembly.md)                                             | 10    | surface     | 2026-09-18 |
| [Natural Expression Surface as Conservative Desugaring](natural-expression-surface.md)                                                  | 11    | surface     | 2026-09-18 |
| [Unit-domain normalization and the source boundary — design note (Phase 12)](unit-domain-normalization.md)                              | 12    | surface     | 2026-09-18 |
| [Source provision by device transducers — formal audit of PRP-0001 (Phase 13)](source-provision-by-device-transducers.md)               | 13    | surface     | 2026-09-20 |
| [Output realization by device encoders — the output-side dual of Source provision (Phase 14)](output-realization-by-device-encoders.md) | 14    | surface     | 2026-09-20 |
| [The adapter boundary and the device clock (Phase 15)](the-adapter-boundary-and-the-device-clock.md)                                    | 15    | surface     | 2026-09-20 |
| [Communication as state, catalogue profiles, and `assign` (Phase 16)](communication-as-state.md)                                        | 16    | surface     | 2026-09-20 |
| [The provider's occurrence contract and the output window (Phase 17)](the-provider-contract-and-the-output-window.md)                   | 17    | surface     | 2026-09-20 |
| [The Source-side boundary (Phase 18)](the-source-side-boundary.md)                                                                      | 18    | surface     | 2026-09-20 |
| [Concepts and their producers (Phase 19)](concepts-and-their-producers.md)                                                              | 19    | experiments | 2026-09-21 |
| [Paper impact — several producers of one concept (Phase 19)](paper-impact-producers-of-one-concept.md)                                  | 19    | paper       | 2026-09-21 |
| [One producer per concept (Phase 20)](one-producer-per-concept.md)                                                                      | 20    | core        | 2026-09-21 |
