# Phase reports

One report per phase: the question the phase asked, the definitions it added,
the models it tried, the theorems and executed counterexamples that decided
between them, the claim audit, and the verdicts. A report is the evidence a
decision cites; it is written once the phase's `lake build` is clean and edited
afterwards only to record a later phase's correction (a struck-through claim
with the phase that changed it) or a wrong path.

Section numbers inside a report are the report's own (`§1.5` is Phase 1, section
5); decisions and the paper cite them as `REPORT §1.5`. The reports were one
file (`REPORT.md`) until 2026-09-20
([migration report](../project/migration-report.md)). Start a new one from
[TEMPLATE.md](TEMPLATE.md).

| Report                                                                                                | Title                                                                                                                     | Area        | Date       |
| ----------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------- | ----------- | ---------- |
| [Phase 0](phase-00-a-single-persistent-declaration.md)                                                | a single persistent declaration                                                                                           | core        | 2026-09-14 |
| [Phase 1](phase-01-cross-declaration-references.md)                                                   | cross-declaration references                                                                                              | core        | 2026-09-14 |
| [Phase 1 → M](phase-01m-migration-holes-to-declarations.md)                                           | Migration: holes → declarations                                                                                           | core        | 2026-09-14 |
| [Phase 2](phase-02-where-does-semantic-identity-live.md)                                              | where does semantic identity live?                                                                                        | core        | 2026-09-15 |
| [Phase 3](phase-03-representation-binding-and-physical-dimensions.md)                                 | representation binding and physical dimensions                                                                            | core        | 2026-09-15 |
| [Phase 4](phase-04-reactive-core.md)                                                                  | Reactive Core                                                                                                             | core        | 2026-09-15 |
| [Phase 5](phase-05-clock-domains-and-synchronization.md)                                              | Clock domains and synchronization                                                                                         | core        | 2026-09-15 |
| [Phase 6](phase-06-physical-outputs-and-the-single-driver-discipline.md)                              | Physical outputs and the single-driver discipline                                                                         | core        | 2026-09-15 |
| [Phase 7](phase-07-hardware-constraint-validation-and-resource-allocation.md)                         | Hardware constraint validation and resource allocation                                                                    | validation  | 2026-09-15 |
| [Phase 8a](phase-08a-behaviour-as-a-first-class-design-object.md)                                     | Behaviour as a first-class design object                                                                                  | behavior    | 2026-09-15 |
| [Phase 8b](phase-08b-behaviour-grouping-and-component-extraction.md)                                  | Behaviour grouping and component extraction                                                                               | behavior    | 2026-09-16 |
| [Phase 9a](phase-09a-list-data-and-lossless-buffered-cross-domain-events.md)                          | List data and lossless buffered cross-domain events                                                                       | core        | 2026-09-17 |
| [Phase 9b](phase-09b-minimal-data-abstraction-and-the-polymorphic-equation-language.md)               | Minimal data abstraction and the polymorphic equation language                                                            | surface     | 2026-09-17 |
| [Phase 9c](phase-09c-capability-boundary-audit-data-vs-eq-vs-ord.md)                                  | Capability boundary audit: Data vs Eq vs Ord                                                                              | core        | 2026-09-18 |
| [Phase 10](phase-10-unit-coordinates-and-formula-assembly-semantics.md)                               | Unit coordinates and formula-assembly semantics                                                                           | surface     | 2026-09-18 |
| [Phase 10b](phase-10b-affine-coordinate-erasure-and-conversion-functoriality.md)                      | Affine coordinate erasure and conversion functoriality                                                                    | surface     | 2026-09-18 |
| [Phase 11](phase-11-natural-expression-surface-as-conservative-desugaring.md)                         | Natural expression surface as conservative desugaring                                                                     | surface     | 2026-09-18 |
| [Phase 12](phase-12-unit-domain-normalization-and-the-source-boundary.md)                             | Unit-domain normalization and the source boundary                                                                         | surface     | 2026-09-18 |
| [Phase 13](phase-13-source-provision-by-device-transducers-prp-0001-audit.md)                         | Source provision by device transducers (PRP-0001 audit)                                                                   | surface     | 2026-09-20 |
| [Phase 14](phase-14-output-realization-by-device-encoders.md)                                         | Output realization by device encoders                                                                                     | surface     | 2026-09-20 |
| [Phase 15](phase-15-the-adapter-boundary-and-the-explicit-device-clock.md)                            | The adapter boundary and the explicit device clock                                                                        | surface     | 2026-09-20 |
| [Phase 16](phase-16-communication-as-state-catalogue-profiles-and-the-deployment-only-assign.md)      | Communication as state, catalogue profiles, and the deployment-only `assign`                                              | surface     | 2026-09-20 |
| [Phase 17](phase-17-the-provider-occurrence-contract-and-the-output-window.md)                        | The provider's occurrence contract and the occurrence-preserving output window                                            | surface     | 2026-09-20 |
| [Phase 18](phase-18-the-source-side-boundary-provider-state-device-clock-commitments-and-readings.md) | The Source-side boundary: provider state, the device clock, initialization, commitments, `computes`, out-of-type readings | surface     | 2026-09-20 |
| [Phase 19](phase-19-may-several-declarations-produce-one-concept.md)                                  | May several declarations produce values of one nominal concept? Models A, B, C                                            | experiments | 2026-09-21 |
| [Phase 20](phase-20-one-producer-per-concept.md)                                                      | One producer per concept: the invariant, its preservation under refinement and composition, and the concept reference     | core        | 2026-09-21 |
| [Phase 21](phase-21-sem-blocks-and-mapping-blocks.md)                                                 | Sem blocks and mapping blocks: the design objects, and the concept as their type template                                 | surface     | 2026-09-21 |
