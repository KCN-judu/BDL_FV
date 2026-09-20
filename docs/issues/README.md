# Formal open items

An open item is a question the formal development has recognised and not
answered: a construct not modelled, a theorem not proved, a boundary not tested.
It is the record for "we know this is unresolved" — never a claim that the
tentative answer holds. When a phase answers it, the item is `resolved`,
`resolved-by` names the phase report (or the decision) that answers it, and the
row moves to the _Resolved_ table; the record itself stays. When the development
decides not to decide, the item is `deferred` with the reason in its Resolution
section. IDs are `FVI-NNNN`; an item that is the formal side of a production
issue or proposal names it in `production`, and current documents cite the two
together — `ISS-0004 (FVI-0017)`.

The items were carried in the _Open items_ list at the end of the report until
2026-09-20 and were `OI-NN` for a few hours that day
([decision-id-migration.md](../project/decision-id-migration.md)); their
`opened` dates are the commits that first listed them. Start a new record from
[TEMPLATE.md](TEMPLATE.md).

## Active

| ID                                                                                           | Item                                                                                                                         | State | Area       | Opened     | Production record  |
| -------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------- | ----- | ---------- | ---------- | ------------------ |
| [FVI-0001](001-interface-level-references.md)                                                | Interface-level references                                                                                                   | open  | core       | 2026-09-14 | ISS-0003           |
| [FVI-0003](003-lambda-guarded-instantaneous-cycles.md)                                       | Lambda-guarded instantaneous cycles                                                                                          | open  | core       | 2026-09-15 | —                  |
| [FVI-0004](004-higher-order-unfoldspreserveseval-closure-equivalence.md)                     | Higher-order `unfolds_preserves_eval` (closure equivalence)                                                                  | open  | core       | 2026-09-15 | —                  |
| [FVI-0006](006-theorem-j-for-mev-with-sync-bindings-higher-order-theorem-j-a.md)             | Theorem J for `MEv` with `sync` bindings; higher-order Theorem J; a consistent modular input                                 | open  | behavior   | 2026-09-15 | —                  |
| [FVI-0007](007-tocomponent-realizes-its-chosen-interface-port-level-inter.md)                | `toComponent` realizes its chosen interface; port-level inter-instance causality                                             | open  | behavior   | 2026-09-15 | —                  |
| [FVI-0009](009-statehandler-with-handler-scoped-clocks-independently-clocked.md)             | StateHandler with handler-scoped clocks / independently clocked nesting                                                      | open  | behavior   | 2026-09-15 | ISS-0010           |
| [FVI-0011](011-minimal-unsat-cores-numeric-hardware-constraints-timer-and-pwm.md)            | Minimal unsat cores; numeric hardware constraints; timer and PWM compatibility                                               | open  | validation | 2026-09-15 | —                  |
| [FVI-0012](012-a-reusable-device-component-library-phase-8-surface.md)                       | A reusable device-component library (Phase 8 surface)                                                                        | open  | behavior   | 2026-09-15 | ISS-0016           |
| [FVI-0013](013-folding-clockenv-into-the-declinterface-record-churn-only.md)                 | Folding `ClockEnv` into the `DeclInterface` record (churn only)                                                              | open  | core       | 2026-09-15 | —                  |
| [FVI-0014](014-several-candidate-definitions-with-one-active-as-a-surface.md)                | Several candidate definitions with one active, as a surface convenience                                                      | open  | surface    | 2026-09-14 | ISS-0002           |
| [FVI-0015](015-environment-sensitive-evidence-and-invalidation-tracking-for.md)              | Environment-sensitive evidence and invalidation tracking for edits                                                           | open  | core       | 2026-09-14 | ISS-0003           |
| [FVI-0017](017-affine-units-a-point-difference-sort-as-optional-validation-the.md)           | Affine units: a point/difference sort as optional validation; the display-name table                                         | open  | surface    | 2026-09-18 | ISS-0004           |
| [FVI-0018](018-grant-delegation-to-higher-order-mappings.md)                                 | Grant delegation to higher-order mappings                                                                                    | open  | core       | 2026-09-15 | —                  |
| [FVI-0019](019-display-name-table-for-concepts.md)                                           | Display-name table for concepts                                                                                              | open  | surface    | 2026-09-15 | —                  |
| [FVI-0020](020-source-provision-stateful-transducers-a-device-clock-commitment.md)           | Source provision: stateful transducers, a device clock, commitment discharge, output provision                               | open  | surface    | 2026-09-20 | PRP-0001, ISS-0016 |
| [FVI-0021](021-unit-domain-normalization-elim-beyond-canonical-types-the-input.md)           | Unit-domain normalization: `elim` beyond canonical types; the `Input` narrowing                                              | open  | surface    | 2026-09-18 | ADR-0029           |
| [FVI-0022](022-output-realization-stateful-adapters-a-device-clock-atomic-frames-codegen.md) | Output realization: stateful adapters, a device clock, atomic multi-value frames, codegen correspondence, output commitments | open  | surface    | 2026-09-20 | ISS-0016, ISS-0017 |

## Resolved

| ID                                                                              | Item                                                                     | Area     | Resolved by                                                                             |
| ------------------------------------------------------------------------------- | ------------------------------------------------------------------------ | -------- | --------------------------------------------------------------------------------------- |
| [FVI-0002](002-delay-temporal-boundaries.md)                                    | Delay/temporal boundaries                                                | core     | [Phase 4](../reports/phase-04-reactive-core.md)                                         |
| [FVI-0005](005-reusable-stateful-components.md)                                 | Reusable stateful components                                             | behavior | [Phase 8a](../reports/phase-08a-behaviour-as-a-first-class-design-object.md)            |
| [FVI-0008](008-event-multiplicity.md)                                           | Event multiplicity                                                       | core     | [Phase 5](../reports/phase-05-clock-domains-and-synchronization.md)                     |
| [FVI-0010](010-ty-list-and-list-operators-to-write-the-buffer-in-the-object.md) | `Ty.list` and list operators, to write the buffer in the object language | core     | [Phase 9a](../reports/phase-09a-list-data-and-lossless-buffered-cross-domain-events.md) |
| [FVI-0016](016-representation-binding-for-concepts.md)                          | Representation binding for concepts                                      | core     | [Phase 3](../reports/phase-03-representation-binding-and-physical-dimensions.md)        |
