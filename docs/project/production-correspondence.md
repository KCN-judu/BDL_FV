---
kind: project
area: process
status: current
snapshot: de8154f5153495de2ad8a09f3ca3166c3678dc93
snapshot-date: 2026-09-20
---

# Production correspondence

Which record in the production repository (`../BDL`, KCN-judu/BDL) consumed
which phase of this development, and at which strength that repository labels
it. The strength words are production's (`docs/project/formal-correspondence.md`
there): _formally proved (model)_, _informed by FV_, _production-tested_,
_engineering choice_. This page mirrors what production's records say **at
commit `de8154f5153495de2ad8a09f3ca3166c3678dc93` (2026-09-20, after the
syntax-highlighting milestone, protocol 0.21)**; the `snapshot` field above is
the one canonical place that hash lives, and the monograph's production snapshot
cites it. The pin is deliberate: `de8154f` is the commit the whole table and the
monograph were audited against. Production has moved on (HEAD `3fba224` at the
Phase-14 hardening, protocol 0.23: the Code view IDE, Source creation over a
chosen concept); none of those milestones touches a row here, and the Phase-14
output-side facts were additionally verified at `7a800bc`, where every
output-side crate and spec (`bdl-model::surface`, `bdl-lower`, `bdl-hardware`,
`bdl-codegen-rust`, `bdl-output`, `runtime-semantics.md`, `hardware-model.md`)
is byte-identical to `de8154f`. The pin moves when a row does. It does not grade
production's labels. The direction of authority is fixed by production's
ADR-0010: the Lean development is a specification, never a dependency.

The formal side of every row is named by its `FVD` decision records
([decisions/README.md](../decisions/README.md)); each of those records names the
production record back in its `production` field, so the correspondence can be
read from either end.

## Production records that cite a phase

| Production record   | Phase   | Formal decisions                         | Formal source                                                                                                                                                                                                                                                                           | Strength production claims                                                         |
| ------------------- | ------- | ---------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------- |
| ADR-0004            | 4, 5    | FVD-0034 … FVD-0047                      | `Core/Reactive.lean`, `Core/Clock.lean` — declarations are streams under a tick relation, not tasks; `delay_is_sync_own`, `scheduling_order_observable`                                                                                                                                 | informed by FV                                                                     |
| ADR-0005            | 6       | FVD-0050 … FVD-0056                      | `Core/Output.lean` — the drive edge, `SingleDriver`; supplied computation may not drive outputs                                                                                                                                                                                         | informed by FV                                                                     |
| ADR-0006            | 7       | FVD-0057 … FVD-0062                      | `Validation/Hardware.lean`                                                                                                                                                                                                                                                              | informed by FV                                                                     |
| ADR-0008            | 1       | FVD-0014                                 | display names are not identity; `DeclId` is                                                                                                                                                                                                                                             | informed by FV                                                                     |
| ADR-0009            | 1       | FVD-0007, FVD-0016                       | `Core/Env.lean` — refinement versus edit; `local_refinement_preserves_global_wf`                                                                                                                                                                                                        | informed by FV                                                                     |
| ADR-0010            | all     | FVD-0001 … FVD-0015                      | the development as the semantic authority; production's `docs/spec/kernel.md` transcribes it                                                                                                                                                                                            | informed by FV                                                                     |
| ADR-0011            | 3       | FVD-0031, FVD-0102                       | production numerics are `f64`; the kernel's `Nat` is the recorded deviation                                                                                                                                                                                                             | engineering choice                                                                 |
| ADR-0013            | 2, 3    | FVD-0019 … FVD-0033                      | `Core/Typing.lean` — `rep`/`mk` under the declaration's own grant, `constructs_granted`; nominal `sem`                                                                                                                                                                                  | informed by FV                                                                     |
| ADR-0015            | 7       | FVD-0057, FVD-0062                       | `Validation/Hardware.lean` — deployment analysis is target-relative, non-monotone evidence                                                                                                                                                                                              | informed by FV                                                                     |
| ADR-0016            | 4       | FVD-0042                                 | the reference evaluator is the executable definition; generated Rust is held to it by differential tests                                                                                                                                                                                | production-tested                                                                  |
| ADR-0019            | 8b      | FVD-0074 … FVD-0082                      | `Behavior/Group.lean`, `Boundary.lean`, `Extract.lean`, `ExtractPreservation.lean`                                                                                                                                                                                                      | informed by FV                                                                     |
| ADR-0021            | 8a      | FVD-0064 … FVD-0073, FVD-0087            | `Behavior/System.lean`, `Instantiate.lean`, `Preservation.lean`                                                                                                                                                                                                                         | informed by FV                                                                     |
| ADR-0022            | 8a      | FVD-0065, FVD-0068                       | `Behavior/Interface.lean`, `Substitution.lean`                                                                                                                                                                                                                                          | informed by FV                                                                     |
| ADR-0024            | 9a      | FVD-0083, FVD-0084                       | `Core/ListData.lean`, `Validation/Capacity.lean`                                                                                                                                                                                                                                        | informed by FV                                                                     |
| ADR-0025            | 9b, 9c  | FVD-0088 … FVD-0100                      | `Poly.matchTy_sound` / `_complete`, `Scheme.instantiate_sound`, `Stdlib.*_typed`, `lib_expansion`, `Comb.noConstruct`, `lib_clocked`, `Generic.generic_preserves_identity` / `_dimension`, `fold_total`, `Cap.eq_iff_data`, `Cap.ord_data`, `lt_rejected`, `min_mode_rejected`          | formally proved (model); the {Data, Eq, Ord} vocabulary a design recommendation    |
| ADR-0026            | 9c      | FVD-0098 … FVD-0100                      | `Surface/Poly.lean` (`Ty.ordB`)                                                                                                                                                                                                                                                         | informed by FV                                                                     |
| ADR-0027            | 9a      | FVD-0086                                 | `Validation/Capacity.lean` — `CapacitySufficient`, `requiredCapacity`, `periodic_capacity_sufficient`, `sufficient_capacity_preserves`, `bounded_buffer_agrees`                                                                                                                         | informed by FV                                                                     |
| ADR-0028            | 10, 11  | FVD-0101 … FVD-0104, FVD-0111 … FVD-0114 | `Surface/Composer.lean`, `Surface/Units.lean` — `solve_sound`, `solve_complete`, `candidates_sound`, `candidates_complete`; `Surface/Natural.lean` — the binder, range and coalesce desugaring                                                                                          | informed by FV                                                                     |
| ADR-0029            | 12      | FVD-0115 … FVD-0117, FVD-0119, FVD-0120  | `Surface/UnitDomain.lean` — `elim_canonical`, `encode_decode`, `decode_encode`, `encode_injective`, `canonical_injective`, `zero_input_obligation`, `refForms_agree`                                                                                                                    | formally proved (model); `() -> A` as the preferred spelling an engineering choice |
| ADR-0032 (amended)  | 12, 13  | FVD-0118, FVD-0119; FVD-0121 … FVD-0130  | `Surface/UnitDomain.lean` — `Source`, `resolved_not_source`, `refForms_agree`, `consumers_indistinguishable`; the amendment of 2026-09-20 states that a provisioned Source (Phase 13) is a Value by the same derived rule                                                               | formally proved (model)                                                            |
| ADR-0034            | 1       | FVD-0005, FVD-0012                       | `Core/Dependency.lean` — `DependsOn`                                                                                                                                                                                                                                                    | informed by FV                                                                     |
| ADR-0035            | —       | —                                        | no formal content: one token classifier, the LSP vocabulary, protocol 0.21 — an engineering choice under ADR-0001                                                                                                                                                                       | engineering choice                                                                 |
| ISS-0001 (open)     | 9a      | FVD-0048, FVD-0085                       | the occurrence window as five declarations over `delay` and `sync` (`Surface/Buffer.lean`); production has no surface form                                                                                                                                                              | —                                                                                  |
| ISS-0002 (open)     | 1       | FVI-0014                                 | several candidate definitions with one active — a surface convenience over a write-once realization                                                                                                                                                                                     | —                                                                                  |
| ISS-0003 (open)     | 1       | FVD-0017, FVD-0018; FVI-0001, FVI-0015   | interface-level references and the evidence model                                                                                                                                                                                                                                       | —                                                                                  |
| ISS-0004 (open)     | 10, 10b | FVD-0106 … FVD-0110; FVI-0017            | affine charts (`Surface/Charts.lean`); the point/difference sort as optional validation                                                                                                                                                                                                 | —                                                                                  |
| ISS-0005 (open)     | 9b      | FVD-0096                                 | sums encoded as tag × optional payload; a kernel `sum` deferred                                                                                                                                                                                                                         | —                                                                                  |
| ISS-0007 (deferred) | 8b      | FVD-0082                                 | nested groups are a relation on the flat group list; packaging inside a body not modelled                                                                                                                                                                                               | —                                                                                  |
| ISS-0010 (open)     | 4       | FVI-0009                                 | temporal modifiers and contexts: the elaboration cases tested in Phase 4; handler-scoped clocks untested                                                                                                                                                                                | —                                                                                  |
| ISS-0014 (resolved) | 11, 12  | FVD-0115 … FVD-0117                      | Phase 12 proved the unit-domain normalization; resolved by ADR-0029                                                                                                                                                                                                                     | formally proved (model)                                                            |
| ISS-0016 (open)     | 13      | FVD-0121 … FVD-0130; FVI-0012, FVI-0020  | a device binding for a Source: the formal construction exists (PRP-0001 audit); nothing implemented                                                                                                                                                                                     | —                                                                                  |
| PRP-0001 (draft)    | 13      | FVD-0121 … FVD-0130                      | the audit: four of seven claims corrected — [Phase 13 report](../reports/phase-13-source-provision-by-device-transducers-prp-0001-audit.md), [note](../notes/source-provision-by-device-transducers.md); production's `relationship-roles.md` § Phase 13 names the ownership when built | — (the proposal is production's to decide)                                         |

## Production facts the formal development has no theorem for

Recorded so that the monograph does not overstate them (production's own words,
at the snapshot):

- **Relationship roles.** `bdl_model::RelationshipRole { Source, Rule, Value }`
  is one derived predicate — a domain with inputs is a Rule; the unit domain
  with a realization is a Value; without one, a Source — never persisted,
  authored or an identity; stated by the compiler and the daemon (protocol
  0.20); Studio re-derives nothing. The formal `Source Δ d` (FVD-0118) is the
  Source case; Rule and Value are production's reading of the realization state
  and the arrow type, with no separate formal object.
- **A Source may drive an output.** Production's `DriveWF` accepts any driver
  whose type is the sink's and whose domain is the sink's — a Source as well as
  a Value; a Rule is refused because its type is an arrow. The formal `DriveWF`
  (FVD-0051) says the same: it mentions realization nowhere.
- **`applied_by`** is the direct inverse of `references` (the kernel's
  `DependsOn`), never a transitive closure; `reactive.rule_unapplied` and the
  action `rule.apply` are IDE and product facts, not kernel kinds.
- **Commitments are empty.** `require` is a reserved word without a production;
  every declaration's commitments are `[]`; `provision_wf`'s evidence hypothesis
  (FVD-0128) is therefore vacuous in production today and no commitment solver
  exists.
- **Standard Library.** `LibraryItem → Fragment → ordinary objects` (36 Concept
  items, 8 Source items, one-transaction instantiation, protocol 0.17); an
  authoring catalogue, not the deployment device catalogue Phase 13 presupposes
  (`hardware/`, not built).
- **Unified project.** `src/**/*.bdl` canonical, `.bdl/identities.json`,
  `.bdl/authoring.json`, `ui/layout.json`; Design, Code and Split are views;
  invalid text is saveable and the graph stays last-good (ADR-0023, ADR-0030).
- **Formula Composer.** Structured nodes: reference, number, quantity, bool,
  unary, binary, compare (incl. `??`), call, slot, binder, range, `if` (a
  choice); `let`, `match`, blocks, rules and collection literals remain opaque
  text (protocol 0.13–0.17).
- **Highlighting.** One Rust classifier (`bdl-ide::tokens`), a lexical layer
  from the lossless tree plus a semantic layer from the snapshot, the LSP
  semantic-token vocabulary plus `unit` and `slot`, a versioned legend, a pure
  encoder for UTF-8/16/32 positions, protocol 0.21; Studio's Code view and
  formula field colour the same stream (ADR-0035).
- **Generated code.** `bdl-lower` + `bdl-codegen-rust` produce a `no_std` core
  held to the reference evaluator by a 22-case differential corpus, golden files
  and property tests. No refinement theorem exists (open agenda).

## Phases with no production consumer yet

Phases 2–6 are consumed only through ADR-0010 (the kernel transcription in
production's `docs/spec/kernel.md`) and through the notes' production guidance;
Phase 11's desugaring was implemented in production
(`2026-09-natural-expression-surface` change fragment) under ADR-0028's second
amendment. When production writes a record for one of these, add the row here
and nothing else.

Phase 14 (output realization by device encoders) has no production consumer:
production's `PhysicalOutput`, `DeviceBinding { kind, output, fixed_pins }`, the
requirement generation and the allocator are the logical output and the
requirements half of a device profile (FVD-0131, FVD-0139 support ADR-0015 and
ADR-0005 as they stand); the encoder half, the machine sink and the lowering do
not exist. Where a consumer would lower: `bdl-lower` plans one `OutputPlan` per
validated edge at the driver's type and the generated core emits
`Outputs { output_n: Option<T> }`; the encoder declaration and the machine sink
would enter there, and the differential corpus would compare the lowered core's
raw outputs against `transfer` of the reference evaluator's logical outputs.
What is proved stops at the raw command trace (`lower_correspondence`); the step
to the generated backend call is FVI-0022 and is not claimed. The
[note](../notes/output-realization-by-device-encoders.md) §5 records what a
consumer would need. No ISS or PRP exists for it; ISS-0016 is the Source side.

## What this page never says

That a theorem proves production code. A theorem here proves a property of the
model; production discharges it by transcription plus its own tests and labels
the result itself. When a production record claims more than the theorem states,
the correction belongs in production's records, and this page notes the
discrepancy until it is fixed there. Production's committed records at the
snapshot — and still at HEAD `3fba224` — cite the retired ledger numbers
(`D-NN`) in ADR-0024, ADR-0025, ADR-0028, `formal-correspondence.md`,
`status.md`, PRP-0001 and `equation-library.md`, and no `FVD-` id appears in a
committed production page; a documentation-convergence pass exists only in
production's working tree, uncommitted. Until it lands,
[decision-id-migration.md](decision-id-migration.md) resolves each retired
number, and this repository does not edit production's records.
