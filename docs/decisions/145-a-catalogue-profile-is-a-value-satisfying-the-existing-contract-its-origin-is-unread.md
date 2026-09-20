---
id: FVD-0145
legacy-id:
status: accepted
date: 2026-09-20
phase: 16
area: surface
supersedes: []
superseded-by: []
related: [FVD-0122, FVD-0133, FVD-0139, FVD-0143]
production: [ISS-0016/bears-on, ISS-0017/bears-on]
---

# FVD-0145: A catalogue profile is a value satisfying the existing contract; its origin is unread; packages extend realizability, not the kernel

## Status

Accepted in Phase 16.

## Decision

A package contributes catalogue entries — `InputEntry ⟨origin, DeviceProfile⟩`
(Phase 13: a raw type and channels) and `OutputEntry ⟨origin,
DeviceOutputProfile⟩` (Phase 14: an encoder and requirements) — and nothing
else the semantics can see. The contract an entry must satisfy is the one the
phases already state: `InputContract Θ τ ch := ch.WF Θ ∧ Fits Θ τ ch` and
`OutputContract Θ accepts P := P.E.WF Θ ∧ EFits Θ accepts P.E`. `Origin`
(`builtin | package PackageId`) is a field no judgment reads. A larger
catalogue realizes and provisions more (`Realizable`, `Provisionable`,
`realizable_mono`, `provisionable_mono`); no typing, evaluation, causality or
clock rule takes a catalogue.

## Alternatives rejected

A `Package` object with versions, names or registries inside a judgment;
package management (resolution, lockfiles, signatures) as a formal object; a
separate `Package.lean` for organisation alone (the objects live beside
`assign`, which uses them).

## Reason

`assign_indistinguishable` and `assignSource_origin_irrelevant`
(`BDL/Surface/Assignment.lean`): two entries with one profile give one lowered
design, one output/drive/clock environment, one `RawCommand` relation and one
`AdapterOp` relation for every policy — by rewriting the realization, which is
a function of the profile (`OutputEntry.realization_of_profile`). Executed:
`exP_origin`. `WF.contract` shows `Provision.WF` asks exactly the input
contract per target.

## Consequences

Production's device library (`docs/spec/concept-library.md` "Device library",
LIB-3) is a catalogue of such entries; the five registry profiles of ADR-0036
are `builtin` entries. Whether an entry came from a package is a provenance
fact for the Deploy page, never for admissibility.
