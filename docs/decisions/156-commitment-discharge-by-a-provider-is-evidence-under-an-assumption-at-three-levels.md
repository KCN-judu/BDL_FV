---
id: FVD-0156
legacy-id:
status: accepted
date: 2026-09-20
phase: 18
area: surface
supersedes: []
superseded-by: []
related: [FVD-0128, FVD-0149]
production: [ISS-0016/bears-on, PRP-0001/audits]
---

# FVD-0156: A provider discharges a Source's commitment as evidence sound under an assumption on the raw reading; static, checked and trusted levels differ in who establishes the assumption, and the trusted one is a visible hypothesis

## Status

Accepted in Phase 18.

## Decision

`RangeSoundUnder ev R r A` names evidence that accepts value-range facts under
an assumption `A` on the raw reading; `discharge_under` discharges the
provisioned target's commitment when the transfer of every reading satisfying
`A` has the property. Static: `A` is typing, established by the transducer.
Checked: `A` is the provider's validation, established by construction.
Trusted: `A` is a declared device range, an assumption the theorem carries. A
profile declaration is not evidence by itself.

## Alternatives rejected

Evidence by declaration; collapsing the three levels into one "compatible"
verdict; semantic evidence quantified over untyped inputs.

## Reason

`discharge_under`, `discharge_static`, `discharge_checked`,
`discharge_trusted`, `realizeAt_only_transfers`; executed `exC_static`,
`exC_trusted`, `exC_checked`, `exC_provider_checks`.
