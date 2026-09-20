---
id: FVD-0127
legacy-id: D-127
status: accepted
date: 2026-09-20
phase: 13
area: surface
supersedes: []
superseded-by: []
related: []
production: [PRP-0001/audits]
---

# FVD-0127: Provision is not re-applicable; "idempotent" is the wrong word

## Status

Accepted in Phase 13.

## Decision

`provision_not_reapplicable`, `provision_source_role`; `provision_idem_total`
records that the totalized function satisfies `P (P Δ) = P Δ` only because it
overwrites with the same body; `provision_reprovision_not_refinement`.

## Alternatives rejected

"idempotent per Source".
