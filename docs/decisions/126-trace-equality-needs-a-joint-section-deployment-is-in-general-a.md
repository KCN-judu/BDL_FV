---
id: FVD-0126
legacy-id: D-126
status: accepted
date: 2026-09-20
phase: 13
area: surface
supersedes: []
superseded-by: []
related: []
production: [PRP-0001/audits]
---

# FVD-0126: Trace equality needs a joint section; deployment is in general a strict refinement

## Status

Accepted in Phase 13.

## Decision

`provision_abstracts` (⊆ always), `provision_exact` (= under `JointSection`),
`JointSection.one`, `exE`, `no_joint_witness`.

## Alternatives rejected

"surjective ⇒ equal traces".

## Reason

Pointwise surjectivity gives neither a raw input (choice) nor, for shared
readings, a joint witness.
