---
id: FVD-0125
legacy-id: D-125
status: accepted
date: 2026-09-20
phase: 13
area: surface
supersedes: []
superseded-by: []
related: []
production: [PRP-0001/audits]
---

# FVD-0125: Shared raw reading is primitive; the singleton is its special case

## Status

Accepted in Phase 13.

## Decision

`Provision = ⟨r, clock, chan⟩`; `Provision.one`.

## Alternatives rejected

The singleton as primitive with a later generalization.

## Reason

The IMU case (`exF`) and the joint-section finding (`no_joint_witness`) are
invisible in the singleton; every theorem is stated once for the general form.
