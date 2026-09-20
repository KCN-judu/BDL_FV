---
id: FVD-0064
legacy-id: D-64
status: accepted
date: 2026-09-15
phase: 8a
area: behavior
supersedes: []
superseded-by: []
related: []
production: [ADR-0021/supports, ADR-0022/supports]
---

# FVD-0064: Behaviour components are surface objects; the kernel is unchanged

## Status

Accepted in Phase 8a.

## Alternatives rejected

A kernel term for components/instances; a second typing judgment for components.

## Reason

Every property the milestone needs is a property of the flattened design under
the _existing_ judgments (`flatten_WF`, `union_globalWF`); `BDL/Core` is
untouched.
