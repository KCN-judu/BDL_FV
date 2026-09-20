---
id: FVD-0071
legacy-id: D-71
status: accepted
date: 2026-09-15
phase: 8a
area: behavior
supersedes: []
superseded-by: []
related: []
production: [ADR-0021/supports, ADR-0022/supports]
---

# FVD-0071: Evidence must be equivariant and port-sound

## Status

Accepted in Phase 8a.

## Reason

`Evidence.Equivariant` is what "template validity is independent of instance
identity" means for commitments; `Evidence.PortSound` is what makes binding by
reference inherit commitments. Both are conditions on the validation layer, like
`Evidence.Monotone`.
