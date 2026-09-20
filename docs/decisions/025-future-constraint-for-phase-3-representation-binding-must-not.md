---
id: FVD-0025
legacy-id: D-25
status: accepted
date: 2026-09-15
phase: 2
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0013/supports]
---

# FVD-0025: Future constraint for Phase 3: representation binding must not defeat semantic identity

## Status

Accepted in Phase 2.

## Decision

Unrestricted `rep : sem s → R` and `mk : R → sem s` would let
`mkMotor (repTilt x)` reconstruct an implicit `Tilt → MotorAngle` path with no
declared semantic mapping, falsifying `no_semantic_value_without_declaration`
and reducing `Ty.sem` to ceremony. Phase 3 must decide which representation
observations are safe, which semantic constructions are safe, and when crossing
`SemanticId`s must require a declared mapping; it must test (A) unrestricted
symmetric `mk`/`rep`, (B) restricted/capability-controlled construction, (C)
binding available only inside realization/elaboration, (D) an explicit witness
`RepresentationBinding s r`, (E) semantic mappings as the only user-visible
cross-identity path — starting with an attempt to construct the bypass
counterexample. Not solved here.
