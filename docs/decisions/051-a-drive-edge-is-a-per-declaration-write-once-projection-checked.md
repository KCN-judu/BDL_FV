---
id: FVD-0051
legacy-id: D-51
status: accepted
date: 2026-09-15
phase: 6
area: core
supersedes: []
superseded-by: []
related: [FVD-0052]
production: [ADR-0005/supports]
---

# FVD-0051: A drive edge is a per-declaration write-once projection `β`, checked by type and clock equality

## Status

Accepted in Phase 6.

## Alternatives rejected

An output expression primitive; output binding in `Ty` or in `HasType`; a
binding that coerces or synchronizes.

## Reason

`output_binding_preserves_semantic_identity_and_dimension`,
`output_binding_respects_clock_domain`; keying `β` by declaration (not by sink)
keeps single-driver a real global check (FVD-0052).
