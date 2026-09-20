---
id: FVD-0027
legacy-id: D-27
status: accepted
date: 2026-09-15
phase: 3
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0013/supports]
---

# FVD-0027: Representation types are sem-free (`ConceptEnv.WF`)

## Status

Accepted in Phase 3.

## Alternatives rejected

Allowing `Θ s = some (sem s')`.

## Reason

`rep` would then be a hidden mapping under every policy
(`binding_to_semantic_type_is_hidden_mapping`). A constraint the brief did not
anticipate; discovered while building Model A.
