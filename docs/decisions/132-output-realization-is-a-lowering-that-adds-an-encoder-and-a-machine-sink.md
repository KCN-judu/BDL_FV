---
id: FVD-0132
legacy-id:
status: accepted
date: 2026-09-20
phase: 14
area: surface
supersedes: []
superseded-by: []
related: [FVD-0121, FVD-0131]
production: [ADR-0015/supports, ADR-0036/supports]
---

# FVD-0132: Output realization is a lowering that adds an encoder declaration and a machine sink; the logical output is never retargeted

## Status

Accepted in Phase 14.

## Decision

A realization `⟨o, d, p, e, E⟩` lowers to
`lowerΔ Δ R spec = Δ[e ↦ ⟨raw, []⟩ := encode (rep d)]`,
`lowerΩ = Ω[p ↦ ⟨raw, spec.clock⟩]`, `lowerβ = β.bind e p`,
`lowerΚ = Κ[e ↦ spec.clock]` (Model C). The specification it implements is
`RawCommand` on the unchanged design (Model B): the command specified for `R` is
`transfer` of what `o` carries; that `p` carries it is `lower_correspondence`.
`o`, its driver `d`, the edge `β d = o` and every other declaration are
untouched; nothing enters `Core`.

## Alternatives rejected

**Model A** — retarget `o.accepts := raw` and re-drive `e -> o`:
`retarget_breaks_driveWF` (the existing edge fails `DriveWF`; Phase 6's
`rebinding_invalidates_design` already calls retargeting an edit; executed
`exI`). A provision expression form, an effect, a `Ty` constructor.

## Reason

`lower_correspondence`: `PhysicalOutput Δ' p t w ↔ RawCommand Δ R t w` — the
lowering implements the specification exactly, tick by tick in the output's
clock. `behavior_unchanged`, `lower_transparent`,
`lower_physicalOutput_unchanged`: the behaviour is literally unchanged off `e`.
`lower_envRefines`, `lower_driveWF`, `lower_singleDriver` (Phase 6's
`first_output_binding_is_monotone`), `lower_completeOutputs`, `lower_wf`,
`lower_causal`, `lower_wellClocked`.

## Consequences

Unlike Source provision (FVD-0121), no declaration changes state and no role
moves: the Source side realizes an unresolved declaration; the output side adds
downstream structure only. `EnvRefines Δ Δ'` holds trivially (one fresh
declaration) and is not the interesting relation; the interesting fact is
`Δ' x = Δ x` for every pre-existing `x`.
