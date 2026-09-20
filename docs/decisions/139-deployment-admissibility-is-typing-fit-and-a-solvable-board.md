---
id: FVD-0139
legacy-id:
status: accepted
date: 2026-09-20
phase: 14
area: surface
supersedes: [FVD-0137]
superseded-by: []
related: [FVD-0057, FVD-0062, FVD-0133]
production: [ADR-0015/supports, ADR-0036/supports]
---

# FVD-0139: Deployment admissibility is the encoder's typing, its fit and a solvable board; fit-and-allocate alone is not admissibility

## Status

Accepted in Phase 14 (hardening pass). Supersedes FVD-0137, which was **wrong on
the same evidence**: its `Admissible` omitted the encoder's typing, so a profile
whose encoder is not `rep -> raw` could be called admissible. The separation of
the encoder from the hardware requirements that FVD-0137 stated stands.

## Decision

`DeviceOutputProfile = ⟨E, requirements⟩`.
`Admissible Θ accepts H P := P.E.WF Θ ∧ EFits Θ accepts P.E ∧ (solve H P.requirements).isSome`
— three judgments, typing, fit and allocation, none of which sees the others;
decidable (`Encoder.WF` is decided by `infer`). The strictly weaker
`FitsAndAllocates Θ accepts H P := EFits ∧ (solve …).isSome` is kept under that
narrow name only to state the gap. A solvable board is not an electrically
correct device: no voltage, current, thermal or timing property is claimed.

## Alternatives rejected

`Admissible := EFits ∧ solvable` (FVD-0137): `exJ` — an `Encoder` value whose
term is `λn. true` (typed `Q0 -> bool`, claimed `Q0 -> Q0`; `computes` holds)
fits the light and allocates one PWM line on the Nano and is not admissible.
Requirements inside the encoder; the encoder inside the hardware model; a solver
that sees the design.

## Reason

`admissible_needs_wf : Admissible ↔ E.WF Θ ∧ FitsAndAllocates`;
`admissible_satisfiable` (Phase 7's `satisfiable_iff_solve`);
`Admissible.enc_wf` is the `Encoder.WF` that `Realization.WF` demands, so an
admissible profile is what a realization may be built from. `exH_admissible`,
`exJ`.

## Consequences

Report §14.1, §14.3; minimality row "hardware requirements of an output device";
the note §2 and §5.
