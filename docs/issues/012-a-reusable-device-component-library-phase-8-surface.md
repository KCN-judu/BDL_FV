---
id: FVI-0012
legacy-id: OI-12
state: resolved
area: behavior
opened: 2026-09-15
resolved-by:
  [
    docs/reports/phase-13-source-provision-by-device-transducers-prp-0001-audit.md,
    docs/reports/phase-14-output-realization-by-device-encoders.md,
  ]
related: []
production: [ISS-0016, ISS-0017]
---

# FVI-0012: A reusable device-component library (Phase 8 surface)

## Problem

A reusable device-component library (Phase 8 surface).

## Resolution

Resolved (2026-09-20) — premise rejected. A device is not a behaviour component:
Phase 13 realizes a Source by a deployment `Channel`/`DeviceProfile` (FVD-0121,
FVD-0124) and Phase 14 realizes an output by a deployment
`Encoder`/`DeviceOutputProfile` (FVD-0131 … FVD-0139); neither is a Phase-8
component, and forcing devices into components would put a protocol into the
design (FVD-0131). Production's registry is code (ADR-0036) and the remaining
question — a reusable device-profile _catalogue_ and who owns it — is
production's ISS-0017, not a formal one.
