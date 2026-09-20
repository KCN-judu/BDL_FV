---
id: FVD-0065
legacy-id: D-65
status: accepted
date: 2026-09-15
phase: 8a
area: behavior
supersedes: []
superseded-by: []
related: []
production: [ADR-0021/supports, ADR-0022/supports]
---

# FVD-0065: A port is a template declaration by identity, with its public interface and clock

## Status

Accepted in Phase 8a.

## Alternatives rejected

Ports by display name; ports as a separate kernel sort; physical sinks as ports.

## Reason

Bindings must respect `tyView` and commitments (Phase 1), so the port _is_ the
declaration's interface; sinks are resources, not relationships (Phase 6), and
stay in `Ω`/`β` (`ExternalSingleDriver`).
