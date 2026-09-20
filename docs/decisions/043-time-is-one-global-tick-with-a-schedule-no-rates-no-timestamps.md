---
id: FVD-0043
legacy-id: D-43
status: accepted
date: 2026-09-15
phase: 5
area: core
supersedes: []
superseded-by: []
related: [FVD-0047]
production: [ADR-0004/supports]
---

# FVD-0043: Time is one global tick with a schedule; no rates, no timestamps in the kernel

## Status

Accepted in Phase 5.

## Alternatives rejected

Domain-local counters with a scheduler relation; physical timestamps.

## Reason

The global tick with `Sched` is the smallest model that distinguishes the
behaviours in question (Counterexamples A, B, F); a period induces a schedule
(`Sched.periodic`) and everything numeric is validation (FVD-0047).
