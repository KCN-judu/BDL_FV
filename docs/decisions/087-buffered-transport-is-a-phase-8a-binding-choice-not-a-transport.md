---
id: FVD-0087
legacy-id: D-87
status: accepted
date: 2026-09-17
phase: 9a
area: core
supersedes: []
superseded-by: []
related: []
production: [ADR-0021/supports]
---

# FVD-0087: Buffered transport is a Phase-8a binding choice, not a transport kind

## Status

Accepted in Phase 9a.

## Decision

A sensor component provides both its event and its log; binding the log through
`sync nil` yields the window (`transport_trace`), binding the event yields
`latest` (`latest_transport_loses`). No new binding kind.
