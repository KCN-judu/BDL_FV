---
id: FVI-0011
legacy-id: OI-11
state: open
area: validation
opened: 2026-09-15
resolved-by: []
related: []
production: []
---

# FVI-0011: Numeric and shared-configuration hardware feasibility (timer/PWM slices, modes, budgets)

## Problem

Numeric (summation) hardware constraints and shared-configuration conflicts: two
outputs on one timer slice needing incompatible frequencies or modes; a current
or thermal budget. The formal hardware model (Phase 7) has unary and binary
structural constraints only. Minimal unsat cores were split out to FVI-0028
(explanation, not correctness).

## Audit (2026-09-20)

Now concretely motivated: production's RP2040 target derives the PWM slice
`(n/2) % 8` and channel from the pad and checks it against the board file
(ADR-0037); both channels of a slice share `top` and divider, so two outputs on
one slice with different carriers would conflict — masked today only because the
adapter fixes one carrier (divider 16) for every slice. The question is ready;
below FVI-0023 in priority.

## Resolution

Open.
