---
id: FVI-0007
legacy-id: OI-07
state: open
area: behavior
opened: 2026-09-15
resolved-by: []
related: [FVI-0006]
production: []
---

# FVI-0007: `toComponent` realizes its chosen interface; port-level inter-instance causality

## Problem

`toComponent` realizes its chosen interface (decidable side condition, not
proved); port-level inter-instance causality graph.

## Audit (2026-09-20)

Ready, together with FVI-0006 (one modular-semantics phase): production flattens
instances into the flat design and has port-level bindings, so a port-level
inter-instance causality graph has a production object to correspond to.

## Resolution

Open.
