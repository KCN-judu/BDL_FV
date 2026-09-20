---
id: FVI-0023
legacy-id:
state: open
area: surface
opened: 2026-09-20
resolved-by: []
related: [FVI-0022, FVI-0024]
production: [ISS-0017, ADR-0037]
---

# FVI-0023: Raw command → adapter operation, and what lies below the register

## Problem

Phase 14 proves the abstract output trace → raw command trace; production's adapter (ADR-0037) turns `Tick.commands` into abstract sink operations through an explicit boundary policy (finite duty in `0 ..= 255` rounds half up and is applied, anything else is refused and the line holds; a driver not due leaves the line). Phase 15 models that one boundary — `Policy`, `Op`, `AdapterOp`, the line as a fold — and proves the operation is determined by the lowered sink's value. What lies below is not modelled: production's `f64` rounding before the range check (the kernel has no fractions), the HAL call, the register, the electrical world; the generated Rust's correspondence to `AdapterOp` is production-tested (`host_adapter_operations_correspond_to_the_commands`), never proved.

## Current evidence

`BDL/Surface/Adapter.lean`: `AdapterOp.det`, `adapter_of_sink`, `sink_of_adapter`, `Line.det`, `line_holds_on_refusal`, `line_value_accepted`; `AdapterExamples.lean` `exA`–`exC`.

## Dependencies

A rational or floating model of the rounding step if the `f64` policy is to be proved; a verified-compiler theorem for anything below the operation.

## Resolution

Open.
