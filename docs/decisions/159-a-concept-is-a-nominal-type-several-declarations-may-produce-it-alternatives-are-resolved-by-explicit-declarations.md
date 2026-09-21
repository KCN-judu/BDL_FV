---
id: FVD-0159
legacy-id:
status: superseded
date: 2026-09-21
phase: 19
area: experiments
supersedes: []
superseded-by: [FVD-0161]
related: [FVD-0019, FVD-0020, FVD-0022, FVD-0053, FVD-0160]
production: [ADR-0034/supports, ADR-0032/bears-on]
---

# FVD-0159: A concept is a nominal type; several declarations may produce values of it in one design; alternatives are resolved by an explicit declaration over declaration references, never by a resolver primitive or a lookup by concept

## Status

Accepted in Phase 19, after an audit that began without imposing uniqueness and
without defending the model at HEAD. It confirms FVD-0019 and FVD-0020 ("a
concept is a type, a declaration is a value") against the two alternatives and
adds the guidance on alternatives.

## Decision

`Ty.sem C` is a nominal type. Any number of declarations of one design may
announce `C` in result position, construct `C` under their own grant, or be
Sources of `C`; `GlobalWF`, `Causal`, `WellClocked`, `DriveWF` gain no
per-concept clause. "The value of concept `C`" has no denotation in the kernel;
every reference is `declRef d`, and no construct names a concept to obtain a
value. When a design has several candidate values of one concept, the resolution
is one ordinary declaration whose formula selects, blends or bounds over the
candidates (`ite`, arithmetic, `max`, …) — Phase 6's `selected`, `blended`,
`maxed` — and it, not a policy, is what a drive edge names. The recommended form
for candidates that are _different quantities_ (two sensors' readings, a manual
and an automatic setting) gives each its own concept and makes the resolver the
one origin of the shared concept (`SensorA`, `SensorB -> Temperature`);
candidates that are _the same quantity under different rules_ (a base angle and
its correction) may share the concept as Phase 6 does. Both forms are legal and,
on the executed designs, trace-equivalent.

## Alternatives rejected

- **Model B, one producer per concept**: as a signature invariant refuted by
  every bound component and every named transport
  (`binding_makes_second_signature`, `transport_second_signature`); as an origin
  invariant it fails ordinary component reuse and Phase 6's composition and has
  no kernel consumer — FVD-0160.
- **Model C with a resolver primitive** (a construct that takes "the candidates
  of `C`" and a policy): everything it would express is an ordinary declaration
  over `declRef`s today (`sensors_rewriting_same_trace`,
  `override_rewriting_same_trace`), and a policy attached to the concept rather
  than to a declaration is the hidden arbitration Phase 6 rejected
  (`hidden_arbitration_observable`, FVD-0053).
- **A lookup by concept** (`valueOf C`): ill-defined when two producers exist
  (`two_C_values_coexist`) and unnecessary when one does.

## Reason

`second_producer_invisible` (a second producer changes nothing any term
evaluates, from `update_transparent`) with `Ev.det`: multiplicity of producers
makes no kernel judgment ambiguous. `sensors_rewriting_same_trace`,
`override_rewriting_same_trace` and `sensorsC_mkUnique`: the explicit-resolution
form with intermediate concepts exists for the alternative-producer uses the
development knows, with the same downstream trace, using no new construct. The
absence of a design that needs two origins of one concept is recorded as
FVI-0030, not claimed.

## Consequences

Minimality rows "producer uniqueness per concept" and "resolver primitive /
lookup by concept" (both _no_). Production's ADR-0034 definition of _produces_
(the signature) is the signature notion `SigProduces`; a canvas may list every
producer of a concept, and must not present one of them as _the_ producer. The
papers' sentences that read a concept as one quantity are listed in the
paper-impact note; none is a false theorem statement.
