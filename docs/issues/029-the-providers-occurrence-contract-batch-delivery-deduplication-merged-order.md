---
id: FVI-0029
legacy-id:
state: open
area: surface
opened: 2026-09-20
resolved-by: []
related: [FVI-0020, FVI-0024, FVI-0001]
production: [ISS-0016, ISS-0001]
---

# FVI-0029: The provider's occurrence contract: batch delivery, deduplication of transport retries, merged order across raw sources, a per-tick bound

## Problem

Phase 16 encodes every tested communication case as state over the existing
kernel (FVD-0143), and the encodings rest on what a raw reading _means_ at the
boundary: a `list raw` reading delivers the occurrences that arrived since the
previous tick, in arrival order (`exC_same_tick`, `exK_cross_clock`); a
transport retry that the adapter delivers twice is two semantic occurrences
(`exF_identity` shows the design can deduplicate by semantic id, `exL_theorem`
that a transport identity the channel discards is unobservable — but which of
the two a given provider does is the provider's); two raw sources delivering
inside one base tick have no order in the model unless the adapter merges them
into one raw reading; and the per-tick batch must be bounded for the deployment
to be bounded (ADR-0027's rule, on the input side). None of this is a language
question; all of it is what a Source device profile (ISS-0016) has to promise,
and no formal statement of the promise exists.

## Current evidence

`BDL/Experiments/CommunicationExamples.lean` `exC_same_tick`, `exF_identity`,
`exK_cross_clock`, `exL_theorem`; Phase 16 report §16.2 (the attacks);
`Validation/Capacity.lean` for the cross-domain bound; production refuses a
design with a Source (`adapter.inputs_unbound`, ADR-0037) and bounds collections
by the design (ADR-0027).

## Dependencies

Production's Source device binding (ISS-0016) and the window's surface form
(ISS-0001): the first provider whose batch semantics can be read from code.

## Resolution

Open.
