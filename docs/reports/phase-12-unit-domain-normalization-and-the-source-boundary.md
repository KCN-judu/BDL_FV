---
kind: report
phase: 12
area: surface
date: 2026-09-18
status: current
---

# Phase 12 — Unit-domain normalization and the source boundary

Question (production ADR-0029, ISS-0014): a relationship with no explicit inputs
has canonical type `() -> B` with `()` the empty product, while the kernel
interface types it `B`. Is the canonical type a conservative interface
normalization over the existing kernel — same typing, evaluation and clock
judgments — or does it need a kernel unit type? Conservative; no unit type.
Files: `BDL/Surface/UnitDomain.lean`, `BDL/Experiments/UnitDomainExamples.lean`;
note `docs/notes/unit-domain-normalization.md`.

**Production read.** `bdl_ir::Ty::Unit` is a real type in production's IR with
the ordinary predicates (data, sem-free, empty grant); `Ty::domain_of` gives
`()`, `A`, `A × (B × …)`; `Ty::of_signature` is `domain -> B`;
`Ty::kernel_of_signature` is the curried, unit-eliminated `expectedType`;
`Ty::canonical_mapping_ty` uncurries back; the two are tested inverse over
signatures. `Signature::is_unit_domain` is `inputs.is_empty()`, the one
predicate behind "read as a value / may drive / may be transported / may hold
memory / is a simulation input when unresolved". The surface spells `()` only to
open a signature and as the argument `f(())`, which elaborates — with `f` and
`f()` — to one `declRef`. `Ty::Unit` never types a Core term, a representation
or a runtime value. Explain shows the canonical type and the empty-product
sentence; protocol 0.14 adds `TypeView.kind = unit`. Simulation inputs in Studio
are `!hasDefinition && isUnitDomain`.

**Interface layer.** `Sig = {inputs : List Ty, output : Ty}`; `CTy` = kernel
types + `unit` + interface `arr`/`prod` (production's `Ty` with `Unit`, kept
above the kernel); `domainOf`, `canonical`, `encode` (`foldr arr`),
`uncurry`/`decode`, `canonicalOfKernel`. Proved: `encode_decode` (all kernel
types), `decode_encode`, `canonicalOfKernel_encode`, `encode_injective` (output
not an arrow — every concept signature), `canonical_injective`. Unit elimination
is a _function_ `elim : CTy → Option Ty` (well-founded on a weight that currying
and unit elimination both decrease):
`elim_canonical : elim (canonical s) = some (encode s)`; `elim unit = none` —
the unit itself has no kernel type. So `Hom(1, B) ≅ B` is, in the existing
model, definitional normalization plus an inverse theorem: the kernel interface
type _is_ the value of the normalization on the canonical type.

**Typing (§5).** `zero_input_obligation`:
`RealizesSig ⟨[], B⟩ e ↔ HasType [] e B`, by `Iff.rfl`. `lams_typed`: a body
checked in `inputs.reverse ++ Γ` is exactly a realization of `encode` under `n`
binders; for `[]` there is no binder. The literal alternative fails:
`delay_not_under_binder`, `sync_not_under_binder` — no term
`lam dom (delay i e)` has any type, so a unit lambda in the kernel would forbid
memory in every zero-input declaration, while `zero_input_memory` shows
`delay init e : B` is a legal realization of `() -> B` under the kernel
encoding. This is the theorem behind ADR-0029's "delay and sync are typed only
outside binders", and the reason the unit is eliminated _before_ Core.

**Evaluation (§6).** `RefForm.{bare, call0, callUnit}` desugar to one `declRef`
(`refForms_agree`, by `rfl`). `Ev.declRef_env_irrelevant`,
`MEv.declRef_env_irrelevant`: a reference's value is independent of the local
environment — a realized declaration evaluates in `[]`, a source is read from
`I`. `same_tick_same_value`: two readings in one tick, under any environments,
agree (`MEv.det`). No per-reference call exists to repeat.

**Clocks (§8).** `Clocked.refForms`, `HasType.refForms`: the three spellings
have the reference's judgments, by `Iff.rfl`; the unit argument is not a term,
has no domain, no activation, no step.

**Source role (§7, §10).** `Source Δ d := realizationOf d = none`;
`UnitDomain Δ d := tyView d` is not an arrow. `source_value`: a source's value
is `I d t` in every domain and environment — indexed by `(d, t)` alone, so the
unique argument carries nothing. `resolved_not_source`: a realized unit-domain
declaration is not a source; its value is its realization's and `I` is never
consulted. `SimulationInput := Source ∧ UnitDomain` is production's narrowing
(an environment provides values, not functions); on it the kernel and production
agree (`SimulationInput.value`). The kernel's `Input` provides for _every_
unresolved declaration, arrow types included; production's narrowing is surface
policy over the same semantics, recorded as such.

**Consequences (§9, §12).** `transport_needs_unit_domain`,
`delay_needs_unit_domain`: a well-typed `sync`/`delay` of a reference forces the
referenced type to be data, hence not an arrow — production's
`reference.transport_of_relationship` is a corollary. `driver_is_unit_domain`:
under `DriveWF`, a driver of a sink accepting a non-arrow type is unit-domain —
"may drive an output" is the drive rule.

**`A -> ()` (§11).** Denotationally, `homUnit : (Unit → β) ≅ β` and
`unit_codomain_collapse : ∀ f g : α → Unit, f = g` (funext only);
`consumers_indistinguishable`. A pure total function into the unit has one
inhabitant up to extensionality, so a type `A -> ()` cannot say which physical
output receives `A`; and `MEv` has no effect component
(`eval_independent_of_drives`). Physical consumption stays `OutputId` +
`DriveWF` + `SingleDriver` + `CompleteOutputs` (Phase 6): the receiver is named
by the edge, the value delivered is the driver's, of type `A`.

**Executed (A–E).** Signatures round-trip and `elim` computes the encodings;
`boost := delay 0 (boost + 1)` read as `boost`/`boost()`/ `boost(())` gives
`0, 1, 3` at ticks `0, 1, 3` and the same under a non-empty local environment;
`TempSensor` (unresolved) reads `I`, `boost` ignores `I`; `infer` accepts
`delay … : Q0` in `[]` and refuses `lam _ (delay …)`; `sync` of `boost` and of
`TempSensor` typed, of `dimByTilt` refused.

**Verdicts.** Unit interface notation — KEEP (surface/interface normalization,
`CTy`); unit kernel type — REMOVE (`elim_canonical`, `delay_not_under_binder`);
unit runtime value — REMOVE (no term former, no `Value`); source semantic kind —
REMOVE/derive (`Source` is a realization state); source surface role — KEEP in
surface (`SimulationInput`); `A -> ()` as physical sink — REMOVE
(`consumers_indistinguishable`); `OutputId` / drive boundary — KEEP. 44 theorems
(39 in `UnitDomain.lean`, 5 executed examples) on `propext`/`Quot.sound`; no
`Classical.choice`.

**Behavior semantics vs realization.** The kernel is: environment-provided
inputs (`I`), pure internal computation (`Ev`/`MEv`), output obligations
(`DriveWF`, `CompleteOutputs`). Sensor reads, buses, GPIO/PWM and device I/O are
the platform adapter's; nothing in the kernel names them, and this phase adds
nothing that does.
