# Unit-domain normalization and the source boundary — design note (Phase 12)

Production ADR-0029 (`KCN-judu/BDL` at `3c6c8be`) gives every relationship
one canonical type `domain(inputs) -> B`, with `domain([]) = ()` the empty
product, and encodes it into the kernel by currying and unit elimination.
ISS-0014 asked the formal development whether that is a theorem.  This note
records the answer, what is theorem, what is definitional normalization, and
what stays production-only presentation.  Lean: `BDL/Surface/UnitDomain.lean`,
`BDL/Experiments/UnitDomainExamples.lean`.

## 1. What production does (read, not inferred)

| production | meaning |
|---|---|
| `bdl_ir::Ty::Unit` | the empty product; a real IR type (data, sem-free, empty grant); never the type of a Core term, a representation or a runtime value |
| `Ty::domain_of(inputs)` | `()` / `A` / `A × (B × …)` (right-nested) |
| `Ty::of_signature` | the canonical type `domain -> B` |
| `Ty::kernel_of_signature` | `A₁ -> … -> Aₙ -> B`, and `B` for no inputs: `DeclInterface.expectedType` |
| `Ty::canonical_mapping_ty` | uncurry a kernel type back to the canonical one; tested inverse over signatures |
| `Signature::is_unit_domain` | `inputs.is_empty()` — the one predicate behind read-as-value, may-drive, may-transport, may-hold-memory, simulation-input-when-unresolved |
| syntax | `()` opens a signature (`mapping f : () -> B`, shorthand `mapping f : B`); `(A, B) -> C` is `A -> B -> C`; `f`, `f()`, `f(())` are one `declRef`; `()` is refused as a value anywhere else, as an output, after an input, as a value form |
| protocol 0.14 | `TypeView.kind` may be `unit` (additive); `Signature` unchanged |
| Explain | `canonical type: () -> B`, the empty-product sentence, the kernel `interface` |
| Studio | simulation inputs are `!hasDefinition && isUnitDomain`; no input socket for the unit domain |

## 2. The formal account

### 2.1 Interface layer (`CTy`), not kernel

`Sig = {inputs : List Ty, output : Ty}`.  `CTy` is production's `Ty` with
`Unit` — `unit | k τ | arr | prod` — kept *above* the kernel.  `domainOf`,
`canonical s = arr (domainOf inputs) (k B)`, `encode s = foldr arr B inputs`,
`decode = uncurry`, `canonicalOfKernel = canonical ∘ decode`.

Theorems: `encode_decode` (identity on every kernel type); `decode_encode`,
`canonicalOfKernel_encode`, `encode_injective` (whenever the output is not
an arrow — every concept signature); `canonical_injective`.

### 2.2 Unit elimination is a function, and `expectedType` is its value

`elim : CTy → Option Ty` — `unit ↦ none`, `k τ ↦ τ`, `arr unit c ↦ elim c`,
`arr (prod a b) c ↦ elim (arr a (arr b c))`, otherwise structural.  Proved
total by a weight that both currying and unit elimination decrease.

**`elim_canonical : elim (canonical s) = some (encode s)`.**  Production's
"two isomorphisms the kernel works with directly" are one normalization
function; the kernel interface type is what it computes.  `elim unit = none`:
the unit alone has no kernel type — it is never a value's type, which is
exactly production's "never in a Core term".

So `Hom(1, B) ≅ B` in this model is: definitional at the kernel (the
obligation *is* `HasType [] e B`), a theorem at the interface (the inverse
pair above), and `homUnit : (Unit → β) ≅ β` denotationally.

### 2.3 Typing: no binder

`zero_input_obligation : RealizesSig ⟨[], B⟩ e ↔ HasType Θ Δ G [] e B` is
`Iff.rfl`.  `lams_typed`: a body checked in the context of its inputs is a
realization of the kernel type under `n` binders; for `[]`, none.

The literal alternative — `λ(). body` in the kernel — is refused by a
theorem, not a preference: **`delay_not_under_binder`** and
**`sync_not_under_binder`** (no `lam dom (delay i e)` has any type, for any
`dom`), while **`zero_input_memory`** shows `delay init e` is a legal
realization of `() -> B`.  A kernel unit binder would forbid memory in every
zero-input declaration.  This is why the unit is eliminated before Core.

### 2.4 Evaluation: a reading, not a call

`RefForm.{bare, call0, callUnit}` desugar to one `declRef`
(`refForms_agree`).  `Ev/MEv.declRef_env_irrelevant`: the reference's value
does not depend on the local environment — a realized declaration evaluates
in `[]`, a source is read from `I`.  `same_tick_same_value`: two readings in
one tick agree.  There is no per-reference application to repeat, and the
unique argument has nowhere to carry information.

### 2.5 Clocks

`Clocked.refForms`, `HasType.refForms` are `Iff.rfl`: no unit clock, no
activation, no evaluation step.  `ClockEnv` is over declarations; the unit
argument is not a term.

### 2.6 Source role ≠ type shape

`Source Δ d := realizationOf d = none`.  `UnitDomain Δ d := tyView d` is not
an arrow.  **`source_value`**: a source's value is `I d t` — environment
provision indexed by `(d, t)`, in every domain and environment.
**`resolved_not_source`**: a realized `() -> B` never consults `I`.
`SimulationInput := Source ∧ UnitDomain` is production's narrowing (an
environment provides values, not functions); the kernel's `Input` provides
for every unresolved declaration.  The narrowing is surface policy over the
same semantics.  Every mathematical `() -> A` is not a sensor.

### 2.7 The two production consequences are corollaries

`transport_needs_unit_domain`, `delay_needs_unit_domain` (from the `Data`
premise of `sync`/`delay`) — production's
`reference.transport_of_relationship`.  `driver_is_unit_domain` (from
`DriveWF`: a driver's type equals the accepted type) — "may drive an output".

### 2.8 `A -> ()` is not a sink

`unit_codomain_collapse : ∀ f g : α → Unit, f = g` (funext);
`consumers_indistinguishable`.  A pure total function into the unit has one
inhabitant up to extensionality; two "consumers" of `A` are the same
function, so the type cannot say which physical output receives `A`.
`MEv` has no effect component (`eval_independent_of_drives`).  Physical
consumption remains Phase 6: `OutputId`, `DriveWF`, `SingleDriver`,
`CompleteOutputs` — the receiver is named by the edge, the value delivered is
the driver's, of type `A`.  Design result: **do not add `A -> ()`**.

### 2.9 Behavior semantics vs realization

| behavior semantics (kernel) | realization (outside) |
|---|---|
| environment-provided inputs `I d t` | sensor reads, ADC, buses |
| pure internal computation `Ev`/`MEv` | generated core, allocator, bounds |
| output obligations `DriveWF`, `CompleteOutputs`, `PhysicalOutput` | GPIO/PWM, device I/O, platform adapter |

Nothing in this phase names a device; the unit domain adds no realization
vocabulary.

## 3. Verdicts

| candidate | verdict | evidence |
|---|---|---|
| Unit in canonical interface notation | KEEP (surface/interface normalization) | `CTy`, `elim_canonical`, `canonicalOfKernel_encode` |
| Unit kernel type | REMOVE | `elim unit = none`; `delay_not_under_binder` |
| Unit runtime value | REMOVE | no term former; `refForms_agree` |
| Source semantic kind | REMOVE / derive | `Source` is a realization state; `resolved_not_source` |
| Source surface role | KEEP in surface | `SimulationInput`, `source_value` |
| `A -> ()` as physical sink | REMOVE | `consumers_indistinguishable` |
| `OutputId` / drive boundary | KEEP | `driver_is_unit_domain`, Phase 6 |

## 4. Answers

- **Q1** Yes: `() -> B` is a conservative interface normalization; the kernel obligation, evaluation and clock judgments are those of `B` (`zero_input_obligation`, `refForms_agree`, `Clocked.refForms`), and the encoding is inverse (`decode_encode`, `elim_canonical`).
- **Q2** No kernel unit type: it would have no term (`elim unit = none`) and would forbid memory (`delay_not_under_binder`).
- **Q3** Yes: the unique argument is erased above the kernel; the reference's value is independent of the local environment (`declRef_env_irrelevant`).
- **Q4** Yes — typing (`lams_typed`), evaluation (`same_tick_same_value`), clocks (`Clocked.refForms`).
- **Q5** No: the source role is `realizationOf d = none`; a resolved `() -> A` never reads `I` (`resolved_not_source`).
- **Q6** No: all pure total `A -> 1` are equal (`consumers_indistinguishable`).
- **Q7** Yes: the drive edge names the receiver and delivers a value of type `A` (`driver_is_unit_domain`, Phase 6 theorems).
- **Q8** Yes: the kernel is inputs + pure computation + output obligations; the unit domain adds no realization vocabulary (§2.9).

## 5. Production guidance

- ISS-0014 can be closed by this phase; the correspondence row for ADR-0029 moves from *engineering choice* to *formally proved* (interface) / *transcribed* (kernel encoding).
- Keep `Ty::Unit` out of Core, representations and values, as now; the formal `CTy` is the record that it is an interface type.
- `Signature::is_unit_domain` is `UnitDomain`; the simulation-input predicate is `SimulationInput`.  Both are derived, and the formal model agrees that no kind is needed.
- `()` in output position: production refuses it; the formal `elim` gives `(A -> ())` the value `arr A ?` only if `unit` had a kernel type, which it does not — the refusal is the right presentation of `elim unit = none`.
- Do not add `A -> ()`; a "consumer" is a drive edge.
