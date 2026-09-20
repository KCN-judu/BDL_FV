---
kind: note
phase: 14
area: surface
date: 2026-09-20
status: current
---

# Output realization by device encoders — the output-side dual of Source provision

For the production repository and for a reader who will not open the Lean:
how a behaviour-level output stays independent of whether the machine realizes
it through PWM, a GPIO level, an I²C frame or a UART packet, and what the
formal development proved about the construction that keeps it so. It
summarises the
[Phase 14 report](../reports/phase-14-output-realization-by-device-encoders.md),
`BDL/Surface/OutputRealization.lean` and
`BDL/Experiments/OutputRealizationExamples.lean`, and the decisions FVD-0131 …
FVD-0138.

## 1. The question and the answer

A behaviour drives a logical output `o` — `OutputId`, `accepts : Ty`, `clock`
(Phase 6) — with a declaration `d` of exactly the accepted type; the design says
nothing about pins, protocols or duty cycles. PRP-0001 asked how a Source is
provisioned by a device; the dual asks how an output is _realized_ by one.

The answer has three stages and one asymmetry:

| Stage                       | Input side (Phase 13)                                     | Output side (Phase 14)                                                       |
| --------------------------- | --------------------------------------------------------- | ---------------------------------------------------------------------------- |
| behaviour design            | `Source s : () -> C`                                      | logical output `o accepts C`, driver `d : C`                                 |
| deployment / validation     | choose `R_in`, a pure transducer `R_in -> Rep(C)`, fit    | choose `R_out`, a pure encoder `Rep(C) -> R_out`, fit; board requirements    |
| lowering / machine          | `r : R_in` read from the environment; `s := mk C (tr r)` | `e := encode (rep d)` at `R_out`; machine sink `p` accepts `R_out`; `e -> p` |
| what changes in the design  | `s` goes from unresolved to realized; the Source role moves to `r` | **nothing**: `o`, `d`, `β d = o` and every declaration are unchanged; `e` and `p` are added downstream |
| the boundary relation       | induced input (environment → behaviour)                   | `RawCommand` (behaviour → machine)                                           |
| the central theorem         | transparency, both directions, under an induced input     | correspondence, directional: `raw trace = transfer ∘ abstract trace`         |
| exactness                   | needs a joint section; deployment restricts               | not required; quantization and saturation are admitted                       |

The asymmetry is the result: Source provision _realizes a declaration_ and
changes environment assumptions; output realization _adds downstream structure
only_ and does not feed evaluation. Behaviour meaning is independent of the
mechanism because the mechanism is downstream of everything the behaviour can
observe.

## 2. What is proved

All on `propext`/`Quot.sound`; theorem names in `BDL/Surface/OutputRealization.lean`.

- **Ontology.** `OutputId`/`OutputSpec`/`DriveWF`/`SingleDriver` are unchanged
  and are read as the _logical output_: semantic intent, terminal, physically
  realized by deployment. No device kind in `OutputSpec`; no concept implies a
  protocol (FVD-0131).
- **The encoder** `Encoder = ⟨rep, raw, encode, transfer, …, computes⟩`: pure
  (`Expr.Pure`), typed `rep -> raw` in the empty design under `Grant.none`
  (`Encoder.WF`), consuming sem-free data and producing sem-free data. Purity
  is necessary: a typed term with `delay` inside encodes the same value
  differently at different ticks (`exEFG`, the Phase-13 `exD` shape). The
  encoder constructs no concept (`encoder_constructs_nothing`), and the
  encoder declaration, typed at `raw`, has no grant at all
  (`encoder_decl_no_grant`); it reads the driver through `rep`, which needs
  none (FVD-0133).
- **Fitting** `EFits Θ accepts E` (`Θ c = some rep` at `sem c`; `τ = rep` at a
  data type) is decidable; `exEFG` executes the misfits.
- **The specification (Model B)** `RawCommand S Δ I Ω β R t w`: sink `p`
  receives `transfer (unwrap v)` where `v` is what `o` carries
  (`PhysicalOutput`). A relation on the unchanged design; a function of the
  tick under `SingleDriver` (`RawCommand.det`). This is the machine boundary;
  no `R -> ()` term, no effect (FVD-0134).
- **The lowering (Model C)** `lowerΔ`, `lowerΩ`, `lowerβ`, `lowerΚ`:
  `behavior_unchanged` (the environment is literally the same off `e`),
  `lower_transparent` (every pre-existing term evaluates identically under the
  _same_ input), `lower_physicalOutput_unchanged` (every logical output carries
  the same value), `lower_envRefines`, `lower_outputEnv_extends`,
  `lower_driveWF`, `lower_singleDriver` (Phase 6's first binding),
  `lower_completeOutputs`, `lower_wf`, `lower_causal` (one edge `e -> d`),
  `lower_wellClocked` (`e` in the output's clock; no device clock) — FVD-0132.
- **Correspondence** `lower_correspondence`:
  `PhysicalOutput Δ' p t w ↔ RawCommand Δ R t w` — the lowered design's machine
  sink carries exactly the specified command, tick by tick in the output's
  clock; `output_value_typed` discharges its typing hypothesis from Phase 5's
  totality.
- **Platform independence** `two_realizations_same_behavior`: two realizations
  of one design evaluate every pre-existing term alike; `exH` executes it
  (PWM duty 102 vs I²C `(42, 40)` for the same light at 40 %). Independent
  realizations commute exactly (`lower_comm`).
- **Model A refuted** `retarget_breaks_driveWF`: retargeting `o.accepts` to
  the command type breaks the existing drive edge (executed `exI`).
- **Validation** `Admissible Θ accepts H P := EFits ∧ solve H P.requirements`
  gives a fit and a valid assignment (`admissible_satisfiable`); `exH_admissible`
  admits both the PWM and the I²C profile for the light on the Nano and
  refuses the PWM profile for the relay — FVD-0137.
- **Lossiness**: no injectivity, exactness or round-trip is required; 4-bit
  PWM sends duty 6 for 40 % and 41 % and the realization is valid
  (`exB_quantized`) — FVD-0135.
- **Structured commands** need no record type: the H-bridge encodes
  `(forward?, magnitude)` to `(duty, direction)` with the kernel's pairs
  (`exD_hbridge`).

## 3. What is not established

Stateful output adapters (slew, dithering, batching, hysteresis); a device
clock different from the output clock (the explicit `sync` variant; the carrier
frequency as configuration); atomic multi-value frames; the codegen half
(raw command trace → generated backend call); commitments on outputs —
FVI-0022. The singleton realization is primitive by decision (FVD-0136), not by
a theorem that many-to-one is never needed.

## 4. Verdicts

Logical output / `DriveWF` / `SingleDriver`: KEEP IN KERNEL. Encoder, device
profile, the lowering: KEEP IN DEPLOYMENT CONSTRUCTION. Hardware requirements:
MOVE TO VALIDATION. The physical effect and `RawCommand`: MOVE TO
MACHINE/BACKEND. Effectful `R -> ()`, device kind in `OutputSpec`, injectivity:
REMOVE. Many-to-one lowering, device clock, stateful adapters: DEFER.

## 5. Production guidance

What exists at `7a800bc` (read from the code, not the prose):

- `bdl-model` `PhysicalOutput { id, accepts: SemanticId, clock, required }` —
  the logical output, at a concept; `DeviceBinding { kind: DeviceKind, output:
  Option<OutputId>, fixed_pins }` associates a device _kind_ (PwmChannel,
  DigitalOutput, HBridgeChannel, I2cSensor, QuadratureEncoder, Uart) with an
  output; `bdl-hardware::devices` turns the kind into requirements and the
  solver allocates board resources (ADR-0015). The kind is deployment data,
  never on the output — this is FVD-0131 already.
- `bdl-lower` plans one `OutputPlan { slot, id, driver, ty: spec.accepts }`
  per validated edge; the generated core produces
  `Outputs { output_n: Option<T> }` at the _driver's_ type and the host bridge
  converts to `DynValue`; `docs/spec/runtime-semantics.md` says the output
  adapter commits them. **No encoder exists**: the value reaching the adapter
  is the concept's representation, and the PWM/GPIO/I²C conversion would be
  the adapter's, unchecked.

What this investigation reinterprets: the device _kind_ is the requirements
half of a device profile; its other half — the encoder `Rep(C) -> R_out` and
the raw command type — is missing, exactly as the transducer was missing on the
Source side (PRP-0001).

What a future production change would need (_design recommendation_, each its
own ADR):

1. A device catalogue entry gains `consumes { representation, encoder, raw }`
   beside its requirements; `DeviceBinding.output` is the realization's `o`.
2. `analyze_deployment` checks `EFits` (in product words: "this device takes a
   duty cycle; Light carries a Brightness, represented as a level") and the
   encoder's purity, separately from allocation.
3. `bdl-lower` inserts the encoder declaration and the machine sink
   (`lowerΔ`/`lowerΩ`/`lowerβ`) so that the generated `Outputs` slot for the
   device carries `raw`, not the representation; the differential tests compare
   the lowered core's raw outputs against `transfer` of the reference
   evaluator's logical outputs (`lower_correspondence` is the oracle).
4. The adapter consumes raw commands only — the boundary `RawCommand`; it never
   sees a concept.
5. Studio: the Deploy page shows, per logical output, the device, the raw
   command type and the encoder; the canvas and the inspector's _Produces_ row
   do not change — the mechanism is not design information.

Nothing here is implemented; the correspondence page records the phase as
_not consumed_.
