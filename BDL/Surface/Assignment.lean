import BDL.Surface.DeviceClock

/-!
# Phase 16 — Assignment: catalogue entries, contracts, and the deployment-only `assign`

The output side (Phase 14) realizes a logical output by a device profile —
an encoder and requirements; the input side (Phase 13) provisions a Source
by a device profile — a raw type and channels.  Both profiles were written
as Lean values inside the development.  This module asks what changes when
a profile is *supplied from outside* — a package — and what a deployment
operation

    assign MotorPosition using emm_v5.position_feedback
    assign MotorOutput   using emm_v5.position_control

is in the model.  The answers:

* **A catalogue entry is a profile with an origin**, and the origin is data
  the semantics never reads: every construction factors through the
  profile (`OutputEntry.realization`, `assignSource`), so two entries with
  one profile give one lowered design, one raw command relation and one
  adapter operation relation (`assign_indistinguishable`,
  `assignSource_origin_irrelevant`).  A builtin and a packaged profile are
  told apart by nothing downstream of the contract.
* **The contract is the existing one.**  Output: the encoder typed
  `rep -> raw` under no grant and fitting the accepted type
  (`OutputContract`); input: the channel typed `raw -> rep` under no grant
  and fitting the Source (`InputContract` — exactly what `Provision.WF`
  asks per target).  Neither mentions a board.
* **Semantic admissibility and deployment feasibility are separate**:
  `Admissible ↔ OutputContract ∧ Feasible` (`admissible_iff`), and a
  profile may satisfy the contract on a board that cannot carry it
  (`CommunicationExamples.exQ_contract_not_feasible`).
* **`assign` is deployment-only**: `assignOutput` *is* `lowerΔ` and
  `assignSource` *is* `provision` — nothing off the fresh identities
  changes (`assignOutput_behavior_unchanged`), every pre-existing term
  evaluates alike (`assignOutput_transparent`, `assignSource_transparent`),
  and the assigned design is checked by the unchanged judgments
  (`assignOutput_checked`).
* **Non-interference, both sides.**  Output: `two_realizations_same_behavior`
  (Phase 14).  Input, new here: two providers whose induced Source traces
  coincide give the same evaluation of every term that mentions neither
  raw declaration (`two_providers_same_behavior`) and the same logical
  outputs (`two_providers_same_outputs`); "same trace" is `SameTrace`:
  the induced inputs agree off the two raw declarations, at every global
  tick — the raw readings themselves may carry any transport identity.
  With Phase 15's
  `two_policies_same_commands` these are the three instances of the
  **replacement-invariance criterion**: a carrier replaced under the same
  semantic trace changes no behaviour.
* **Packages extend realizability**: a larger catalogue realizes and
  provisions more (`realizable_mono`, `provisionable_mono`) and nothing
  else — no typing, evaluation, causality or clock rule takes a catalogue.
* **Two realizations of one output** — a paired axis on two motors —
  specify at each tick two commands that are the two transfers of *one*
  value (`paired_commands_of_one_value`); the frame that carries them is
  the backend's per-tick commit.

Not modelled: package resolution, versions, registries, signatures — the
profile is a value satisfying a contract, and how it arrived is engineering.
-/

namespace BDL.Assignment
open BDL BDL.Reactive BDL.Clock BDL.Output BDL.Provision BDL.OutputRealization BDL.Adapter BDL.Hardware

/-! ## Catalogue entries -/

/-- A package's identity — display data, never read by a judgment. -/
structure PackageId where
  n : Nat
  deriving DecidableEq, Repr

/-- Where a profile comes from: the toolchain's own registry or a package. -/
inductive Origin where
  | builtin
  | package (p : PackageId)
  deriving DecidableEq, Repr

/-- A catalogue entry that *provides*: a Phase-13 device profile (raw type,
    channels) with its origin. -/
structure InputEntry where
  origin : Origin
  profile : DeviceProfile

/-- A catalogue entry that *consumes*: a Phase-14 device profile (encoder,
    requirements) with its origin. -/
structure OutputEntry where
  origin : Origin
  profile : DeviceOutputProfile

/-- A catalogue: what a deployment may assign.  Builtin and packaged
    entries are one list. -/
structure Catalogue where
  inputs : List InputEntry
  outputs : List OutputEntry

/-! ## Contracts -/

/-- **Semantic admissibility** of an output profile for an accepted type:
    the encoder is typed `rep -> raw` under no grant and fits.  No board. -/
def OutputContract (Θ : ConceptEnv) (accepts : Ty) (P : DeviceOutputProfile) : Prop :=
  P.E.WF Θ ∧ EFits Θ accepts P.E

instance (Θ : ConceptEnv) (accepts : Ty) (P : DeviceOutputProfile) : Decidable (OutputContract Θ accepts P) :=
  inferInstanceAs (Decidable (P.E.WF Θ ∧ EFits Θ accepts P.E))

/-- **Deployment feasibility** of an output profile on a board: the
    requirements allocate.  No type. -/
def Feasible (H : Hardware) (P : DeviceOutputProfile) : Prop := (solve H P.requirements).isSome

instance (H : Hardware) (P : DeviceOutputProfile) : Decidable (Feasible H P) :=
  inferInstanceAs (Decidable ((solve H P.requirements).isSome))

/-- **`admissible_iff`**: Phase 14's admissibility is the conjunction of the
    two, and neither sees the other. -/
theorem admissible_iff {Θ : ConceptEnv} {accepts : Ty} {H : Hardware} {P : DeviceOutputProfile} :
    Admissible Θ accepts H P ↔ OutputContract Θ accepts P ∧ Feasible H P :=
  ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

/-- **Semantic admissibility** of a channel for a Source's type: the
    channel is typed `raw -> rep` under no grant and fits — exactly what
    `Provision.WF` asks of every target. -/
def InputContract (Θ : ConceptEnv) (τ : Ty) {raw : Ty} (ch : Channel raw) : Prop :=
  ch.WF Θ ∧ Fits Θ τ ch

/-- A well-formed provision's targets satisfy the contract. -/
theorem WF.contract {Θ : ConceptEnv} {Δ : DeclEnv} {raw : Ty} {P : Provision raw} (wf : WF Θ Δ P)
    {s : DeclId} {ch : Channel raw} (hc : P.chan s = some ch) :
    ∃ h, Δ s = some h ∧ h.realization = none ∧ InputContract Θ h.interface.expectedType ch := by
  obtain ⟨h, hs, hun, hfit, hty⟩ := wf.targets s ch hc
  exact ⟨h, hs, hun, hty, hfit⟩

/-- The singleton provision is well formed exactly from the contract and
    the freshness/type-shape facts (`WF.one`, restated). -/
theorem WF.one_of_contract {Θ : ConceptEnv} {Δ : DeclEnv} {raw : Ty} {r s : DeclId} {clock : Option ClockId}
    {ch : Channel raw} {h : DesignDecl} (hfresh : Δ r = none) (hsf : raw.SemFree) (hdata : raw.Data)
    (hs : Δ s = some h) (hun : h.realization = none) (hc : InputContract Θ h.interface.expectedType ch) :
    WF Θ Δ (Provision.one r s clock ch) :=
  WF.one hfresh hsf hdata hs hun hc.2 hc.1

/-! ## What a catalogue makes realizable -/

/-- An accepted type is realizable from a catalogue on a board when some
    entry is admissible for it. -/
def Realizable (Θ : ConceptEnv) (H : Hardware) (C : Catalogue) (accepts : Ty) : Prop :=
  ∃ en ∈ C.outputs, Admissible Θ accepts H en.profile

/-- A Source type is provisionable from a catalogue when some entry offers
    a channel satisfying the contract. -/
def Provisionable (Θ : ConceptEnv) (C : Catalogue) (τ : Ty) : Prop :=
  ∃ en ∈ C.inputs, ∃ ch ∈ en.profile.channels, InputContract Θ τ ch

/-- **`realizable_mono`**: a package that adds entries realizes more and
    unrealizes nothing. -/
theorem realizable_mono {Θ : ConceptEnv} {H : Hardware} {C C' : Catalogue} (h : ∀ en ∈ C.outputs, en ∈ C'.outputs)
    {accepts : Ty} : Realizable Θ H C accepts → Realizable Θ H C' accepts :=
  fun ⟨en, hen, ha⟩ => ⟨en, h en hen, ha⟩

theorem provisionable_mono {Θ : ConceptEnv} {C C' : Catalogue} (h : ∀ en ∈ C.inputs, en ∈ C'.inputs)
    {τ : Ty} : Provisionable Θ C τ → Provisionable Θ C' τ :=
  fun ⟨en, hen, ch, hch, hc⟩ => ⟨en, h en hen, ch, hch, hc⟩

/-! ## `assign` on the output side -/

/-- The realization an output assignment builds: the pre-existing logical
    output `o` and its driver `d`, the fresh machine sink `p` and encoder
    declaration `e`, and the entry's encoder.  A function of the profile. -/
def OutputEntry.realization (en : OutputEntry) (o : OutputId) (d : DeclId) (p : OutputId) (e : DeclId) :
    Realization :=
  ⟨o, d, p, e, en.profile.E⟩

/-- **`assign o using en`** — the lowered design.  It *is* Phase 14's
    lowering; the operation adds no construction of its own. -/
def assignOutput (Δ : DeclEnv) (en : OutputEntry) (o : OutputId) (d : DeclId) (p : OutputId) (e : DeclId)
    (spec : OutputSpec) : DeclEnv :=
  lowerΔ Δ (en.realization o d p e) spec

/-- **The origin is not read**: two entries with one profile build one
    realization. -/
theorem OutputEntry.realization_of_profile {en₁ en₂ : OutputEntry} (h : en₁.profile = en₂.profile)
    (o : OutputId) (d : DeclId) (p : OutputId) (e : DeclId) :
    en₁.realization o d p e = en₂.realization o d p e := by
  simp [OutputEntry.realization, h]

/-- **`assign_indistinguishable`** (builtin vs packaged): with one profile,
    the lowered design, output environment, drive environment and clock
    environment coincide, the raw command relation coincides, and every
    adapter's operation relation coincides.  Nothing downstream of the
    contract sees where the profile came from. -/
theorem assign_indistinguishable {Δ : DeclEnv} {Ω : OutputEnv} {β : DriveEnv} {Κ : ClockEnv}
    {en₁ en₂ : OutputEntry} (h : en₁.profile = en₂.profile)
    (o : OutputId) (d : DeclId) (p : OutputId) (e : DeclId) (spec : OutputSpec) :
    assignOutput Δ en₁ o d p e spec = assignOutput Δ en₂ o d p e spec ∧
    lowerΩ Ω (en₁.realization o d p e) spec = lowerΩ Ω (en₂.realization o d p e) spec ∧
    lowerβ β (en₁.realization o d p e) = lowerβ β (en₂.realization o d p e) ∧
    lowerΚ Κ (en₁.realization o d p e) spec = lowerΚ Κ (en₂.realization o d p e) spec ∧
    (∀ S I t w, RawCommand S Δ I Ω β (en₁.realization o d p e) t w ↔
      RawCommand S Δ I Ω β (en₂.realization o d p e) t w) ∧
    (∀ S I (P : Policy) t op, AdapterOp S Δ I Ω β (en₁.realization o d p e) spec P t op ↔
      AdapterOp S Δ I Ω β (en₂.realization o d p e) spec P t op) := by
  rw [assignOutput, assignOutput, OutputEntry.realization_of_profile h]
  exact ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl⟩

section AssignOutput
variable {Θ : ConceptEnv} {Δ : DeclEnv} {Ω : OutputEnv} {β : DriveEnv} {Κ : ClockEnv} {S : Sched} {I : Input}
  {en : OutputEntry} {o : OutputId} {d : DeclId} {p : OutputId} {e : DeclId} {spec : OutputSpec}

/-- **`assign` does not edit behaviour**: off the fresh encoder identity the
    design is literally the same (`behavior_unchanged`). -/
theorem assignOutput_behavior_unchanged {x : DeclId} (hx : x ≠ e) : assignOutput Δ en o d p e spec x = Δ x :=
  behavior_unchanged (R := en.realization o d p e) hx

/-- Every pre-existing term evaluates alike before and after the
    assignment (`lower_transparent`). -/
theorem assignOutput_transparent (nm : NoMention Δ e) (hI : ∀ x t, Avoids e (I x t))
    {c : ClockId} {t : Nat} {ρ : List Value} {ex : Expr} {v : Value}
    (he : e ∉ ex.refs) (hρ : ∀ w ∈ ρ, Avoids e w) :
    MEv S Δ I c t ρ ex v ↔ MEv S (assignOutput Δ en o d p e spec) I c t ρ ex v :=
  lower_transparent (R := en.realization o d p e) (spec := spec) nm hI he hρ

/-- The assigned design is accepted by the *unchanged* judgments — global
    well-formedness, causality, clocking, drive well-formedness and the
    single-driver invariant — under Phase 14's preconditions.  A catalogue
    entry brings a profile, not a rule. -/
theorem assignOutput_checked {ev : Evidence} (mono : ev.Monotone) (g : GlobalWF ev Θ Δ)
    (wf : WF Θ Δ Ω β Κ (en.realization o d p e) spec)
    (hc : Causal Δ) (hK : WellClocked Κ Δ) (hw : DriveWF Ω Κ Δ β) (hs : SingleDriver β) :
    GlobalWF ev Θ (assignOutput Δ en o d p e spec) ∧ Causal (assignOutput Δ en o d p e spec) ∧
    WellClocked (lowerΚ Κ (en.realization o d p e) spec) (assignOutput Δ en o d p e spec) ∧
    DriveWF (lowerΩ Ω (en.realization o d p e) spec) (lowerΚ Κ (en.realization o d p e) spec)
      (assignOutput Δ en o d p e spec) (lowerβ β (en.realization o d p e)) ∧
    SingleDriver (lowerβ β (en.realization o d p e)) :=
  have nm : NoMention Δ e := NoMention.of_globalWF g wf.e_fresh
  ⟨lower_wf mono g wf, lower_causal wf nm hc, lower_wellClocked wf nm hK, lower_driveWF wf hw,
   (lower_singleDriver wf hw hs).2⟩

end AssignOutput

/-! ## `assign` on the input side -/

/-- **`assign s using en.channel i`** — the provisioned design: Phase 13's
    singleton provision with the entry's `i`-th channel, or nothing when
    the entry has no such channel.  A function of the profile. -/
def assignSource (Δ : DeclEnv) (en : InputEntry) (i : Nat) (r s : DeclId) (clock : Option ClockId) :
    Option DeclEnv :=
  (en.profile.channels[i]?).map fun ch => provision Δ (Provision.one r s clock ch)

/-- **The origin is not read** on the input side either. -/
theorem assignSource_origin_irrelevant {Δ : DeclEnv} {en₁ en₂ : InputEntry} (h : en₁.profile = en₂.profile)
    (i : Nat) (r s : DeclId) (clock : Option ClockId) :
    assignSource Δ en₁ i r s clock = assignSource Δ en₂ i r s clock := by
  cases en₁; cases en₂; cases h; rfl

/-- **`assign` does not edit behaviour** on the input side: every term that
    does not mention the raw declaration evaluates alike under the induced
    input (`provisionOne_transparent`). -/
theorem assignSource_transparent {Θ : ConceptEnv} {Δ : DeclEnv} {S : Sched} {raw : Ty}
    {r s : DeclId} {clock : Option ClockId} {ch : Channel raw}
    (wf : WF Θ Δ (Provision.one r s clock ch)) (nm : NoMention Δ r) {I' : Input}
    (hI : RawInput (Provision.one r s clock ch) I')
    {c : ClockId} {t : Nat} {e : Expr} {v : Value} (he : r ∉ e.refs) :
    MEv S Δ (induced Δ (Provision.one r s clock ch) I') c t [] e v ↔
      MEv S (provision Δ (Provision.one r s clock ch)) I' c t [] e v :=
  provisionOne_transparent wf nm hI he

/-! ## Source-side non-interference -/

section Providers
variable {Θ : ConceptEnv} {Δ : DeclEnv} {S : Sched} {raw₁ raw₂ : Ty} {P₁ : Provision raw₁} {P₂ : Provision raw₂}

/-- The induced input avoids every identity: at a target it is the pure
    transfer of a closure-free raw value, elsewhere the closure-free raw
    input itself. -/
theorem induced_avoids {raw : Ty} {P : Provision raw} (wf : WF Θ Δ P) {I' : Input} (hI : RawInput P I')
    (r d : DeclId) (t : Nat) : Avoids r (induced Δ P I' d t) := by
  simp only [induced]
  split
  · rename_i ch τ _ _
    have hraw := hI.1 t
    have hv : (I' P.r t).NoClo := TyVal.noClo wf.raw_data hraw
    have hp : (ch.transfer (I' P.r t)).Pure := (ch.computes _ hraw).pure ch.tr_pure hv
    cases τ with
    | sem c => exact .sem (Avoids.of_pure hp)
    | bool | nat | arr _ _ | q _ | opt _ | list _ | prod _ _ => exact Avoids.of_pure hp
  · exact Avoids.of_noClo (hI.2 d t)

/-- **Same semantic Source trace**: the two induced inputs agree at every
    declaration other than the two raw ones, at every global tick.  The raw
    declarations themselves may carry anything — a sequence number, a
    frame id, a retry token — and no two raw types need be related. -/
def SameTrace {raw₁ raw₂ : Ty} (Δ : DeclEnv) (P₁ : Provision raw₁) (P₂ : Provision raw₂) (I₁ I₂ : Input) : Prop :=
  ∀ d t, d ≠ P₁.r → d ≠ P₂.r → induced Δ P₁ I₁ d t = induced Δ P₂ I₂ d t

theorem SameTrace.symm {I₁ I₂ : Input} (h : SameTrace Δ P₁ P₂ I₁ I₂) : SameTrace Δ P₂ P₁ I₂ I₁ :=
  fun d t h₂ h₁ => (h d t h₁ h₂).symm

/-- Under the same trace, the abstract design evaluates alike under either
    induced input — two applications of `input_congr`, one per raw
    identity. -/
theorem induced_congr (wf₁ : WF Θ Δ P₁) (wf₂ : WF Θ Δ P₂) (nm₁ : NoMention Δ P₁.r) (nm₂ : NoMention Δ P₂.r)
    {I₁ I₂ : Input} (hI₁ : RawInput P₁ I₁) (hI₂ : RawInput P₂ I₂) (same : SameTrace Δ P₁ P₂ I₁ I₂)
    {c : ClockId} {t : Nat} {ρ : List Value} {e : Expr} {v : Value}
    (he₁ : P₁.r ∉ e.refs) (he₂ : P₂.r ∉ e.refs)
    (hρ₁ : ∀ w ∈ ρ, Avoids P₁.r w) (hρ₂ : ∀ w ∈ ρ, Avoids P₂.r w)
    (h : MEv S Δ (induced Δ P₁ I₁) c t ρ e v) : MEv S Δ (induced Δ P₂ I₂) c t ρ e v := by
  let J : Input := fun d t => if d = P₁.r then induced Δ P₂ I₂ d t else induced Δ P₁ I₁ d t
  have h1 : MEv S Δ J c t ρ e v :=
    input_congr P₁.r nm₁ (fun d t hd => by simp [J, hd]) (fun d t _ _ => induced_avoids wf₁ hI₁ _ d t) he₁ hρ₁ h
  refine input_congr P₂.r nm₂ (I := J) (fun d t hd => ?_) (fun d t _ _ => ?_) he₂ hρ₂ h1
  · simp only [J]
    split
    · rename_i h'; rw [h']
    · exact same d t ‹_› hd
  · simp only [J]
    split
    · exact induced_avoids wf₂ hI₂ _ _ _
    · exact induced_avoids wf₁ hI₁ _ _ _

/-- **`two_providers_same_behavior`** — the input-side dual of
    `two_realizations_same_behavior`.  Two providers of the same abstract
    design — a CAN feedback frame and a simulated sensor, a TCP command
    stream and a USB one — whose raw inputs induce the same semantic
    Source trace (`SameTrace`) evaluate every term that mentions neither
    raw declaration to the same values.  Nothing about the two raw types,
    transfers or transport identities enters: a sequence number that the
    channel discards is not observable. -/
theorem two_providers_same_behavior (wf₁ : WF Θ Δ P₁) (wf₂ : WF Θ Δ P₂)
    (nm₁ : NoMention Δ P₁.r) (nm₂ : NoMention Δ P₂.r)
    {I₁ I₂ : Input} (hI₁ : RawInput P₁ I₁) (hI₂ : RawInput P₂ I₂) (same : SameTrace Δ P₁ P₂ I₁ I₂)
    {c : ClockId} {t : Nat} {ρ : List Value} {e : Expr} {v : Value}
    (he₁ : P₁.r ∉ e.refs) (he₂ : P₂.r ∉ e.refs)
    (hρ₁ : ∀ w ∈ ρ, Avoids P₁.r w) (hρ₂ : ∀ w ∈ ρ, Avoids P₂.r w) :
    MEv S (provision Δ P₁) I₁ c t ρ e v ↔ MEv S (provision Δ P₂) I₂ c t ρ e v := by
  rw [← provision_transparent wf₁ nm₁ hI₁ he₁ hρ₁, ← provision_transparent wf₂ nm₂ hI₂ he₂ hρ₂]
  exact ⟨induced_congr wf₁ wf₂ nm₁ nm₂ hI₁ hI₂ same he₁ he₂ hρ₁ hρ₂,
    induced_congr wf₂ wf₁ nm₂ nm₁ hI₂ hI₁ same.symm he₂ he₁ hρ₂ hρ₁⟩

/-- The same, at every logical output driven by the abstract design: the
    sinks see one trace. -/
theorem two_providers_same_outputs (wf₁ : WF Θ Δ P₁) (wf₂ : WF Θ Δ P₂)
    (nm₁ : NoMention Δ P₁.r) (nm₂ : NoMention Δ P₂.r)
    {I₁ I₂ : Input} (hI₁ : RawInput P₁ I₁) (hI₂ : RawInput P₂ I₂) (same : SameTrace Δ P₁ P₂ I₁ I₂)
    {Ω : OutputEnv} {β : DriveEnv} (hβ : ∀ d o, β d = some o → Δ d ≠ none) {o : OutputId} {t : Nat} {v : Value} :
    PhysicalOutput S (provision Δ P₁) I₁ Ω β o t v ↔ PhysicalOutput S (provision Δ P₂) I₂ Ω β o t v := by
  unfold PhysicalOutput
  constructor
  · rintro ⟨d, spec, hb, hΩ, he⟩
    refine ⟨d, spec, hb, hΩ, ?_⟩
    refine (two_providers_same_behavior wf₁ wf₂ nm₁ nm₂ hI₁ hI₂ same ?_ ?_ (fun _ h => by simp at h)
      (fun _ h => by simp at h)).mp he
    · simp [Expr.refs]; intro h; exact hβ d o hb (h ▸ wf₁.fresh)
    · simp [Expr.refs]; intro h; exact hβ d o hb (h ▸ wf₂.fresh)
  · rintro ⟨d, spec, hb, hΩ, he⟩
    refine ⟨d, spec, hb, hΩ, ?_⟩
    refine (two_providers_same_behavior wf₁ wf₂ nm₁ nm₂ hI₁ hI₂ same ?_ ?_ (fun _ h => by simp at h)
      (fun _ h => by simp at h)).mpr he
    · simp [Expr.refs]; intro h; exact hβ d o hb (h ▸ wf₁.fresh)
    · simp [Expr.refs]; intro h; exact hβ d o hb (h ▸ wf₂.fresh)

end Providers

/-! ## Two realizations of one output -/

/-- **`paired_commands_of_one_value`**: two realizations of one logical
    output — a Y axis on two motors — specify at each tick two commands
    that are the two encoders' transfers of *one* value, the value the
    output carries.  What the device protocol needs beyond the pair
    (prepare, prepare, commit) orders the backend's per-tick commit of the
    two operations; it is below `AdapterOp` and carries no information the
    pair does not. -/
theorem paired_commands_of_one_value {S : Sched} {Δ : DeclEnv} {I : Input} {Ω : OutputEnv} {β : DriveEnv}
    (hs : SingleDriver β) {R₁ R₂ : Realization} (ho : R₁.o = R₂.o) {t : Nat} {w₁ w₂ : Value}
    (h₁ : RawCommand S Δ I Ω β R₁ t w₁) (h₂ : RawCommand S Δ I Ω β R₂ t w₂) :
    ∃ spec v, Ω R₁.o = some spec ∧ PhysicalOutput S Δ I Ω β R₁.o t v ∧
      w₁ = R₁.E.transfer (unwrapAt spec.accepts v) ∧ w₂ = R₂.E.transfer (unwrapAt spec.accepts v) := by
  obtain ⟨spec₁, v₁, hΩ₁, hv₁, rfl⟩ := h₁
  obtain ⟨spec₂, v₂, hΩ₂, hv₂, rfl⟩ := h₂
  rw [← ho] at hΩ₂ hv₂
  rw [hΩ₁] at hΩ₂; cases hΩ₂
  exact ⟨spec₁, v₁, hΩ₁, hv₁, rfl, by rw [single_driver_output_deterministic hs hv₁ hv₂]⟩

end BDL.Assignment
