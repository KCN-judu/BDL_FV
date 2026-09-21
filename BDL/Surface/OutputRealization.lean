import BDL.Surface.Provision
import BDL.Validation.Hardware

/-!
# Phase 14 — Output realization by device encoders (the dual of Phase 13)

A behaviour drives a *logical* output `o` — `OutputId`, `accepts : Ty`,
`clock` (Phase 6) — with a declaration `d` of exactly the accepted type.
Nothing in the design says whether the product moves that value to the
world through PWM, a GPIO level, an I²C frame or a UART packet.  This
module keeps it that way: the behaviour fixes the semantic intent `C`,
*deployment* chooses a raw command type `raw` and an **encoder**
`rep(C) -> raw`, *validation* checks the encoder fits and the board can
carry the device, *lowering* inserts the encoder as an ordinary
declaration driving a fresh machine sink, and only the backend performs
the effect.  No `Ty`, `Expr`, typing, grant, clock or evaluation rule is
added; no effectful `R -> ()` exists (Phase 12 `consumers_indistinguishable`).

## What is defined

* `Encoder` — `rep`, `raw`, the pure term `encode : rep -> raw`, its transfer
  function on values, and `computes`.  `Encoder.WF Θ` types it in the empty
  design under `Grant.none`.  `EFits Θ accepts E`: the encoder consumes the
  accepted concept's representation (or the accepted data type).
* `Realization` — the logical output `o`, its driver `d`, a fresh machine
  sink `p` and a fresh encoder declaration `e`, and the encoder.
* **Model B, the specification**: `RawCommand` — the command *specified*
  for realization `R` at tick `t`: `transfer` of what the logical output `o`
  carries (`PhysicalOutput`), stated on the *unchanged* design.  The machine
  sink `p` does not occur in it; that `p` carries exactly this command in
  the lowered design is the theorem `lower_correspondence`, not the
  definition.  The machine boundary is this relation, not a term.
* **Model C, the lowering**: `lowerΔ`/`lowerΩ`/`lowerβ`/`lowerΚ` — `e :=
  encode (rep d)` at `raw`, `p` accepts `raw` in `o`'s clock, `e` drives
  `p`; `o`, `d`, `β d = o` and every other declaration are untouched.
* **Model A** (retarget `o.accepts` to `raw`) is refuted:
  `retarget_breaks_driveWF`.

## Theorems (all on `propext`/`Quot.sound`)

`behavior_unchanged` (the behaviour environment is literally the same off
`e`), `lower_transparent` (every pre-existing term evaluates alike),
`lower_physicalOutput_unchanged` (every logical output carries the same
value), `lower_envRefines`, `lower_driveWF`, `lower_singleDriver`,
`lower_completeOutputs`, `lower_wf`, `lower_causal`, `lower_wellClocked`,
`lower_correspondence` (the machine sink's value in the lowered design is
exactly the specified raw command: `raw trace = transfer ∘ abstract trace`),
`output_value_typed` (the abstract value is a typed representation value in
a well-formed causal design), `encoder_constructs_nothing` /
`encoder_decl_no_grant` (the nominality boundary),
`two_realizations_same_behavior` (the formal side of platform independence:
the same evaluation of every pre-existing term under the theorem's
freshness and input hypotheses — nothing about a compiler, a backend or a
board), `lower_comm`, `Admissible` (well-typed encoder + fit + solvable
requirements; `FitsAndAllocates` is the strictly weaker predicate without
the typing, kept only to show the gap: `admissible_needs_wf`).
-/

namespace BDL.OutputRealization
open BDL BDL.Reactive BDL.Clock BDL.Output BDL.UnitDomain BDL.Provision BDL.Hardware

/-! ## Encoders -/

/-- A device **encoder**: what the deployment chooses for one logical
    output.  It consumes the accepted concept's *representation* `rep`
    (sem-free data — an encoder observes, it never constructs a concept)
    and produces the machine command `raw` (sem-free data — what a backend
    sink accepts).  `encode` is the BDL term the compiler lowers, pure
    (no `declRef`, `delay`, `sync`): a stateless device transfer.
    `transfer` is the same function on values — the data sheet — and
    `computes` ties the two on every representation value; it is what lets
    the raw command trace be *named* without evaluating the term. -/
structure Encoder where
  rep : Ty
  raw : Ty
  encode : Expr
  transfer : Value → Value
  rep_semFree : rep.SemFree
  rep_data : rep.Data
  raw_semFree : raw.SemFree
  raw_data : raw.Data
  encode_pure : encode.Pure
  computes : ∀ v, TyVal rep v → Transduces encode v (transfer v)

/-- Typed in the empty design under no grant: `rep -> raw`.  Not part of
    the structure: an `Encoder` value may carry a term of another type
    (`computes` only relates the term to `transfer`), which is why
    `Admissible` demands `WF` explicitly. -/
def Encoder.WF (Θ : ConceptEnv) (E : Encoder) : Prop :=
  HasType Θ DeclEnv.empty Grant.none [] E.encode (.arr E.rep E.raw)

instance (Θ : ConceptEnv) (E : Encoder) : Decidable (E.WF Θ) :=
  decidable_of_iff (infer Θ DeclEnv.empty Grant.none [] E.encode = some (.arr E.rep E.raw))
    ⟨infer_sound, infer_complete⟩

/-- `EFits Θ accepts E`: at `sem c` the encoder consumes `c`'s
    representation; at a data type the types coincide.  Decidable. -/
def EFits (Θ : ConceptEnv) (accepts : Ty) (E : Encoder) : Prop :=
  match accepts with
  | .sem c => Θ c = some E.rep
  | τ => τ = E.rep

instance (Θ : ConceptEnv) (accepts : Ty) (E : Encoder) : Decidable (EFits Θ accepts E) := by
  unfold EFits; cases accepts <;> exact inferInstance

/-- A term typed in the empty design references no declaration. -/
theorem refFree_of_empty_typed {Θ : ConceptEnv} {G : Grant} {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : HasType Θ DeclEnv.empty G Γ e τ) : e.RefFree := by
  unfold Expr.RefFree
  cases hr : e.refs with
  | nil => rfl
  | cons d _ =>
    obtain ⟨τ', hτ⟩ := h.refs_declared d (by rw [hr]; exact List.mem_cons_self)
    simp [DeclEnv.tyView, DeclEnv.empty] at hτ

theorem Encoder.WF_refFree {Θ : ConceptEnv} {E : Encoder} (h : E.WF Θ) : E.encode.RefFree :=
  refFree_of_empty_typed h

/-- **The nominality boundary, encoder side**: a well-formed encoder
    constructs no concept — it is typed under `Grant.none`. -/
theorem encoder_constructs_nothing {Θ : ConceptEnv} {E : Encoder} (h : E.WF Θ) :
    ∀ c, ¬ E.encode.constructs c :=
  fun c hc => h.constructs_granted c hc

/-- A sem-free data type grants nothing: the encoder *declaration*, typed at
    `raw`, is realized under the empty grant. -/
theorem grant_of_semFree_data {τ : Ty} (hs : τ.SemFree) (hd : τ.Data) : ∀ s, ¬ Grant.of τ s := by
  intro s h
  cases τ <;> simp [Grant.of, Ty.grant] at h <;> first | exact hs | exact hd

theorem encoder_decl_no_grant (E : Encoder) : ∀ s, ¬ Grant.of E.raw s :=
  grant_of_semFree_data E.raw_semFree E.raw_data

/-! ## Realizations -/

/-- One realization: the logical output `o` and its driver `d` (both
    pre-existing), the fresh machine sink `p`, the fresh encoder
    declaration `e`, and the encoder. -/
structure Realization where
  o : OutputId
  d : DeclId
  p : OutputId
  e : DeclId
  E : Encoder

/-- What the encoder declaration computes: the encoder applied to the
    driver's *representation* (through `rep`, which needs no grant) at a
    semantic output, or to the driver's value at a data output. -/
def encoderBody (accepts : Ty) (encode : Expr) (d : DeclId) : Expr :=
  match accepts with
  | .sem _ => .app encode (.rep (.declRef d))
  | _ => .app encode (.declRef d)

/-! ### Model B — the specification (nothing changes) -/

/-- **The raw command specified for realization `R` at tick `t`**: the
    encoder's transfer applied to what the logical output `o` carries.  A
    relation on the *unchanged* design in which the machine sink `p` does
    not occur — it says what the command *is*, not who receives it; that the
    lowered design's `p` carries exactly this value is `lower_correspondence`.
    The backend that consumes the command is outside the semantics.  This
    relation — not an `R -> ()` term — is the machine boundary. -/
def RawCommand (S : Sched) (Δ : DeclEnv) (I : Input) (Ω : OutputEnv) (β : DriveEnv) (R : Realization)
    (t : Nat) (w : Value) : Prop :=
  ∃ spec v, Ω R.o = some spec ∧ PhysicalOutput S Δ I Ω β R.o t v ∧ w = R.E.transfer (unwrapAt spec.accepts v)

/-- The command is a function of the tick when the logical output is. -/
theorem RawCommand.det {S : Sched} {Δ : DeclEnv} {I : Input} {Ω : OutputEnv} {β : DriveEnv} {R : Realization}
    (hs : SingleDriver β) {t : Nat} {w₁ w₂ : Value}
    (h₁ : RawCommand S Δ I Ω β R t w₁) (h₂ : RawCommand S Δ I Ω β R t w₂) : w₁ = w₂ := by
  obtain ⟨spec₁, v₁, hΩ₁, hv₁, rfl⟩ := h₁
  obtain ⟨spec₂, v₂, hΩ₂, hv₂, rfl⟩ := h₂
  rw [hΩ₁] at hΩ₂; cases hΩ₂
  rw [single_driver_output_deterministic hs hv₁ hv₂]

/-! ### Model C — the lowering -/

def lowerΔ (Δ : DeclEnv) (R : Realization) (spec : OutputSpec) : DeclEnv :=
  Δ.update ⟨R.e, ⟨R.E.raw, []⟩, some (encoderBody spec.accepts R.E.encode R.d)⟩

def lowerΩ (Ω : OutputEnv) (R : Realization) (spec : OutputSpec) : OutputEnv :=
  fun q => if q = R.p then some ⟨R.E.raw, spec.clock⟩ else Ω q

def lowerβ (β : DriveEnv) (R : Realization) : DriveEnv := β.bind R.e R.p

def lowerΚ (Κ : ClockEnv) (R : Realization) (spec : OutputSpec) : ClockEnv :=
  fun x => if x = R.e then some spec.clock else Κ x

/-- Preconditions: the output exists with `spec`, `d` drives it in a
    well-formed edge, `e` and `p` are fresh, the encoder fits and is well
    typed. -/
structure WF (Θ : ConceptEnv) (Δ : DeclEnv) (Ω : OutputEnv) (β : DriveEnv) (Κ : ClockEnv)
    (R : Realization) (spec : OutputSpec) : Prop where
  spec_of : Ω R.o = some spec
  drives : β R.d = some R.o
  driver_ty : Δ.tyView R.d = some spec.accepts
  driver_clock : Κ R.d = some spec.clock
  e_fresh : Δ R.e = none
  p_fresh : Ω R.p = none
  fits : EFits Θ spec.accepts R.E
  enc_wf : R.E.WF Θ

/-- The driver's clock and type are what `DriveWF` gives. -/
theorem WF.of_driveWF {Θ : ConceptEnv} {Δ : DeclEnv} {Ω : OutputEnv} {β : DriveEnv} {Κ : ClockEnv}
    (hw : DriveWF Ω Κ Δ β) {R : Realization} {spec : OutputSpec} (hΩ : Ω R.o = some spec)
    (hβ : β R.d = some R.o) (he : Δ R.e = none) (hp : Ω R.p = none) (hf : EFits Θ spec.accepts R.E)
    (hE : R.E.WF Θ) : WF Θ Δ Ω β Κ R spec := by
  obtain ⟨spec', hΩ', hty, hck⟩ := hw R.d R.o hβ
  rw [hΩ] at hΩ'; cases hΩ'
  exact ⟨hΩ, hβ, hty, hck, he, hp, hf, hE⟩

section Basic
variable {Θ : ConceptEnv} {Δ : DeclEnv} {Ω : OutputEnv} {β : DriveEnv} {Κ : ClockEnv}
  {R : Realization} {spec : OutputSpec}

theorem WF.d_ne_e (wf : WF Θ Δ Ω β Κ R spec) : R.d ≠ R.e := by
  intro h; have := wf.driver_ty; rw [h] at this; simp [DeclEnv.tyView, wf.e_fresh] at this

theorem WF.o_ne_p (wf : WF Θ Δ Ω β Κ R spec) : R.o ≠ R.p := by
  intro h; have := wf.spec_of; rw [h, wf.p_fresh] at this; exact nomatch this

/-- **`behavior_unchanged`**: off the fresh encoder identity the behaviour
    environment *is* the original — not observationally, literally. -/
theorem behavior_unchanged {x : DeclId} (hx : x ≠ R.e) : lowerΔ Δ R spec x = Δ x :=
  Δ.update_other _ hx

theorem lowerΔ_e : lowerΔ Δ R spec R.e = some ⟨R.e, ⟨R.E.raw, []⟩, some (encoderBody spec.accepts R.E.encode R.d)⟩ :=
  Δ.update_self _

theorem lowerΔ_tyView_e : (lowerΔ Δ R spec).tyView R.e = some R.E.raw := by
  simp [DeclEnv.tyView, lowerΔ_e]

theorem lowerΔ_tyView {x : DeclId} (hx : x ≠ R.e) : (lowerΔ Δ R spec).tyView x = Δ.tyView x := by
  simp [DeclEnv.tyView, behavior_unchanged hx]

theorem lowerΔ_realizationOf_e :
    (lowerΔ Δ R spec).realizationOf R.e = some (encoderBody spec.accepts R.E.encode R.d) := by
  simp [DeclEnv.realizationOf, lowerΔ_e]

theorem lowerΔ_realizationOf {x : DeclId} (hx : x ≠ R.e) :
    (lowerΔ Δ R spec).realizationOf x = Δ.realizationOf x := by
  simp [DeclEnv.realizationOf, behavior_unchanged hx]

theorem lowerΩ_p : lowerΩ Ω R spec R.p = some ⟨R.E.raw, spec.clock⟩ := by simp [lowerΩ]
theorem lowerΩ_other {q : OutputId} (hq : q ≠ R.p) : lowerΩ Ω R spec q = Ω q := by simp [lowerΩ, hq]
theorem lowerβ_e : lowerβ β R R.e = some R.p := by simp [lowerβ, DriveEnv.bind]
theorem lowerβ_other {x : DeclId} (hx : x ≠ R.e) : lowerβ β R x = β x := by simp [lowerβ, DriveEnv.bind, hx]
theorem lowerΚ_e : lowerΚ Κ R spec R.e = some spec.clock := by simp [lowerΚ]
theorem lowerΚ_other {x : DeclId} (hx : x ≠ R.e) : lowerΚ Κ R spec x = Κ x := by simp [lowerΚ, hx]

theorem encoderBody_refs (accepts : Ty) {encode : Expr} (hp : encode.Pure) (d : DeclId) :
    (encoderBody accepts encode d).refs = [d] := by
  cases accepts <;> simp [encoderBody, Expr.refs, Expr.Pure.refs_nil hp]

theorem encoderBody_instRefs (accepts : Ty) {encode : Expr} (hp : encode.Pure) (d : DeclId) :
    (encoderBody accepts encode d).instRefs = [d] := by
  cases accepts <;> simp [encoderBody, Expr.instRefs, Expr.Pure.instRefs_nil hp]

end Basic

/-! ## The behaviour is unchanged -/

section Behaviour
variable {Θ : ConceptEnv} {Δ : DeclEnv} {Ω : OutputEnv} {β : DriveEnv} {Κ : ClockEnv}
  {R : Realization} {spec : OutputSpec} {S : Sched} {I : Input}

/-- **`lower_transparent`**: every term that does not mention the fresh
    encoder identity evaluates identically in the abstract and the lowered
    design, under the *same* input — no induced input exists on the output
    side, because outputs do not feed evaluation.  Hypotheses: no
    realization of `Δ` mentions `e` (true of every globally well-typed
    design) and the local environment avoids `e`. -/
theorem lower_transparent (nm : NoMention Δ R.e) (hI : ∀ d t, Avoids R.e (I d t))
    {c : ClockId} {t : Nat} {ρ : List Value} {ex : Expr} {v : Value}
    (he : R.e ∉ ex.refs) (hρ : ∀ w ∈ ρ, Avoids R.e w) :
    MEv S Δ I c t ρ ex v ↔ MEv S (lowerΔ Δ R spec) I c t ρ ex v := by
  constructor
  · intro h
    refine (simulate R.e ?_ ?_ h he hρ).1
    · intro x hx body hb; exact Or.inl ⟨by rw [lowerΔ_realizationOf hx]; exact hb, nm x body hb⟩
    · intro x hx hn c t
      exact ⟨.refInput (by rw [lowerΔ_realizationOf hx]; exact hn), hI x t⟩
  · intro h
    refine (simulate R.e ?_ ?_ h he hρ).1
    · intro x hx body hb
      rw [lowerΔ_realizationOf hx] at hb
      exact Or.inl ⟨hb, nm x body hb⟩
    · intro x hx hn c t
      rw [lowerΔ_realizationOf hx] at hn
      exact ⟨.refInput hn, hI x t⟩

/-- Every declaration of the abstract design is observed identically. -/
theorem lower_decl_transparent (nm : NoMention Δ R.e) (hI : ∀ d t, Avoids R.e (I d t))
    {x : DeclId} (hx : x ≠ R.e) {c : ClockId} {t : Nat} {v : Value} :
    MEv S Δ I c t [] (.declRef x) v ↔ MEv S (lowerΔ Δ R spec) I c t [] (.declRef x) v :=
  lower_transparent nm hI (by simp [Expr.refs]; exact fun h => hx h.symm) (fun _ h => by simp at h)

/-- **`lower_physicalOutput_unchanged`**: every logical output — `o`
    included — carries in the lowered design exactly what it carried
    before.  The realization adds the machine sink `p`; it changes no
    logical output. -/
theorem lower_physicalOutput_unchanged (wf : WF Θ Δ Ω β Κ R spec) (hw : DriveWF Ω Κ Δ β) (nm : NoMention Δ R.e)
    (hI : ∀ d t, Avoids R.e (I d t)) {q : OutputId} (hq : q ≠ R.p) {t : Nat} {v : Value} :
    PhysicalOutput S Δ I Ω β q t v ↔ PhysicalOutput S (lowerΔ Δ R spec) I (lowerΩ Ω R spec) (lowerβ β R) q t v := by
  unfold PhysicalOutput
  constructor
  · rintro ⟨d, sp, hb, hΩ, he⟩
    have hd : d ≠ R.e := by
      intro h; subst h
      obtain ⟨_, _, hty, _⟩ := hw _ _ hb
      simp [DeclEnv.tyView, wf.e_fresh] at hty
    exact ⟨d, sp, by rw [lowerβ_other hd]; exact hb, by rw [lowerΩ_other hq]; exact hΩ,
      (lower_decl_transparent nm hI hd).mp he⟩
  · rintro ⟨d, sp, hb, hΩ, he⟩
    have hd : d ≠ R.e := by
      intro h; subst h; rw [lowerβ_e] at hb; cases hb; exact hq rfl
    rw [lowerβ_other hd] at hb
    rw [lowerΩ_other hq] at hΩ
    exact ⟨d, sp, hb, hΩ, (lower_decl_transparent nm hI hd).mpr he⟩

end Behaviour

/-! ## Structure of the lowered design -/

section Structure
variable {Θ : ConceptEnv} {Δ : DeclEnv} {Ω : OutputEnv} {β : DriveEnv} {Κ : ClockEnv}
  {R : Realization} {spec : OutputSpec}

/-- A fresh identity drives nothing in a well-formed drive environment. -/
theorem WF.e_unbound (wf : WF Θ Δ Ω β Κ R spec) (hw : DriveWF Ω Κ Δ β) : β R.e = none := by
  cases h : β R.e with
  | none => rfl
  | some o =>
    obtain ⟨_, _, hty, _⟩ := hw _ _ h
    simp [DeclEnv.tyView, wf.e_fresh] at hty

/-- A fresh sink is driven by nothing in a well-formed drive environment. -/
theorem WF.p_undriven (wf : WF Θ Δ Ω β Κ R spec) (hw : DriveWF Ω Κ Δ β) : ¬ Driven β R.p := by
  rintro ⟨d, hd⟩
  obtain ⟨sp, hΩ, _, _⟩ := hw d _ hd
  rw [wf.p_fresh] at hΩ; exact nomatch hΩ

theorem WF.o_ne_p' (wf : WF Θ Δ Ω β Κ R spec) {q : OutputId} {sp : OutputSpec} (h : Ω q = some sp) : q ≠ R.p := by
  intro e; rw [e, wf.p_fresh] at h; exact nomatch h

/-- **`lower_envRefines`**: the lowering adds one declaration; every
    pre-existing declaration is unchanged. -/
theorem lower_envRefines (wf : WF Θ Δ Ω β Κ R spec) : EnvRefines Δ (lowerΔ Δ R spec) := by
  intro x h hx
  have hxe : x ≠ R.e := by intro e; rw [e, wf.e_fresh] at hx; exact nomatch hx
  exact ⟨h, by rw [behavior_unchanged hxe]; exact hx, DeclLeq.refl h⟩

/-- The output environment is extended, never rewritten: `o` keeps its
    `accepts` and clock. -/
theorem lower_outputEnv_extends (wf : WF Θ Δ Ω β Κ R spec) {q : OutputId} {sp : OutputSpec} (h : Ω q = some sp) :
    lowerΩ Ω R spec q = some sp := by
  rw [lowerΩ_other (wf.o_ne_p' h)]; exact h

/-- **`lower_singleDriver`**: binding the fresh encoder to the fresh sink is
    the first binding of Phase 6 — a refinement of the drive edges that
    preserves single-driver.  The logical output `o` keeps its one driver
    `d`; the machine sink `p` gets its one driver `e`.  Nothing about pins. -/
theorem lower_singleDriver (wf : WF Θ Δ Ω β Κ R spec) (hw : DriveWF Ω Κ Δ β) (hs : SingleDriver β) :
    DriveRefines β (lowerβ β R) ∧ SingleDriver (lowerβ β R) :=
  first_output_binding_is_monotone hs (wf.e_unbound hw) (wf.p_undriven hw)

/-- **`lower_driveWF`**: the new edge `e → p` is well formed (type `raw`,
    clock `spec.clock`), and every old edge stays well formed. -/
theorem lower_driveWF (wf : WF Θ Δ Ω β Κ R spec) (hw : DriveWF Ω Κ Δ β) :
    DriveWF (lowerΩ Ω R spec) (lowerΚ Κ R spec) (lowerΔ Δ R spec) (lowerβ β R) := by
  intro x o hb
  by_cases hx : x = R.e
  · subst hx
    rw [lowerβ_e] at hb; cases hb
    exact ⟨⟨R.E.raw, spec.clock⟩, lowerΩ_p, lowerΔ_tyView_e, lowerΚ_e⟩
  · rw [lowerβ_other hx] at hb
    obtain ⟨sp, hΩ, hty, hck⟩ := hw x o hb
    exact ⟨sp, lower_outputEnv_extends wf hΩ, by rw [lowerΔ_tyView hx]; exact hty,
      by rw [lowerΚ_other hx]; exact hck⟩

/-- Completeness: the required sinks plus the machine sink are driven. -/
theorem lower_completeOutputs (wf : WF Θ Δ Ω β Κ R spec) (hw : DriveWF Ω Κ Δ β) {req : List OutputId}
    (hc : CompleteOutputs β req) : CompleteOutputs (lowerβ β R) (R.p :: req) := by
  intro o ho
  rcases List.mem_cons.mp ho with rfl | ho
  · exact ⟨R.e, lowerβ_e⟩
  · obtain ⟨d, hd⟩ := hc o ho
    have hde : d ≠ R.e := by intro e; rw [e, wf.e_unbound hw] at hd; exact nomatch hd
    exact ⟨d, by rw [lowerβ_other hde]; exact hd⟩

/-- The encoder declaration is typed at `raw` under its own (empty) grant:
    the encoder term is moved from the empty design (reference-free), the
    driver is read through `rep` at a semantic output — no `mk` anywhere. -/
theorem encoderBody_typed (wf : WF Θ Δ Ω β Κ R spec) :
    HasType Θ (lowerΔ Δ R spec) (Grant.of R.E.raw) [] (encoderBody spec.accepts R.E.encode R.d) R.E.raw := by
  have htr : HasType Θ (lowerΔ Δ R spec) (Grant.of R.E.raw) [] R.E.encode (.arr R.E.rep R.E.raw) :=
    (wf.enc_wf.refFree_env_irrelevant (Encoder.WF_refFree wf.enc_wf)).mono_grant (fun _ hf => hf.elim)
  have hd : HasType Θ (lowerΔ Δ R spec) (Grant.of R.E.raw) [] (.declRef R.d) spec.accepts :=
    .declRef (by rw [lowerΔ_tyView wf.d_ne_e]; exact wf.driver_ty)
  have hfit := wf.fits
  unfold EFits at hfit
  generalize hτ : spec.accepts = τ at *
  cases τ with
  | sem c =>
    simp only [encoderBody]
    exact .app htr (.rep hfit hd)
  | bool | nat | arr _ _ | q _ | opt _ | list _ | prod _ _ =>
    simp only at hfit
    rw [hfit] at hd
    simp only [encoderBody]
    exact .app htr hd

/-- **`lower_wf`**: the lowered design is globally well formed.  The encoder
    declaration carries no commitments; every other declaration's evidence
    survives the refinement. -/
theorem lower_wf {ev : Evidence} (mono : ev.Monotone) (g : GlobalWF ev Θ Δ) (wf : WF Θ Δ Ω β Κ R spec) :
    GlobalWF ev Θ (lowerΔ Δ R spec) := by
  have er := lower_envRefines wf
  intro x h hx
  by_cases hxe : x = R.e
  · subst hxe
    rw [lowerΔ_e] at hx
    rw [← Option.some.inj hx]
    refine ⟨rfl, fun b hb => ?_⟩
    simp only at hb
    rw [← Option.some.inj hb]
    exact ⟨encoderBody_typed wf, fun _ hp => by simp at hp⟩
  · rw [behavior_unchanged hxe] at hx
    exact ⟨g.stored_id hx, (g.wellFormed hx).of_envRefines mono er⟩

/-- **`lower_causal`**: the instantaneous graph gains the edge `e → d` and
    nothing else — purity keeps the encoder term edge-free.  `e` sits on top. -/
theorem lower_causal (wf : WF Θ Δ Ω β Κ R spec) (nm : NoMention Δ R.e) (hc : Causal Δ) :
    Causal (lowerΔ Δ R spec) := by
  obtain ⟨rank, Rk, hR, hedge⟩ := hc
  refine ⟨fun x => if x = R.e then Rk else rank x, Rk + 1, ?_, ?_⟩
  · intro x; by_cases h : x = R.e
    · simp [h]
    · simp [h]; exact Nat.lt_succ_of_lt (hR x)
  · intro a b hab
    obtain ⟨body, hb, hmem⟩ := InstDependsOn.iff.mp hab
    by_cases hae : a = R.e
    · subst hae
      rw [lowerΔ_realizationOf_e] at hb
      cases hb
      rw [encoderBody_instRefs _ R.E.encode_pure] at hmem
      simp at hmem; subst hmem
      simp [wf.d_ne_e]; exact hR R.d
    · rw [lowerΔ_realizationOf hae] at hb
      have hbe : b ≠ R.e := fun e => nm a body hb (e ▸ InstDependsOn.toDependsOn.instRefs_sub hmem)
      simp [hae, hbe]
      exact hedge a b (InstDependsOn.iff.mpr ⟨body, hb, hmem⟩)

/-- **`lower_wellClocked`**: the encoder is read in the output's clock, which
    is the driver's clock (`DriveWF`); the encoder term is clocked
    everywhere; no other realization mentions `e`.  No device clock exists. -/
theorem lower_wellClocked (wf : WF Θ Δ Ω β Κ R spec) (nm : NoMention Δ R.e) (hw : WellClocked Κ Δ) :
    WellClocked (lowerΚ Κ R spec) (lowerΔ Δ R spec) := by
  intro x body hb
  by_cases hxe : x = R.e
  · subst hxe
    rw [lowerΔ_realizationOf_e] at hb
    cases hb
    rw [lowerΚ_e]
    have hd : lowerΚ Κ R spec R.d = some spec.clock := by rw [lowerΚ_other wf.d_ne_e]; exact wf.driver_clock
    unfold Clocked
    cases spec.accepts <;>
      simp [encoderBody, clockedB, Expr.Pure.clocked (lowerΚ Κ R spec) (some spec.clock) R.E.encode_pure, hd]
  · rw [lowerΔ_realizationOf hxe] at hb
    rw [lowerΚ_other hxe]
    have := hw x body hb
    unfold Clocked at *
    rw [← clockedB_congr (Κ := Κ) (Κ' := lowerΚ Κ R spec)]
    · exact this
    · intro y hy
      have hye : y ≠ R.e := fun e => nm x body hb (e ▸ hy)
      simp [lowerΚ, hye]

end Structure

/-! ## Correspondence: the machine sink carries the specified command -/

section Correspondence
variable {Θ : ConceptEnv} {Δ : DeclEnv} {Ω : OutputEnv} {β : DriveEnv} {Κ : ClockEnv}
  {R : Realization} {spec : OutputSpec} {S : Sched} {I : Input}

theorem unwrapAt_wrapAt (τ : Ty) (w : Value) : unwrapAt τ (wrapAt τ w) = w := by
  cases τ <;> simp [wrapAt, unwrapAt]

/-- The logical output carries typed representation values (wrapped at a
    semantic output).  Derivable in a well-formed causal design
    (`output_value_typed`); stated as a hypothesis so the correspondence
    theorem does not carry the totality hypotheses. -/
def OutputTyped (S : Sched) (Δ : DeclEnv) (I : Input) (Ω : OutputEnv) (β : DriveEnv) (R : Realization)
    (spec : OutputSpec) : Prop :=
  ∀ t v, PhysicalOutput S Δ I Ω β R.o t v → ∃ w, v = wrapAt spec.accepts w ∧ TyVal R.E.rep w

/-- The encoder declaration's value from the driver's value. -/
theorem encoder_value (_wf : WF Θ Δ Ω β Κ R spec) {t : Nat} {w : Value} (hw : TyVal R.E.rep w)
    (hd : MEv S (lowerΔ Δ R spec) I spec.clock t [] (.declRef R.d) (wrapAt spec.accepts w)) :
    MEv S (lowerΔ Δ R spec) I spec.clock t [] (encoderBody spec.accepts R.E.encode R.d) (R.E.transfer w) := by
  have hnc : w.NoClo := TyVal.noClo R.E.rep_data hw
  generalize hτ : spec.accepts = τ at *
  cases τ with
  | sem c => exact (R.E.computes w hw).mev R.E.encode_pure hnc (.rep hd)
  | bool | nat | arr _ _ | q _ | opt _ | list _ | prod _ _ => exact (R.E.computes w hw).mev R.E.encode_pure hnc hd

/-- **`lower_correspondence`** (the central theorem): the machine sink `p`
    carries, in the lowered design, exactly the raw command the
    specification assigns to the abstract design —
    `raw trace = transfer ∘ abstract trace`, tick by tick in the output's
    clock.  Directional by nature: `p` is downstream of `o`; nothing flows
    back.  Hypotheses: the realization is well formed over a well-formed
    single-driver drive environment, the design mentions no `e`, inputs
    avoid `e`, and the logical output carries typed values. -/
theorem lower_correspondence (wf : WF Θ Δ Ω β Κ R spec) (hw : DriveWF Ω Κ Δ β) (hs : SingleDriver β)
    (nm : NoMention Δ R.e) (hI : ∀ d t, Avoids R.e (I d t)) (hty : OutputTyped S Δ I Ω β R spec)
    {t : Nat} {w : Value} :
    PhysicalOutput S (lowerΔ Δ R spec) I (lowerΩ Ω R spec) (lowerβ β R) R.p t w ↔ RawCommand S Δ I Ω β R t w := by
  constructor
  · rintro ⟨d', sp, hb, hΩ, he⟩
    have hd' : d' = R.e := by
      cases hne : decide (d' = R.e) with
      | true => exact of_decide_eq_true hne
      | false =>
        have hne' : d' ≠ R.e := of_decide_eq_false hne
        rw [lowerβ_other hne'] at hb
        exact (wf.p_undriven hw ⟨d', hb⟩).elim
    subst hd'
    rw [lowerΩ_p] at hΩ; cases hΩ
    -- the encoder's derivation contains the driver's value
    cases he with
    | refRealized hr hbody =>
      rw [lowerΔ_realizationOf_e] at hr; cases hr
      have hdv : ∃ v, MEv S (lowerΔ Δ R spec) I spec.clock t [] (.declRef R.d) v := by
        cases hacc : spec.accepts <;> simp only [encoderBody, hacc] at hbody <;>
          (cases hbody with
            | appClo _ ha _ => first | (cases ha with | rep hv => exact ⟨_, hv⟩) | exact ⟨_, ha⟩
            | appPrim _ ha => first | (cases ha with | rep hv => exact ⟨_, hv⟩) | exact ⟨_, ha⟩)
      obtain ⟨v, hv⟩ := hdv
      have hvΔ : MEv S Δ I spec.clock t [] (.declRef R.d) v := (lower_decl_transparent nm hI wf.d_ne_e).mpr hv
      have hpo : PhysicalOutput S Δ I Ω β R.o t v := ⟨R.d, spec, wf.drives, wf.spec_of, hvΔ⟩
      obtain ⟨w', hvw, hw'⟩ := hty t v hpo
      subst hvw
      have hcanon := encoder_value (S := S) (I := I) wf hw' hv
      have := hbody.det hcanon
      subst this
      exact ⟨spec, _, wf.spec_of, hpo, by rw [unwrapAt_wrapAt]⟩
    | refInput hn => rw [lowerΔ_realizationOf_e] at hn; exact nomatch hn
  · rintro ⟨sp, v, hΩ, hpo, rfl⟩
    rw [wf.spec_of] at hΩ; cases hΩ
    obtain ⟨d', sp', hb, hΩ', he⟩ := hpo
    have hd' : d' = R.d := hs d' R.d R.o hb wf.drives
    subst hd'
    rw [wf.spec_of] at hΩ'; cases hΩ'
    obtain ⟨w', hvw, hw'⟩ := hty t v ⟨R.d, spec, wf.drives, wf.spec_of, he⟩
    subst hvw
    have hv' := (lower_decl_transparent (spec := spec) nm hI wf.d_ne_e).mp he
    have hcanon := encoder_value (S := S) (I := I) wf hw' hv'
    refine ⟨R.e, ⟨R.E.raw, spec.clock⟩, lowerβ_e, lowerΩ_p, ?_⟩
    rw [unwrapAt_wrapAt]
    exact .refRealized lowerΔ_realizationOf_e hcanon

/-- **`output_value_typed`**: in a causal, globally well-formed design with
    typed inputs the logical output carries typed representation values —
    the hypothesis of the correspondence theorem is discharged by Phase 5's
    totality. -/
theorem output_value_typed {ev : Evidence} (hΘ : Θ.WF) (hc : Causal Δ) (g : GlobalWF ev Θ Δ)
    (hI : ∀ d τ c t, Δ.tyView d = some τ → Δ.realizationOf d = none → Red Θ (MApply S Δ I c t) τ (I d t))
    (wf : WF Θ Δ Ω β Κ R spec) (hs : SingleDriver β) : OutputTyped S Δ I Ω β R spec := by
  intro t v hpo
  obtain ⟨d', sp, hb, hΩ, he⟩ := hpo
  have hd' : d' = R.d := hs d' R.d R.o hb wf.drives
  subst hd'
  rw [wf.spec_of] at hΩ; cases hΩ
  obtain ⟨v', hv', hred⟩ := multi_domain_total hΘ hc g hI wf.driver_ty spec.clock t
  have := he.det hv'
  subst this
  have hfit := wf.fits
  unfold EFits at hfit
  generalize hτ : spec.accepts = τ at *
  cases τ with
  | sem c =>
    obtain ⟨w, rfl, hw⟩ := hred
    exact ⟨w, rfl, RedSF_data R.E.rep_data (hw _ hfit)⟩
  | bool | nat | arr _ _ | q _ | opt _ | list _ | prod _ _ =>
    simp only at hfit
    rw [hfit] at hred
    exact ⟨v, rfl, RedSF_data R.E.rep_data ((Red_semFree R.E.rep_semFree).mp hred)⟩

end Correspondence

/-! ## Platform independence, commutation, the refuted model -/

section Independence
variable {Θ : ConceptEnv} {Δ : DeclEnv} {Ω : OutputEnv} {β : DriveEnv} {Κ : ClockEnv} {S : Sched} {I : Input}

/-- **`two_realizations_same_behavior`**: two realizations of the same
    abstract design — PWM and I²C, say — evaluate every pre-existing term
    identically.  Behaviour meaning is independent of the physical
    mechanism; only the raw command traces differ (`lower_correspondence`
    with the two transfers). -/
theorem two_realizations_same_behavior {R₁ R₂ : Realization} {spec₁ spec₂ : OutputSpec}
    (nm₁ : NoMention Δ R₁.e) (nm₂ : NoMention Δ R₂.e)
    (hI₁ : ∀ d t, Avoids R₁.e (I d t)) (hI₂ : ∀ d t, Avoids R₂.e (I d t))
    {c : ClockId} {t : Nat} {ρ : List Value} {ex : Expr} {v : Value}
    (he₁ : R₁.e ∉ ex.refs) (he₂ : R₂.e ∉ ex.refs) (hρ₁ : ∀ w ∈ ρ, Avoids R₁.e w) (hρ₂ : ∀ w ∈ ρ, Avoids R₂.e w) :
    MEv S (lowerΔ Δ R₁ spec₁) I c t ρ ex v ↔ MEv S (lowerΔ Δ R₂ spec₂) I c t ρ ex v := by
  rw [← lower_transparent nm₁ hI₁ he₁ hρ₁, ← lower_transparent nm₂ hI₂ he₂ hρ₂]

theorem DeclEnv.update_comm {Δ : DeclEnv} {h₁ h₂ : DesignDecl} (hne : h₁.id ≠ h₂.id) :
    (Δ.update h₁).update h₂ = (Δ.update h₂).update h₁ := by
  funext x
  unfold DeclEnv.update
  by_cases e₁ : x = h₁.id <;> by_cases e₂ : x = h₂.id <;> simp [e₁, e₂] <;>
    (intro h; first | exact absurd h hne | exact absurd h.symm hne)

/-- **`lower_comm`**: independent realizations commute exactly — distinct
    encoder identities and machine sinks, and neither encoder is the
    other's driver.  Two logical outputs realized by two devices, in
    either order, give one lowered design. -/
theorem lower_comm {R₁ R₂ : Realization} {spec₁ spec₂ : OutputSpec}
    (he : R₁.e ≠ R₂.e) (hp : R₁.p ≠ R₂.p) :
    lowerΔ (lowerΔ Δ R₁ spec₁) R₂ spec₂ = lowerΔ (lowerΔ Δ R₂ spec₂) R₁ spec₁ ∧
    lowerΩ (lowerΩ Ω R₁ spec₁) R₂ spec₂ = lowerΩ (lowerΩ Ω R₂ spec₂) R₁ spec₁ ∧
    lowerβ (lowerβ β R₁) R₂ = lowerβ (lowerβ β R₂) R₁ ∧
    lowerΚ (lowerΚ Κ R₁ spec₁) R₂ spec₂ = lowerΚ (lowerΚ Κ R₂ spec₂) R₁ spec₁ := by
  refine ⟨DeclEnv.update_comm he, ?_, ?_, ?_⟩
  · funext q; unfold lowerΩ
    by_cases e₁ : q = R₁.p <;> by_cases e₂ : q = R₂.p <;> simp [e₁, e₂] <;>
      (intro h; first | exact absurd h hp | exact absurd h.symm hp)
  · funext x; unfold lowerβ DriveEnv.bind
    by_cases e₁ : x = R₁.e <;> by_cases e₂ : x = R₂.e <;> simp [e₁, e₂] <;>
      (intro h; first | exact absurd h he | exact absurd h.symm he)
  · funext x; unfold lowerΚ
    by_cases e₁ : x = R₁.e <;> by_cases e₂ : x = R₂.e <;> simp [e₁, e₂] <;>
      (intro h; first | exact absurd h he | exact absurd h.symm he)

/-- **Model A refuted** (`retarget_breaks_driveWF`): retargeting the
    logical output's accepted type to the raw command type breaks the
    existing drive edge — the driver is typed at the concept, not at the
    command — so the abstract design would have to be re-driven and its
    output meaning lost.  `rebinding_invalidates_design` (Phase 6) already
    calls this an edit. -/
theorem retarget_breaks_driveWF {o : OutputId} {d : DeclId} {c : ConceptId} {raw : Ty} {clock : ClockId}
    (hβ : β d = some o) (hty : Δ.tyView d = some (.sem c)) (hraw : raw.SemFree) :
    ¬ DriveWF (fun q => if q = o then some ⟨raw, clock⟩ else Ω q) Κ Δ β := by
  intro hw
  obtain ⟨sp, hΩ, hty', _⟩ := hw d o hβ
  simp at hΩ; subst hΩ
  rw [hty] at hty'
  simp only [Option.some.injEq] at hty'
  rw [← hty'] at hraw
  exact hraw

end Independence

/-! ## The raw declaration and the machine sink, canonically -/

/-- The encoder declaration's canonical type is `() -> raw` (Phase 12); the
    machine sink accepts `raw` in the output's clock. -/
theorem lowered_interfaces {Δ : DeclEnv} {Ω : OutputEnv} {R : Realization} {spec : OutputSpec} :
    (lowerΔ Δ R spec).tyView R.e = some R.E.raw ∧ canonicalOfKernel R.E.raw = .arr .unit (.k R.E.raw) ∧
    lowerΩ Ω R spec R.p = some ⟨R.E.raw, spec.clock⟩ :=
  ⟨lowerΔ_tyView_e, canonicalOfKernel_encode ⟨[], R.E.raw⟩ (Ty.Data.not_arr R.E.raw_data), lowerΩ_p⟩

/-! ## Validation: fit plus a solvable board -/

/-- A device profile for an output: the encoder (behaviour-to-command
    semantics) and the hardware requirements (deployment validation) —
    two judgments, never one. -/
structure DeviceOutputProfile where
  E : Encoder
  requirements : Requirements

/-- The narrow predicate: the encoder *fits* the accepted type and the
    board can carry the requirements.  It does **not** say the encoder is
    typed `rep -> raw`; it is kept only to state the gap
    (`admissible_needs_wf`, `exJ`). -/
def FitsAndAllocates (Θ : ConceptEnv) (accepts : Ty) (H : Hardware) (P : DeviceOutputProfile) : Prop :=
  EFits Θ accepts P.E ∧ (solve H P.requirements).isSome

instance (Θ : ConceptEnv) (accepts : Ty) (H : Hardware) (P : DeviceOutputProfile) :
    Decidable (FitsAndAllocates Θ accepts H P) :=
  inferInstanceAs (Decidable (EFits Θ accepts P.E ∧ (solve H P.requirements).isSome))

/-- **Deployment admissibility** of a profile for an output on a board: the
    encoder is well typed `rep -> raw` under no grant, it fits the accepted
    type, and the board can carry the device's requirements.  Three
    judgments — typing, fit, allocation — none of which sees the others.
    Nothing electrical, thermal or timing-related is claimed. -/
def Admissible (Θ : ConceptEnv) (accepts : Ty) (H : Hardware) (P : DeviceOutputProfile) : Prop :=
  P.E.WF Θ ∧ EFits Θ accepts P.E ∧ (solve H P.requirements).isSome

instance (Θ : ConceptEnv) (accepts : Ty) (H : Hardware) (P : DeviceOutputProfile) :
    Decidable (Admissible Θ accepts H P) :=
  inferInstanceAs (Decidable (P.E.WF Θ ∧ EFits Θ accepts P.E ∧ (solve H P.requirements).isSome))

theorem Admissible.toFitsAndAllocates {Θ : ConceptEnv} {accepts : Ty} {H : Hardware} {P : DeviceOutputProfile}
    (h : Admissible Θ accepts H P) : FitsAndAllocates Θ accepts H P :=
  ⟨h.2.1, h.2.2⟩

/-- **`admissible_needs_wf`**: the narrow predicate plus the encoder's
    typing is admissibility, and nothing less is — a profile whose encoder
    fits and whose device allocates but whose term is not `rep -> raw` is
    not admissible (`exJ` exhibits one). -/
theorem admissible_needs_wf {Θ : ConceptEnv} {accepts : Ty} {H : Hardware} {P : DeviceOutputProfile} :
    Admissible Θ accepts H P ↔ P.E.WF Θ ∧ FitsAndAllocates Θ accepts H P :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- Admissibility gives a well-typed encoder, a fit and a valid assignment
    (Phase 7's soundness); it says nothing electrical. -/
theorem admissible_satisfiable {Θ : ConceptEnv} {accepts : Ty} {H : Hardware} {P : DeviceOutputProfile}
    (h : Admissible Θ accepts H P) :
    P.E.WF Θ ∧ EFits Θ accepts P.E ∧ HardwareSatisfiable H P.requirements :=
  ⟨h.1, h.2.1, satisfiable_iff_solve.mpr h.2.2⟩

/-- An admissible profile's encoder is the `WF` that `Realization.WF`
    demands: admissibility is what a realization may be built from. -/
theorem Admissible.enc_wf {Θ : ConceptEnv} {accepts : Ty} {H : Hardware} {P : DeviceOutputProfile}
    (h : Admissible Θ accepts H P) : P.E.WF Θ := h.1

end BDL.OutputRealization
