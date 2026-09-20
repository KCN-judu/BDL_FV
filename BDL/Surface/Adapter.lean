import BDL.Surface.OutputRealization

/-!
# Phase 15 — The adapter boundary: raw commands to abstract sink operations

Phase 14 ends at `RawCommand`: the command specified for a realization at
a tick.  Production (ADR-0037) now has a platform adapter that consumes
exactly those commands — `Tick.commands → adapter::apply → AdapterOp` —
with an explicit *boundary policy* (a finite duty in `0 ..= 255` is
applied, anything else is refused and the line holds; a driver that is
not due leaves the line as it is) and a host-recorded operation trace.
This module extends the formal model by that one boundary and no further:

* `Policy` — what the adapter makes of a raw command: an accepted
  machine-level value or a refusal.  `Policy.total` accepts everything;
  `duty8` is production's policy on the kernel's naturals (production's
  `f64` rounding is recorded outside the model, FVI-0023).
* `Op` — the abstract sink operation: `set m`, `refused`, `held`.  Data,
  not an effect: no `Expr`, no evaluation rule, nothing in `Core`.
* `AdapterOp` — the operation on the realization's sink at a global tick,
  defined over the *specification* `RawCommand` on the unchanged design
  and gated by the output's clock activation: `held` when the clock is
  not active, `set (P w)` or `refused` when it is.
* `Line` — the state of the physical line as a fold over the operations:
  the last accepted value, or the start value.  Reject-and-hold is a
  fact about this fold, not about the encoder.

## Theorems

`AdapterOp.det`, `adapter_of_sink` / `adapter_of_sink_iff` (the operation
is determined by the lowered design's machine sink — `lower_correspondence`
carried one step further), `adapter_downstream` (policies do not enter the
raw command, hence not the behaviour), `Line.det`, `line_last_accepted`,
`line_holds_on_refusal`, `line_holds_when_inactive`, `two_policies_same_commands`.
Not modelled: the HAL, the register, the electrical world (FVI-0023).
-/

namespace BDL.Adapter
open BDL BDL.Reactive BDL.Clock BDL.Output BDL.Provision BDL.OutputRealization

/-! ## Policies and operations -/

/-- A boundary policy: the adapter's reading of a raw command.  `none` is a
    refusal.  A policy is *not* an encoder: it lives below the raw command
    trace, in the adapter, and it may be partial. -/
structure Policy where
  accept : Value → Option Value

/-- Apply the command as it is. -/
def Policy.total : Policy := ⟨fun v => some v⟩

/-- Production's 8-bit duty policy on the kernel's naturals: a duty in
    `0 ..= 255` is applied as it is, anything else is refused.  (Production
    rounds a finite `f64` to the nearest whole duty, halves up, before this
    check; the kernel has no fraction to round.) -/
def duty8 : Policy :=
  ⟨fun v => match v with | .nat n => if n ≤ 255 then some (.nat n) else none | _ => none⟩

/-- A clamping policy, for comparison: an out-of-range duty is applied at
    the nearest end.  Production refused it (ADR-0037) because it hides that
    the design commanded what the profile did not promise; the model
    represents both and prefers neither. -/
def clamp8 : Policy :=
  ⟨fun v => match v with | .nat n => some (.nat (min n 255)) | _ => none⟩

/-- A level policy: a truth value is applied as written. -/
def level : Policy :=
  ⟨fun v => match v with | .bool b => some (.bool b) | _ => none⟩

/-- The abstract sink operation — production's `AdapterOp` as data. -/
inductive Op where
  | set (m : Value)   -- the sink was set to `m`
  | refused           -- the command was refused; the line holds
  | held              -- the driver was not due; the line holds
  deriving Repr

/-! ## The operation at a tick -/

/-- **The adapter's operation** on realization `R`'s sink at global tick
    `t`: nothing when the output's clock is not active; otherwise the
    policy's reading of the command specified at `t`.  A relation over the
    *unchanged* design: the adapter reads the raw command and nothing
    upstream of it. -/
inductive AdapterOp (S : Sched) (Δ : DeclEnv) (I : Input) (Ω : OutputEnv) (β : DriveEnv)
    (R : Realization) (spec : OutputSpec) (P : Policy) : Nat → Op → Prop where
  | held {t} : Ω R.o = some spec → S spec.clock t = false →
      AdapterOp S Δ I Ω β R spec P t .held
  | set {t w m} : Ω R.o = some spec → S spec.clock t = true →
      RawCommand S Δ I Ω β R t w → P.accept w = some m →
      AdapterOp S Δ I Ω β R spec P t (.set m)
  | refused {t w} : Ω R.o = some spec → S spec.clock t = true →
      RawCommand S Δ I Ω β R t w → P.accept w = none →
      AdapterOp S Δ I Ω β R spec P t .refused

section Ops
variable {S : Sched} {Δ : DeclEnv} {I : Input} {Ω : OutputEnv} {β : DriveEnv}
  {R : Realization} {spec : OutputSpec} {P : Policy}

/-- The operation is a function of the tick under single-driver. -/
theorem AdapterOp.det (hs : SingleDriver β) {t : Nat} {op₁ op₂ : Op}
    (h₁ : AdapterOp S Δ I Ω β R spec P t op₁) (h₂ : AdapterOp S Δ I Ω β R spec P t op₂) : op₁ = op₂ := by
  cases h₁ with
  | held _ ha =>
    cases h₂ with
    | held _ _ => rfl
    | set _ hb _ _ => rw [ha] at hb; exact nomatch hb
    | refused _ hb _ _ => rw [ha] at hb; exact nomatch hb
  | set _ ha hw hm =>
    cases h₂ with
    | held _ hb => rw [ha] at hb; exact nomatch hb
    | set _ _ hw' hm' => rw [RawCommand.det hs hw hw'] at hm; rw [hm] at hm'; cases hm'; rfl
    | refused _ _ hw' hm' => rw [RawCommand.det hs hw hw'] at hm; rw [hm] at hm'; exact nomatch hm'
  | refused _ ha hw hm =>
    cases h₂ with
    | held _ hb => rw [ha] at hb; exact nomatch hb
    | set _ _ hw' hm' => rw [RawCommand.det hs hw hw'] at hm; rw [hm] at hm'; exact nomatch hm'
    | refused _ _ _ _ => rfl

/-- **`adapter_downstream`**: the raw command does not depend on the policy
    — definitionally, `RawCommand` does not mention `P` — so no policy, and
    no refusal, reaches the behaviour.  Two adapters over one realization
    see one command trace. -/
theorem adapter_downstream (_P₁ _P₂ : Policy) {t : Nat} {w : Value} :
    RawCommand S Δ I Ω β R t w ↔ RawCommand S Δ I Ω β R t w := Iff.rfl

/-- **`adapter_of_sink`**: the operation is determined by what the lowered
    design's machine sink carries — `lower_correspondence` carried one step
    further.  What the adapter does at an active tick is the policy's
    reading of the value the fresh sink `p` holds in the lowered design. -/
theorem adapter_of_sink {Θ : ConceptEnv} {Κ : ClockEnv} (wf : WF Θ Δ Ω β Κ R spec) (hw : DriveWF Ω Κ Δ β)
    (hs : SingleDriver β) (nm : NoMention Δ R.e) (hI : ∀ d t, Avoids R.e (I d t))
    (hty : OutputTyped S Δ I Ω β R spec) {t : Nat} {w : Value}
    (hp : PhysicalOutput S (lowerΔ Δ R spec) I (lowerΩ Ω R spec) (lowerβ β R) R.p t w)
    (hact : S spec.clock t = true) :
    AdapterOp S Δ I Ω β R spec P t (match P.accept w with | some m => .set m | none => .refused) := by
  have hraw := (lower_correspondence wf hw hs nm hI hty).mp hp
  cases hm : P.accept w with
  | some m => exact .set wf.spec_of hact hraw hm
  | none => exact .refused wf.spec_of hact hraw hm

/-- The converse: an operation at an active tick names a command the
    lowered sink carries. -/
theorem sink_of_adapter {Θ : ConceptEnv} {Κ : ClockEnv} (wf : WF Θ Δ Ω β Κ R spec) (hw : DriveWF Ω Κ Δ β)
    (hs : SingleDriver β) (nm : NoMention Δ R.e) (hI : ∀ d t, Avoids R.e (I d t))
    (hty : OutputTyped S Δ I Ω β R spec) {t : Nat} {op : Op}
    (h : AdapterOp S Δ I Ω β R spec P t op) (hact : S spec.clock t = true) :
    ∃ w, PhysicalOutput S (lowerΔ Δ R spec) I (lowerΩ Ω R spec) (lowerβ β R) R.p t w ∧
      op = (match P.accept w with | some m => .set m | none => .refused) := by
  cases h with
  | held _ hb => rw [hact] at hb; exact nomatch hb
  | set _ _ hraw hm =>
    exact ⟨_, (lower_correspondence wf hw hs nm hI hty).mpr hraw, by rw [hm]⟩
  | refused _ _ hraw hm =>
    exact ⟨_, (lower_correspondence wf hw hs nm hI hty).mpr hraw, by rw [hm]⟩

/-- Two policies over one realization read one command trace; they differ
    only in the operation — never in the behaviour, never in the command. -/
theorem two_policies_same_commands (P₁ P₂ : Policy) {t : Nat} {w : Value}
    (h : RawCommand S Δ I Ω β R t w) (hact : S spec.clock t = true) (hΩ : Ω R.o = some spec) :
    AdapterOp S Δ I Ω β R spec P₁ t (match P₁.accept w with | some m => .set m | none => .refused) ∧
    AdapterOp S Δ I Ω β R spec P₂ t (match P₂.accept w with | some m => .set m | none => .refused) := by
  constructor
  · cases hm : P₁.accept w with
    | some m => exact .set hΩ hact h hm
    | none => exact .refused hΩ hact h hm
  · cases hm : P₂.accept w with
    | some m => exact .set hΩ hact h hm
    | none => exact .refused hΩ hact h hm

end Ops

/-! ## The line: reject-and-hold as a fold over operations -/

/-- The value the physical line carries after tick `t`: the start value
    until a command is accepted; the last accepted value thereafter; a
    refusal or an inactive tick changes nothing.  This is the only state at
    the boundary, and it lives in the adapter — below the realization,
    outside the behaviour. -/
inductive Line (S : Sched) (Δ : DeclEnv) (I : Input) (Ω : OutputEnv) (β : DriveEnv)
    (R : Realization) (spec : OutputSpec) (P : Policy) (start : Value) : Nat → Value → Prop where
  | set0 {m} : AdapterOp S Δ I Ω β R spec P 0 (.set m) → Line S Δ I Ω β R spec P start 0 m
  | hold0 {op} : AdapterOp S Δ I Ω β R spec P 0 op → (∀ m', op ≠ .set m') → Line S Δ I Ω β R spec P start 0 start
  | set {t m} : AdapterOp S Δ I Ω β R spec P (t + 1) (.set m) → Line S Δ I Ω β R spec P start (t + 1) m
  | hold {t op m} : AdapterOp S Δ I Ω β R spec P (t + 1) op → (∀ m', op ≠ .set m') →
      Line S Δ I Ω β R spec P start t m → Line S Δ I Ω β R spec P start (t + 1) m

section Lines
variable {S : Sched} {Δ : DeclEnv} {I : Input} {Ω : OutputEnv} {β : DriveEnv}
  {R : Realization} {spec : OutputSpec} {P : Policy} {start : Value}

theorem Line.det (hs : SingleDriver β) : ∀ {t : Nat} {m₁ m₂ : Value},
    Line S Δ I Ω β R spec P start t m₁ → Line S Δ I Ω β R spec P start t m₂ → m₁ = m₂
  | 0, m₁, m₂, h₁, h₂ => by
    cases h₁ with
    | set0 ha =>
      cases h₂ with
      | set0 hb => exact Op.set.inj (AdapterOp.det hs ha hb)
      | hold0 hb hne => exact absurd (AdapterOp.det hs hb ha) (hne _)
    | hold0 ha hne =>
      cases h₂ with
      | set0 hb => exact absurd (AdapterOp.det hs ha hb) (hne _)
      | hold0 _ _ => rfl
  | t + 1, m₁, m₂, h₁, h₂ => by
    cases h₁ with
    | set ha =>
      cases h₂ with
      | set hb => exact Op.set.inj (AdapterOp.det hs ha hb)
      | hold hb hne _ => exact absurd (AdapterOp.det hs hb ha) (hne _)
    | hold ha hne hl₁ =>
      cases h₂ with
      | set hb => exact absurd (AdapterOp.det hs ha hb) (hne _)
      | hold _ _ hl₂ => exact Line.det hs hl₁ hl₂

/-- **`line_holds_on_refusal`**: a refused command leaves the line where it
    was — the "hold" of reject-and-hold is a property of the fold, not of
    the encoder or the behaviour. -/
theorem line_holds_on_refusal {m : Value} {t' : Nat}
    (h : AdapterOp S Δ I Ω β R spec P (t' + 1) .refused) (hl : Line S Δ I Ω β R spec P start t' m) :
    Line S Δ I Ω β R spec P start (t' + 1) m :=
  .hold h (fun _ h => nomatch h) hl

/-- **`line_holds_when_inactive`**: a tick at which the output's clock is
    not active leaves the line where it was. -/
theorem line_holds_when_inactive {m : Value} {t' : Nat} (hΩ : Ω R.o = some spec)
    (hin : S spec.clock (t' + 1) = false) (hl : Line S Δ I Ω β R spec P start t' m) :
    Line S Δ I Ω β R spec P start (t' + 1) m :=
  .hold (.held hΩ hin) (fun _ h => nomatch h) hl

/-- **`line_last_accepted`**: an accepted command is the line's value at
    that tick, whatever the history. -/
theorem line_last_accepted {t : Nat} {m : Value} (h : AdapterOp S Δ I Ω β R spec P t (.set m)) :
    Line S Δ I Ω β R spec P start t m := by
  cases t with
  | zero => exact .set0 h
  | succ t => exact .set h

/-- The line's value is either the start value or a value the policy
    accepted at some tick `≤ t` — the line never carries a command the
    policy refused. -/
theorem line_value_accepted : ∀ {t : Nat} {m : Value}, Line S Δ I Ω β R spec P start t m →
    m = start ∨ ∃ t' ≤ t, AdapterOp S Δ I Ω β R spec P t' (.set m)
  | 0, m, h => by
    cases h with
    | set0 ha => exact Or.inr ⟨0, Nat.le_refl 0, ha⟩
    | hold0 _ _ => exact Or.inl rfl
  | t + 1, m, h => by
    cases h with
    | set ha => exact Or.inr ⟨t + 1, Nat.le_refl _, ha⟩
    | hold _ _ hl =>
      rcases line_value_accepted hl with h | ⟨t', ht', ha⟩
      · exact Or.inl h
      · exact Or.inr ⟨t', Nat.le_succ_of_le ht', ha⟩

end Lines

end BDL.Adapter
