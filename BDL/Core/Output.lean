import BDL.Core.Clock

/-!
# Output — physical outputs and the single-driver discipline (Phase 6)

A declaration computes a *value*; hardware moves only through an explicit
**drive edge** from a declaration to a **physical sink**.

* `OutputId`   — nominal identity of a sink (a resource; not a concept, not
                 a design relationship).
* `OutputEnv Ω`— what each sink accepts: a target `Ty` and a `ClockId`.
* `DriveEnv β` — which declaration drives which sink (per-declaration
                 projection, write-once, like `Κ`).
* `DriveWF`    — a drive edge is well formed iff the driver's type *equals*
                 the accepted type and the driver lives in the sink's domain.
                 No coercion and no synchronization happen in the binding.
* `SingleDriver β` — at most one driver per sink: a **global** invariant that
                 no local typing rule can express.
* `CompleteOutputs β req` — every required sink is driven; with
                 `SingleDriver`, exactly once (executable designs only).

All combination of several behaviours into one target is ordinary value
computation upstream of the single drive edge.  Rejected alternatives and
counterexamples: `Experiments/OutputAlternatives.lean`.
-/

namespace BDL.Output
open BDL BDL.Reactive BDL.Clock

/-! ## §1 The model -/

/-- Nominal identity of a physical sink.  Distinct from `DeclId` (a design
    relationship) and `ConceptId` (a concept): "the steering motor" is a
    resource, "the desired steering angle" is a value. -/
structure OutputId where
  n : Nat
  deriving DecidableEq, Repr

/-- What a sink accepts.  The accepted type is ordinary `Ty` — typically a
    semantic target (`MotorAngle`) or a device-command concept; the kernel
    does not distinguish, the deployment declares. -/
structure OutputSpec where
  accepts : Ty
  clock   : ClockId
  deriving DecidableEq, Repr

abbrev OutputEnv := OutputId → Option OutputSpec
/-- The drive edges: declaration `d` directly drives sink `o`. -/
abbrev DriveEnv := DeclId → Option OutputId

def DriveEnv.none : DriveEnv := fun _ => Option.none
def DriveEnv.ofList (l : List (DeclId × OutputId)) : DriveEnv :=
  fun d => (l.find? fun p => p.1 = d).map Prod.snd
def OutputEnv.ofList (l : List (OutputId × OutputSpec)) : OutputEnv :=
  fun o => (l.find? fun p => p.1 = o).map Prod.snd

/-- A drive edge consumes an already valid target value: the driver's type
    *equals* the accepted type and the driver lives in the sink's domain. -/
def DriveWF (Ω : OutputEnv) (Κ : ClockEnv) (Δ : DeclEnv) (β : DriveEnv) : Prop :=
  ∀ d o, β d = some o → ∃ spec, Ω o = some spec ∧ Δ.tyView d = some spec.accepts ∧ Κ d = some spec.clock

/-- **The single-driver invariant** — global, over the drive edges only.
    Upstream contributors are not drivers. -/
def SingleDriver (β : DriveEnv) : Prop :=
  ∀ d₁ d₂ o, β d₁ = some o → β d₂ = some o → d₁ = d₂

def Driven (β : DriveEnv) (o : OutputId) : Prop := ∃ d, β d = some o

/-- Every required sink is driven.  With `SingleDriver`: exactly once. -/
def CompleteOutputs (β : DriveEnv) (req : List OutputId) : Prop := ∀ o ∈ req, Driven β o

/-- Decidable checks for finite designs. -/
def driveWFCheck (Ω : OutputEnv) (Κ : ClockEnv) (Δ : DeclEnv) (l : List (DeclId × OutputId)) : Bool :=
  l.all fun p => match Ω p.2 with
    | some spec => decide (Δ.tyView p.1 = some spec.accepts) && decide (Κ p.1 = some spec.clock)
    | none => false

theorem DriveWF.ofList {Ω : OutputEnv} {Κ : ClockEnv} {Δ : DeclEnv} {l : List (DeclId × OutputId)}
    (h : driveWFCheck Ω Κ Δ l = true) : DriveWF Ω Κ Δ (.ofList l) := by
  intro d o hβ
  simp only [DriveEnv.ofList, Option.map_eq_some_iff] at hβ
  obtain ⟨p, hp, rfl⟩ := hβ
  have hmem := List.mem_of_find?_eq_some hp
  have hfst : p.1 = d := by simpa using List.find?_some hp
  have := (List.all_eq_true.mp h) p hmem
  cases hΩ : Ω p.2 with
  | none => rw [hΩ] at this; exact nomatch this
  | some spec =>
    rw [hΩ] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨spec, rfl, hfst ▸ this.1, hfst ▸ this.2⟩

/-- Single-driver for a finite drive list: the sinks are pairwise distinct. -/
theorem SingleDriver.ofList {l : List (DeclId × OutputId)} (h : (l.map Prod.snd).Nodup) :
    SingleDriver (.ofList l) := by
  intro d₁ d₂ o h₁ h₂
  simp only [DriveEnv.ofList, Option.map_eq_some_iff] at h₁ h₂
  obtain ⟨p₁, hp₁, hs₁⟩ := h₁
  obtain ⟨p₂, hp₂, hs₂⟩ := h₂
  have m₁ := List.mem_of_find?_eq_some hp₁
  have m₂ := List.mem_of_find?_eq_some hp₂
  have f₁ : p₁.1 = d₁ := by simpa using List.find?_some hp₁
  have f₂ : p₂.1 = d₂ := by simpa using List.find?_some hp₂
  have : p₁ = p₂ := by
    -- two entries with the same sink in a sink-nodup list are the same entry
    have key : ∀ (l : List (DeclId × OutputId)), (l.map Prod.snd).Nodup →
        ∀ p q, p ∈ l → q ∈ l → p.2 = q.2 → p = q := by
      intro l
      induction l with
      | nil => intro _ p q hp; simp at hp
      | cons x xs ih =>
        intro hn p q hp hq heq
        rw [List.map_cons, List.nodup_cons] at hn
        rcases List.mem_cons.mp hp with rfl | hp' <;> rcases List.mem_cons.mp hq with rfl | hq'
        · rfl
        · exact absurd (heq ▸ List.mem_map_of_mem hq' : p.2 ∈ xs.map Prod.snd) hn.1
        · exact absurd (heq ▸ List.mem_map_of_mem hp' : q.2 ∈ xs.map Prod.snd) (by simpa [heq] using hn.1)
        · exact ih hn.2 p q hp' hq' heq
    exact key l h p₁ p₂ m₁ m₂ (hs₁.trans hs₂.symm)
  subst this
  exact f₁.symm.trans f₂

/-! ## Refinement -/

/-- Drive edges are write-once per declaration, like realizations. -/
def DriveRefines (β₁ β₂ : DriveEnv) : Prop := ∀ d o, β₁ d = some o → β₂ d = some o

def DriveEnv.bind (β : DriveEnv) (d : DeclId) (o : OutputId) : DriveEnv :=
  fun d' => if d' = d then Option.some o else β d'

/-- **`first_output_binding_is_monotone`.**  Binding an unbound declaration
    to a sink nobody drives preserves single-driver (and, given the edge is
    well formed, `DriveWF`): the first binding is a refinement. -/
theorem first_output_binding_is_monotone {β : DriveEnv} (hs : SingleDriver β) {d : DeclId} {o : OutputId}
    (hd : β d = Option.none) (ho : ¬ Driven β o) :
    DriveRefines β (β.bind d o) ∧ SingleDriver (β.bind d o) := by
  refine ⟨?_, ?_⟩
  · intro d' o' h
    unfold DriveEnv.bind
    split
    · rename_i heq; subst heq; rw [hd] at h; exact nomatch h
    · exact h
  · intro d₁ d₂ o' h₁ h₂
    unfold DriveEnv.bind at h₁ h₂
    split at h₁ <;> split at h₂
    · rename_i e₁ e₂; exact e₁.trans e₂.symm
    · rename_i e₁ _; cases h₁; exact absurd ⟨d₂, h₂⟩ ho
    · rename_i _ e₂; cases h₂; exact absurd ⟨d₁, h₁⟩ ho
    · exact hs d₁ d₂ o' h₁ h₂

/-! ## Partial vs executable -/

/-- A *partial* design: single-driver and well-formed edges; sinks may be undriven. -/
def PartialOutputWF (Ω : OutputEnv) (Κ : ClockEnv) (Δ : DeclEnv) (β : DriveEnv) : Prop :=
  DriveWF Ω Κ Δ β ∧ SingleDriver β

/-- The additional condition for an executable design: every required sink
    is driven (hence, with single-driver, exactly once). -/
def ExecutableOutputs (Ω : OutputEnv) (Κ : ClockEnv) (Δ : DeclEnv) (β : DriveEnv) (req : List OutputId) : Prop :=
  PartialOutputWF Ω Κ Δ β ∧ CompleteOutputs β req

/-! ## Physical output semantics -/

/-- What a sink physically receives at global tick `t`: the value of its
    driver, evaluated in the sink's domain.  Sinks are terminal — no feedback
    edge; a sensed consequence is another input. -/
def PhysicalOutput (S : Sched) (Δ : DeclEnv) (I : Input) (Ω : OutputEnv) (β : DriveEnv)
    (o : OutputId) (t : Nat) (v : Value) : Prop :=
  ∃ d spec, β d = some o ∧ Ω o = some spec ∧ MEv S Δ I spec.clock t [] (.declRef d) v

/-- **`single_driver_completed_design_deterministic`**: with a single driver
    the physical output is a partial function of the tick. -/
theorem single_driver_output_deterministic {S : Sched} {Δ : DeclEnv} {I : Input} {Ω : OutputEnv} {β : DriveEnv}
    (hs : SingleDriver β) {o : OutputId} {t : Nat} {v₁ v₂ : Value}
    (h₁ : PhysicalOutput S Δ I Ω β o t v₁) (h₂ : PhysicalOutput S Δ I Ω β o t v₂) : v₁ = v₂ := by
  obtain ⟨d₁, spec₁, hb₁, hΩ₁, he₁⟩ := h₁
  obtain ⟨d₂, spec₂, hb₂, hΩ₂, he₂⟩ := h₂
  have := hs d₁ d₂ o hb₁ hb₂
  subst this
  rw [hΩ₁] at hΩ₂; cases hΩ₂
  exact he₁.det he₂


end BDL.Output
