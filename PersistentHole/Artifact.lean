import PersistentHole.Refinement

/-!
# Artifact — references between design artifacts

The smallest model in which persistent identity does observable work.

* An `Artifact` is anything that mentions holes *by id* (here: a bare list of
  ids — no dependency graph, no module system).
* A `HoleEnv` maps ids to hole states.  Refining or realizing a hole is an
  `update` of the environment at the hole's own id.

The payoff of Theorem 1 (`HoleRefines.id_eq`) is `EnvRefines_update`: because
a refinement step cannot change the id, updating the environment with the new
state overwrites *exactly* the slot every existing reference points at.  So
references are stable across the entire lifecycle, and — via
`resolve_update_refines` — whatever they resolve to afterwards is a refinement
of what they resolved to before.

`Examples.lean` shows the failure mode when identity is regenerated instead.
-/

namespace PersistentHole

structure Artifact where
  name : String
  refs : List HoleId
  deriving DecidableEq, Repr

/-- `a` refers to (the design entity that is) `h`. Only the id matters. -/
def Artifact.RefersTo (a : Artifact) (h : DesignHole) : Prop :=
  h.id ∈ a.refs

instance (a : Artifact) (h : DesignHole) : Decidable (a.RefersTo h) :=
  inferInstanceAs (Decidable (h.id ∈ a.refs))

/-- **Reference stability.** A reference to a hole survives every refinement
    and realization step of that hole. -/
theorem Artifact.refersTo_of_refines {ev : Evidence} {Γ : Ctx}
    {a : Artifact} {h₁ h₂ : DesignHole}
    (hr : a.RefersTo h₁) (h : HoleRefinesStar ev Γ h₁ h₂) : a.RefersTo h₂ := by
  unfold Artifact.RefersTo at *
  rw [← h.id_eq]
  exact hr

/-! ## Hole environments -/

/-- A hole environment: partial map from ids to hole states. -/
abbrev HoleEnv := HoleId → Option DesignHole

/-- Store the (new state of) hole `h` under its own id. -/
def HoleEnv.update (env : HoleEnv) (h : DesignHole) : HoleEnv :=
  fun id => if id = h.id then some h else env id

theorem HoleEnv.update_self (env : HoleEnv) (h : DesignHole) :
    env.update h h.id = some h := by
  simp [HoleEnv.update]

theorem HoleEnv.update_other (env : HoleEnv) (h : DesignHole) {id : HoleId}
    (hne : id ≠ h.id) : env.update h id = env id := by
  simp [HoleEnv.update, hne]

/-- Environment-level refinement: every hole present before is still present,
    under the same id, in a refined state. -/
def EnvRefines (ev : Evidence) (Γ : Ctx) (env₁ env₂ : HoleEnv) : Prop :=
  ∀ id h₁, env₁ id = some h₁ → ∃ h₂, env₂ id = some h₂ ∧ HoleRefinesStar ev Γ h₁ h₂

theorem EnvRefines.refl (ev : Evidence) (Γ : Ctx) (env : HoleEnv) : EnvRefines ev Γ env env :=
  fun _ h₁ h => ⟨h₁, h, .refl _⟩

theorem EnvRefines.trans {ev : Evidence} {Γ : Ctx} {env₀ env₁ env₂ : HoleEnv}
    (a : EnvRefines ev Γ env₀ env₁) (b : EnvRefines ev Γ env₁ env₂) :
    EnvRefines ev Γ env₀ env₂ := by
  intro id h₀ h
  obtain ⟨h₁, h₁eq, r₁⟩ := a id h₀ h
  obtain ⟨h₂, h₂eq, r₂⟩ := b id h₁ h₁eq
  exact ⟨h₂, h₂eq, r₁.trans r₂⟩

/-- **The role of identity.** Stepping the hole stored at `h₁.id` to `h₂` and
    writing the result back under `h₂.id` is an environment refinement.  The
    proof needs `HoleRefines.id_eq` to know the write lands on the slot that
    `h₁` occupied; without identity preservation this theorem is false
    (`Examples.fresh_id_breaks_env_refinement`). -/
theorem EnvRefines_update {ev : Evidence} {Γ : Ctx} {env : HoleEnv} {h₁ h₂ : DesignHole}
    (hstored : env h₁.id = some h₁) (step : HoleRefines ev Γ h₁ h₂) :
    EnvRefines ev Γ env (env.update h₂) := by
  intro id h hh
  by_cases hid : id = h₂.id
  · subst hid
    -- the slot being written is exactly `h₁`'s slot
    have : h = h₁ := by
      rw [← step.id_eq] at hh
      exact Option.some.inj (hh.symm.trans hstored)
    subst this
    exact ⟨h₂, env.update_self h₂, .single step⟩
  · exact ⟨h, (env.update_other h₂ hid).trans hh, .refl _⟩

/-- Resolving a reference: look every id up in the environment. -/
def Artifact.ResolvesIn (a : Artifact) (env : HoleEnv) : Prop :=
  ∀ id ∈ a.refs, ∃ h, env id = some h

/-- **Reference resolution is preserved by environment refinement**, and each
    reference resolves to a refinement of what it resolved to before. -/
theorem resolve_update_refines {ev : Evidence} {Γ : Ctx} {env₁ env₂ : HoleEnv}
    (er : EnvRefines ev Γ env₁ env₂) {a : Artifact} (ha : a.ResolvesIn env₁) :
    a.ResolvesIn env₂ ∧
    ∀ id ∈ a.refs, ∀ h₁, env₁ id = some h₁ →
      ∃ h₂, env₂ id = some h₂ ∧ HoleRefinesStar ev Γ h₁ h₂ := by
  refine ⟨?_, fun id _ h₁ hh => er id h₁ hh⟩
  intro id hid
  obtain ⟨h₁, hh⟩ := ha id hid
  obtain ⟨h₂, hh₂, _⟩ := er id h₁ hh
  exact ⟨h₂, hh₂⟩

end PersistentHole
