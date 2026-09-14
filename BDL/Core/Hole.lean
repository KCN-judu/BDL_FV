import BDL.Core.Spec

/-!
# Hole — design holes, hole environments, and the structural lifecycle order

`DesignHole` is unchanged from Phase 0: identity, spec and realization are
three independent fields.

New in Phase 1:

* `HoleEnv` — the global map from ids to hole states that references are
  resolved against, and its *type view* `tyView`, which is all that typing
  is allowed to see.
* `HoleLeq` / `EnvRefines` — the purely **structural** lifecycle order
  (id frozen, spec refines, realization write-once), with *no* satisfaction
  condition.  Satisfaction is a separate global invariant (`GlobalWF` in
  `Env.lean`).  Separating the order from the invariant is what lets the
  typing-preservation theorem be stated under the weakest hypotheses.
-/

namespace BDL

structure DesignHole where
  id          : HoleId
  spec        : Spec
  realization : Option Expr
  deriving DecidableEq, Repr

def DesignHole.unresolved (id : HoleId) (S : Spec) : DesignHole := ⟨id, S, none⟩

/-! ## Environments -/

/-- Partial map from ids to hole states. -/
abbrev HoleEnv := HoleId → Option DesignHole

def HoleEnv.empty : HoleEnv := fun _ => none

/-- Store (the new state of) hole `h` under its own id. -/
def HoleEnv.update (Δ : HoleEnv) (h : DesignHole) : HoleEnv :=
  fun id => if id = h.id then some h else Δ id

theorem HoleEnv.update_self (Δ : HoleEnv) (h : DesignHole) :
    Δ.update h h.id = some h := by
  simp [HoleEnv.update]

theorem HoleEnv.update_other (Δ : HoleEnv) (h : DesignHole) {id : HoleId}
    (hne : id ≠ h.id) : Δ.update h id = Δ id := by
  simp [HoleEnv.update, hne]

/-- Finite environments, for decidable examples.  First match wins. -/
def HoleEnv.ofList (l : List DesignHole) : HoleEnv :=
  fun id => l.find? (·.id = id)

theorem HoleEnv.ofList_some {l : List DesignHole} {id : HoleId} {h : DesignHole}
    (hh : HoleEnv.ofList l id = some h) : h ∈ l ∧ h.id = id := by
  unfold HoleEnv.ofList at hh
  exact ⟨List.mem_of_find?_eq_some hh, by simpa using List.find?_some hh⟩

/-- **The type view.**  Typing may consult the environment only through this
    projection: the expected type of each declared hole. -/
def HoleEnv.tyView (Δ : HoleEnv) (h : HoleId) : Option Ty :=
  (Δ h).map (·.spec.expectedType)

/-- The realization of a hole, if it is declared and realized. -/
def HoleEnv.realizationOf (Δ : HoleEnv) (h : HoleId) : Option Expr :=
  (Δ h).bind (·.realization)

/-! ## Structural lifecycle order -/

/-- `HoleLeq h₁ h₂`: `h₂` is a later state of the *same* design entity. -/
def HoleLeq (h₁ h₂ : DesignHole) : Prop :=
  h₁.id = h₂.id ∧
  Refines h₁.spec h₂.spec ∧
  ∀ e, h₁.realization = some e → h₂.realization = some e

instance (h₁ h₂ : DesignHole) : Decidable (HoleLeq h₁ h₂) := by
  unfold HoleLeq
  have : Decidable (∀ e, h₁.realization = some e → h₂.realization = some e) := by
    cases h₁.realization with
    | none => exact isTrue fun _ h => nomatch h
    | some e =>
      if h : h₂.realization = some e then
        exact isTrue fun _ h' => Option.some.inj h' ▸ h
      else
        exact isFalse fun f => h (f e rfl)
  exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem HoleLeq.refl (h : DesignHole) : HoleLeq h h :=
  ⟨rfl, Refines.refl _, fun _ he => he⟩

theorem HoleLeq.trans {h₀ h₁ h₂ : DesignHole} (a : HoleLeq h₀ h₁) (b : HoleLeq h₁ h₂) :
    HoleLeq h₀ h₂ :=
  ⟨a.1.trans b.1, a.2.1.trans b.2.1, fun e he => b.2.2 e (a.2.2 e he)⟩

theorem HoleLeq.id_eq {h₁ h₂ : DesignHole} (h : HoleLeq h₁ h₂) : h₁.id = h₂.id := h.1
theorem HoleLeq.spec_refines {h₁ h₂ : DesignHole} (h : HoleLeq h₁ h₂) : Refines h₁.spec h₂.spec := h.2.1
theorem HoleLeq.expectedType_eq {h₁ h₂ : DesignHole} (h : HoleLeq h₁ h₂) :
    h₁.spec.expectedType = h₂.spec.expectedType := h.2.1.1

/-- `EnvRefines Δ₁ Δ₂`: every entity declared in `Δ₁` is declared in `Δ₂`, under
    the same id, in a later state.  New entities may appear. -/
def EnvRefines (Δ₁ Δ₂ : HoleEnv) : Prop :=
  ∀ id h₁, Δ₁ id = some h₁ → ∃ h₂, Δ₂ id = some h₂ ∧ HoleLeq h₁ h₂

theorem EnvRefines.refl (Δ : HoleEnv) : EnvRefines Δ Δ :=
  fun _ h₁ h => ⟨h₁, h, HoleLeq.refl _⟩

theorem EnvRefines.trans {Δ₀ Δ₁ Δ₂ : HoleEnv}
    (a : EnvRefines Δ₀ Δ₁) (b : EnvRefines Δ₁ Δ₂) : EnvRefines Δ₀ Δ₂ := by
  intro id h₀ h
  obtain ⟨h₁, h₁eq, r₁⟩ := a id h₀ h
  obtain ⟨h₂, h₂eq, r₂⟩ := b id h₁ h₁eq
  exact ⟨h₂, h₂eq, r₁.trans r₂⟩

/-- Environment refinement never changes the type view of a declared hole. -/
theorem EnvRefines.tyView {Δ₁ Δ₂ : HoleEnv} (er : EnvRefines Δ₁ Δ₂) {h : HoleId} {τ : Ty}
    (ht : Δ₁.tyView h = some τ) : Δ₂.tyView h = some τ := by
  unfold HoleEnv.tyView at *
  cases hh : Δ₁ h with
  | none => simp [hh] at ht
  | some dh =>
    obtain ⟨dh₂, hh₂, le⟩ := er h dh hh
    simp [hh] at ht
    simp [hh₂, ← le.expectedType_eq, ht]

/-- Realizations, once present, survive environment refinement. -/
theorem EnvRefines.realizationOf {Δ₁ Δ₂ : HoleEnv} (er : EnvRefines Δ₁ Δ₂) {h : HoleId} {e : Expr}
    (he : Δ₁.realizationOf h = some e) : Δ₂.realizationOf h = some e := by
  unfold HoleEnv.realizationOf at *
  cases hh : Δ₁ h with
  | none => simp [hh] at he
  | some dh =>
    obtain ⟨dh₂, hh₂, le⟩ := er h dh hh
    simp [hh] at he
    simp [hh₂, le.2.2 e he]

/-- **Where identity does its work.**  Stepping the entity stored at `h₁.id`
    to `h₂` and writing it back is an environment refinement *because*
    `h₂.id = h₁.id` puts the write on the slot every reference resolves to. -/
theorem EnvRefines_update {Δ : HoleEnv} {h₁ h₂ : DesignHole}
    (hstored : Δ h₁.id = some h₁) (le : HoleLeq h₁ h₂) :
    EnvRefines Δ (Δ.update h₂) := by
  intro id h hh
  by_cases hid : id = h₂.id
  · subst hid
    have : h = h₁ := by
      rw [← le.id_eq] at hh
      exact Option.some.inj (hh.symm.trans hstored)
    subst this
    exact ⟨h₂, Δ.update_self h₂, le⟩
  · exact ⟨h, (Δ.update_other h₂ hid).trans hh, HoleLeq.refl _⟩

end BDL
