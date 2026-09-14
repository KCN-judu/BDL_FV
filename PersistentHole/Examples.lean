import PersistentHole.Artifact

/-!
# Examples and counterexamples

Part 1 instantiates the model with concrete (decidable) evidence and walks one
hole through its whole life.

Part 2 constructs counterexamples for each of the weakenings the experiment
was asked to probe:

* **A** refinement may change `expectedType`   → Theorem 5 fails, clients break
* **B** refinement may drop obligations         → Theorem 5 fails silently
* **C** realization regenerates the identity    → references go stale
* **D** `strengthen` without re-verification    → Theorem 4 fails

plus the observation that `SpecEquiv` is not antisymmetric.
-/

namespace PersistentHole.Examples
open PersistentHole

/-! ## Part 1 — a concrete lifecycle -/

/-- Purely syntactic evidence, just so examples can be checked by `decide`.
    It is deliberately incomplete (no term is ever `bounded`); the theorems
    do not care. -/
def evB (e : Expr) : PropertyId → Bool
  | .total    => match e with | .lam _ _ => true | _ => false
  | .monotone => e == .lam .nat (.var 0)     -- only the identity is "known" monotone
  | .bounded  => false

def ev : Evidence := fun e p => evB e p = true

instance : ∀ e p, Decidable (ev e p) := fun e p => inferInstanceAs (Decidable (evB e p = true))

/-- The hole under study, say "the map from tilt to brightness". -/
def hid : HoleId := ⟨0⟩

def S₀ : Spec := ⟨.arr .nat .nat, []⟩
def S₁ : Spec := S₀.addObligation .total
def S₂ : Spec := S₁.addObligation .monotone

def idNat : Expr := .lam .nat (.var 0)

/-- `h : S₀  ↝  h : S₁  ↝  h : S₂  ↝  h := idNat` -/
def h₀ : DesignHole := .unresolved hid S₀
def h₁ : DesignHole := .unresolved hid S₁
def h₂ : DesignHole := .unresolved hid S₂
def h₃ : DesignHole := ⟨hid, S₂, some idNat⟩

theorem step₀₁ : HoleRefines ev [] h₀ h₁ := .refine (by decide)
theorem step₁₂ : HoleRefines ev [] h₁ h₂ := .refine (by decide)
theorem step₂₃ : HoleRefines ev [] h₂ h₃ := .realize (by decide)

theorem lifecycle : HoleRefinesStar ev [] h₀ h₃ :=
  .step step₀₁ (.step step₁₂ (.single step₂₃))

-- Identity survives; the closed form agrees; the final term meets S₀.
example : h₀.id = h₃.id := lifecycle.id_eq
example : HoleLeq ev [] h₀ h₃ := by decide
example : Satisfies ev [] idNat S₀ :=
  lifecycle.final_realization_satisfies_all (WellFormedHole.unresolved ev [] hid S₀) rfl

-- A term that fails a commitment made along the way is rejected as a
-- realization of the *current* spec even though it has the right type.
def constZero : Expr := .lam .nat (.natLit 0)
example : Satisfies ev [] constZero S₁ := by decide      -- typed and total
example : ¬ Satisfies ev [] constZero S₂ := by decide    -- but not (known) monotone

-- An artifact referring to the hole by id refers to every state of it.
def consumer : Artifact := ⟨"lamp-controller", [hid]⟩
example : consumer.RefersTo h₀ := by decide
example : consumer.RefersTo h₃ := consumer.refersTo_of_refines (by decide) lifecycle

-- Environment view: realizing the hole overwrites the referenced slot.
def env₀ : HoleEnv := fun id => if id = hid then some h₂ else none
example : EnvRefines ev [] env₀ (env₀.update h₃) :=
  EnvRefines_update (by simp [env₀, h₂, DesignHole.unresolved, hid]) step₂₃
example : (env₀.update h₃) hid = some h₃ := by decide

/-! ## Part 2 — counterexamples -/

/-! ### A. If refinement may change `expectedType` -/

/-- "Refinement" that keeps obligations but is free to retarget the type. -/
def LooseRefines (old new : Spec) : Prop := old.obligations ⊆ new.obligations

/-- Theorem 5 fails: `true : bool` realizes the retargeted spec but not the
    original `nat` commitment. -/
theorem loose_breaks_theorem5 :
    ¬ ∀ (ev : Evidence) (Γ : Ctx) (e : Expr) (S₀ S₁ : Spec),
        LooseRefines S₀ S₁ → Satisfies ev Γ e S₁ → Satisfies ev Γ e S₀ := by
  intro h
  have hs := h (fun _ _ => True) [] (.boolLit true) ⟨.nat, []⟩ ⟨.bool, []⟩
    (List.Subset.refl _) ⟨.boolLit, fun _ _ => trivial⟩
  exact absurd hs.1 (by decide)

/-- Worse: a *client* typed against the old commitment is invalidated even
    though the client itself did not change.  `client` consumes the hole's
    value (de Bruijn 0) at type `nat`. -/
def client : Expr := .app (.lam .nat (.var 0)) (.var 0)
example : HasType [Ty.nat] client .nat := by decide
example : ¬ HasType [Ty.bool] client .nat := by decide

/-- Any realization of the old type is incompatible with the new one, by
    uniqueness of typing — so retargeting is never a "refinement" of a
    realized hole. -/
theorem retype_kills_realization {Γ : Ctx} {e : Expr} {τ τ' : Ty}
    (hne : τ ≠ τ') (he : HasType Γ e τ) : ¬ HasType Γ e τ' :=
  fun he' => hne (he.unique he')

/-! ### B. If refinement may drop obligations -/

/-- "Refinement" that keeps the type but is free to forget obligations. -/
def ForgetfulRefines (old new : Spec) : Prop := old.expectedType = new.expectedType

/-- Theorem 5 fails: after `bounded` is forgotten, a term with no evidence for
    it is accepted, and the earlier design commitment is silently violated.
    Nothing in the types detects this — it is exactly the "progressive
    formalization forgets a commitment" failure. -/
theorem forgetful_breaks_theorem5 :
    ¬ ∀ (ev : Evidence) (Γ : Ctx) (e : Expr) (S₀ S₁ : Spec),
        ForgetfulRefines S₀ S₁ → Satisfies ev Γ e S₁ → Satisfies ev Γ e S₀ := by
  intro h
  have hs := h (fun _ _ => False) [] (.natLit 7) ⟨.nat, [.bounded]⟩ ⟨.nat, []⟩
    rfl ⟨.natLit, fun _ hp => nomatch hp⟩
  exact hs.2 .bounded (List.mem_singleton.mpr rfl)

-- The same with the concrete evidence of Part 1: `constZero` meets S₁ but
-- would be accepted for S₂ if `monotone` could be dropped again.
example : Satisfies ev [] constZero ⟨S₂.expectedType, []⟩ := by decide
example : ¬ Satisfies ev [] constZero S₂ := by decide
example : ForgetfulRefines S₂ ⟨S₂.expectedType, []⟩ := rfl

/-! ### C. If realization regenerates the identity -/

/-- Realization that mints a fresh id, i.e. treats "the realized thing" as a
    new entity distinct from "the unresolved thing". -/
def realizeFresh (h : DesignHole) (fresh : HoleId) (e : Expr) : DesignHole :=
  ⟨fresh, h.spec, some e⟩

def fresh : HoleId := ⟨1⟩
def h₃' : DesignHole := realizeFresh h₂ fresh idNat

/-- The consumer referred to the design entity while it was unresolved and no
    longer refers to it once realized — although *nothing about the consumer
    changed*. -/
example : consumer.RefersTo h₂ ∧ ¬ consumer.RefersTo h₃' := by decide

/-- At the environment level: writing the freshly-identified realization back
    leaves the referenced slot holding the stale *unresolved* state, so the
    consumer keeps resolving to a hole that has no realization. -/
theorem fresh_id_breaks_env_refinement :
    (env₀.update h₃') hid = some h₂ ∧ ((env₀.update h₃') hid).map (·.realization) = some none := by
  decide

/-- Consequently the "update" is not an `EnvRefines` step in the sense that
    matters: the slot the consumer reads has not been refined to `h₃'`
    (it has not moved at all), and no hole in the environment before the
    update is related to `h₃'` by `HoleRefinesStar`. -/
theorem no_prior_hole_refines_to_fresh :
    ∀ id h, env₀ id = some h → ¬ HoleRefinesStar ev [] h h₃' := by
  intro id h hh hr
  have hid_eq : h.id = h₃'.id := hr.id_eq
  have : h = h₂ := by
    unfold env₀ at hh
    split at hh
    · exact (Option.some.inj hh).symm
    · exact nomatch hh
  subst this
  exact absurd hid_eq (by decide)

/-! ### D. If a realized hole may be strengthened without re-verification

This is the "first, natural" definition of the lifecycle relation: the same
three steps as `HoleRefines`, but `strengthen` only asks for `Refines S S'`.
It seems harmless — surely adding an obligation to the *spec* does not touch
the *term*?  But well-formedness says the term meets the spec, so the term
must be re-checked against every added obligation. -/
inductive NaiveHoleRefines (ev : Evidence) (Γ : Ctx) : DesignHole → DesignHole → Prop where
  | refine {id S S'} (h : Refines S S') :
      NaiveHoleRefines ev Γ ⟨id, S, none⟩ ⟨id, S', none⟩
  | realize {id S e} (hs : Satisfies ev Γ e S) :
      NaiveHoleRefines ev Γ ⟨id, S, none⟩ ⟨id, S, some e⟩
  | strengthen {id S S' e} (h : Refines S S') :
      NaiveHoleRefines ev Γ ⟨id, S, some e⟩ ⟨id, S', some e⟩

-- Theorems 1–3 still hold for the naive relation …
theorem NaiveHoleRefines.id_eq {ev Γ} {h₁ h₂ : DesignHole}
    (h : NaiveHoleRefines ev Γ h₁ h₂) : h₁.id = h₂.id := by cases h <;> rfl

theorem NaiveHoleRefines.spec_refines {ev Γ} {h₁ h₂ : DesignHole}
    (h : NaiveHoleRefines ev Γ h₁ h₂) : Refines h₁.spec h₂.spec := by
  cases h with
  | refine h => exact h
  | realize _ => exact Refines.refl _
  | strengthen h => exact h

-- … but Theorem 4 does not.  Strengthening the realized `constZero` with
-- `monotone` produces a hole whose term violates its own spec.
def realizedS₁ : DesignHole := ⟨hid, S₁, some constZero⟩
def realizedS₂ : DesignHole := ⟨hid, S₂, some constZero⟩

theorem naive_breaks_wellformedness :
    ¬ ∀ (h₁ h₂ : DesignHole),
        WellFormedHole ev [] h₁ → NaiveHoleRefines ev [] h₁ h₂ → WellFormedHole ev [] h₂ := by
  intro h
  have wf₁ : WellFormedHole ev [] realizedS₁ := by decide
  have step : NaiveHoleRefines ev [] realizedS₁ realizedS₂ :=
    .strengthen (Refines_addObligation S₁ .monotone)
  have wf₂ := h _ _ wf₁ step
  exact absurd wf₂ (by decide)

/-- The missing assumption, isolated: the naive step preserves well-formedness
    exactly when the existing term meets the strengthened spec — which is the
    premise `HoleRefines.strengthen` carries.  (`Refines S S'` plays no role
    in this equivalence: the type is preserved automatically, and the *new*
    obligations are precisely what needs fresh evidence.) -/
theorem naive_strengthen_wf_iff {id : HoleId} {S S' : Spec} {e : Expr} :
    (WellFormedHole ev [] ⟨id, S, some e⟩ → WellFormedHole ev [] ⟨id, S', some e⟩)
      ↔ (Satisfies ev [] e S → Satisfies ev [] e S') := by
  constructor
  · intro f hs
    exact f (WellFormedHole.realized hs) e rfl
  · intro f wf
    exact WellFormedHole.realized (f (wf e rfl))

/-! ### `SpecEquiv` is not antisymmetric -/

example : SpecEquiv ⟨.nat, [.total, .total]⟩ ⟨.nat, [.total]⟩ ∧
    (⟨.nat, [.total, .total]⟩ : Spec) ≠ ⟨.nat, [.total]⟩ := by decide

end PersistentHole.Examples
