import BDL.Core.Dependency

/-!
# Experiments — holes, cross-hole references, and their counterexamples

Part 0 — Phase-0 examples and counterexamples, ported (environment `.empty`).

Part 1 — the Phase-1 probes.  `A := λx. f (B x)` is realized while `B` is
still unresolved.  We then do each of the five things to `B` and watch `A`:

| probe                     | typing of A | commitments of A | theorem / counterexample |
|---------------------------|-------------|------------------|--------------------------|
| 1 strengthen B's spec     | kept        | kept             | `probe1_*`               |
| 2 realize B               | kept        | kept             | `probe2_*`               |
| 3 re-identify B           | **broken**  | —                | `probe3_*`               |
| 4 change B's type         | **broken**  | —                | `probe4_*`               |
| 5 drop B's obligation     | kept        | **broken**       | `probe5_*`               |
| 6 non-monotone evidence   | kept        | **broken**       | `probe6_*`               |

Part 2 — dependency cycles.
-/

namespace BDL.Experiments
open BDL

/-! ## Part 0 — Phase 0, ported -/

/-- Syntactic, environment-independent evidence (decidable). -/
def evB (e : Expr) : PropertyId → Bool
  | .total    => match e with | .lam _ _ => true | _ => false
  | .monotone => e == .lam .nat (.var 0)
  | .bounded  => false

def ev : Evidence := fun _ e p => evB e p = true

instance : ∀ Δ e p, Decidable (ev Δ e p) := fun _ e p => inferInstanceAs (Decidable (evB e p = true))

theorem ev_mono : ev.Monotone := fun _ _ _ _ _ h => h

def hid : HoleId := ⟨0⟩
def S₀ : Spec := ⟨.arr .nat .nat, []⟩
def S₁ : Spec := S₀.addObligation .total
def S₂ : Spec := S₁.addObligation .monotone
def idNat : Expr := .lam .nat (.var 0)
def constZero : Expr := .lam .nat (.natLit 0)

def h₀ : DesignHole := .unresolved hid S₀
def h₁ : DesignHole := .unresolved hid S₁
def h₂ : DesignHole := .unresolved hid S₂
def h₃ : DesignHole := ⟨hid, S₂, some idNat⟩

theorem step₀₁ : HoleRefines ev .empty [] h₀ h₁ := .refine (by decide)
theorem step₁₂ : HoleRefines ev .empty [] h₁ h₂ := .refine (by decide)
theorem step₂₃ : HoleRefines ev .empty [] h₂ h₃ := .realize (by decide)
theorem lifecycle : HoleRefinesStar ev .empty [] h₀ h₃ :=
  .step step₀₁ (.step step₁₂ (.single step₂₃))

example : h₀.id = h₃.id := lifecycle.id_eq
example : Satisfies ev .empty [] idNat S₀ :=
  lifecycle.final_realization_satisfies_all (WellFormedHole.unresolved ev _ [] hid S₀) rfl
example : Satisfies ev .empty [] constZero S₁ := by decide
example : ¬ Satisfies ev .empty [] constZero S₂ := by decide

/-- A. Type-changing "refinement" breaks Theorem 5. -/
def LooseRefines (old new : Spec) : Prop := old.obligations ⊆ new.obligations

theorem loose_breaks_theorem5 :
    ¬ ∀ (ev : Evidence) (Δ : HoleEnv) (Γ : Ctx) (e : Expr) (S₀ S₁ : Spec),
        LooseRefines S₀ S₁ → Satisfies ev Δ Γ e S₁ → Satisfies ev Δ Γ e S₀ := by
  intro h
  have hs := h (fun _ _ _ => True) .empty [] (.boolLit true) ⟨.nat, []⟩ ⟨.bool, []⟩
    (List.Subset.refl _) ⟨.boolLit, fun _ _ => trivial⟩
  exact absurd hs.1 (by decide)

/-- B. Obligation-dropping "refinement" breaks Theorem 5. -/
def ForgetfulRefines (old new : Spec) : Prop := old.expectedType = new.expectedType

theorem forgetful_breaks_theorem5 :
    ¬ ∀ (ev : Evidence) (Δ : HoleEnv) (Γ : Ctx) (e : Expr) (S₀ S₁ : Spec),
        ForgetfulRefines S₀ S₁ → Satisfies ev Δ Γ e S₁ → Satisfies ev Δ Γ e S₀ := by
  intro h
  have hs := h (fun _ _ _ => False) .empty [] (.natLit 7) ⟨.nat, [.bounded]⟩ ⟨.nat, []⟩
    rfl ⟨.natLit, fun _ hp => nomatch hp⟩
  exact hs.2 .bounded (List.mem_singleton.mpr rfl)

/-- D. Strengthening a realized hole without re-verification breaks Theorem 4. -/
inductive NaiveHoleRefines (ev : Evidence) (Δ : HoleEnv) (Γ : Ctx) : DesignHole → DesignHole → Prop where
  | refine {id S S'} (h : Refines S S') :
      NaiveHoleRefines ev Δ Γ ⟨id, S, none⟩ ⟨id, S', none⟩
  | realize {id S e} (hs : Satisfies ev Δ Γ e S) :
      NaiveHoleRefines ev Δ Γ ⟨id, S, none⟩ ⟨id, S, some e⟩
  | strengthen {id S S' e} (h : Refines S S') :
      NaiveHoleRefines ev Δ Γ ⟨id, S, some e⟩ ⟨id, S', some e⟩

theorem naive_breaks_wellformedness :
    ¬ ∀ (h₁ h₂ : DesignHole),
        WellFormedHole ev .empty [] h₁ → NaiveHoleRefines ev .empty [] h₁ h₂ →
        WellFormedHole ev .empty [] h₂ := by
  intro h
  have wf₁ : WellFormedHole ev .empty [] ⟨hid, S₁, some constZero⟩ := by decide
  have step : NaiveHoleRefines ev .empty [] ⟨hid, S₁, some constZero⟩ ⟨hid, S₂, some constZero⟩ :=
    .strengthen (Refines_addObligation S₁ .monotone)
  exact absurd (h _ _ wf₁ step) (by decide)

example : SpecEquiv ⟨.nat, [.total, .total]⟩ ⟨.nat, [.total]⟩ ∧
    (⟨.nat, [.total, .total]⟩ : Spec) ≠ ⟨.nat, [.total]⟩ := by decide

/-! ## Part 1 — cross-hole references

    A : nat → bool          A := λx. f (B x)      f := λy. true : nat → bool
    B : nat → nat           B unresolved
-/

def A : HoleId := ⟨10⟩
def B : HoleId := ⟨11⟩

def f  : Expr := .lam .nat (.boolLit true)
def eA : Expr := .lam .nat (.app f (.app (.holeRef B) (.var 0)))

def specA : Spec := ⟨.arr .nat .bool, []⟩
def specB : Spec := ⟨.arr .nat .nat, []⟩

def hA  : DesignHole := ⟨A, specA, some eA⟩
def hB₀ : DesignHole := .unresolved B specB

/-- The initial design: `A` realized in terms of the still-unresolved `B`. -/
def Δ₀ : HoleEnv := .ofList [hA, hB₀]

/-- `A` types against `B`'s *signature*; it cannot type without `B` declared. -/
example : HasType Δ₀ [] eA (.arr .nat .bool) := by decide
example : ¬ HasType .empty [] eA (.arr .nat .bool) := by decide

theorem Δ₀_wf : GlobalWF ev Δ₀ := GlobalWF.ofList (by decide)
theorem Δ₀_B : Δ₀ hB₀.id = some hB₀ := by decide

/-- Which holes `A` depends on, as a finite graph. -/
example : depEdges [hA, hB₀] = [(A, B)] := by decide
example : DependsOn Δ₀ A B ∧ ¬ DependsOn Δ₀ B A := by decide

/-! ### Probe 1 — strengthen `B`'s specification -/

def hB₁ : DesignHole := .unresolved B (specB.addObligation .monotone)

theorem probe1_step : HoleRefines ev Δ₀ [] hB₀ hB₁ := .refine (by decide)

/-- `A` is untouched and still well typed, by the theorem … -/
theorem probe1_typing : HasType (Δ₀.update hB₁) [] eA (.arr .nat .bool) :=
  local_refinement_preserves_global_typing Δ₀_B probe1_step.toLeq (by decide)

/-- … and the whole design is still well formed. -/
theorem probe1_wf : GlobalWF ev (Δ₀.update hB₁) :=
  local_refinement_preserves_global_wf ev_mono Δ₀_wf Δ₀_B probe1_step

/-! ### Probe 2 — realize `B` -/

def hB₂ : DesignHole := ⟨B, specB.addObligation .monotone, some idNat⟩

theorem probe2_step : HoleRefines ev Δ₀ [] hB₁ hB₂ := .realize (by decide)

theorem probe2_lifecycle : HoleRefinesStar ev Δ₀ [] hB₀ hB₂ := .of_two probe1_step probe2_step

theorem probe2_wf : GlobalWF ev (Δ₀.update hB₂) :=
  local_lifecycle_preserves_global_wf ev_mono Δ₀_wf Δ₀_B probe2_lifecycle

/-- After realization `A` unfolds to a hole-free program … -/
def eA_flat : Expr := .lam .nat (.app f (.app idNat (.var 0)))

theorem probe2_unfolds : Unfolds (Δ₀.update hB₂) eA eA_flat :=
  .lam (.app (.lam (.boolLit _)) (.app (.refRealized (by decide) (.lam (.var 0))) (.var 0)))

example : eA_flat.HoleFree := by decide

/-- … of the same type, now independent of any environment. -/
example : HasType .empty [] eA_flat (.arr .nat .bool) :=
  (probe2_unfolds.preserves_typing probe2_wf
    (local_refinement_preserves_global_typing Δ₀_B probe2_lifecycle.toLeq (by decide)))
    |>.holeFree_env_irrelevant (by decide)

/-- Before realization, unfolding is stuck at `B`: the design is well typed
    but not executable.  ("Well-typed partial" vs "executable".) -/
theorem probe0_stuck : Unfolds Δ₀ eA eA :=
  .lam (.app (.lam (.boolLit _)) (.app (.refStuck (by decide)) (.var 0)))

/-! ### Probe 3 — re-identify `B` on realization

Realization mints a fresh id `B'` instead of keeping `B`. -/

def B' : HoleId := ⟨12⟩
def hB' : DesignHole := ⟨B', specB, some idNat⟩

/-- (a) If `B'` *replaces* `B`, `A` — unchanged — is no longer well typed:
    it has a dangling reference. -/
def Δ₃a : HoleEnv := .ofList [hA, hB']

theorem probe3a_breaks_typing : ¬ HasType Δ₃a [] eA (.arr .nat .bool) := by decide

/-- (b) If `B'` is added *beside* `B`, `A` types, but it still depends on the
    stale unresolved `B`, never on the realized `B'`: the realization is
    invisible to every client, and the design can never become executable
    without editing `A`. -/
def Δ₃b : HoleEnv := .ofList [hA, hB₀, hB']

example : HasType Δ₃b [] eA (.arr .nat .bool) := by decide
theorem probe3b_stale : DependsOn Δ₃b A B ∧ ¬ DependsOn Δ₃b A B' := by decide
theorem probe3b_stuck : Unfolds Δ₃b eA eA :=
  .lam (.app (.lam (.boolLit _)) (.app (.refStuck (by decide)) (.var 0)))
theorem probe3b_not_executable : ¬ Δ₃b.FullyRealized := by
  intro fr
  obtain ⟨e, he⟩ := fr B hB₀ (by decide)
  exact nomatch he

/-! ### Probe 4 — change `B`'s expected type (id preserved) -/

def hB₄ : DesignHole := .unresolved B ⟨.arr .nat .bool, []⟩

/-- Not a structural step, so the preservation theorem does not apply … -/
example : ¬ HoleLeq hB₀ hB₄ := by decide

/-- … and indeed `A` breaks. -/
theorem probe4_breaks_typing : ¬ HasType (Δ₀.update hB₄) [] eA (.arr .nat .bool) := by decide

/-- The theorem's `HoleLeq` hypothesis cannot be weakened to "same id":
    identity alone does not protect clients. -/
theorem probe4_id_alone_insufficient :
    ¬ ∀ (Δ : HoleEnv) (h h' : DesignHole), Δ h.id = some h → h.id = h'.id →
        ∀ Γ e τ, HasType Δ Γ e τ → HasType (Δ.update h') Γ e τ := by
  intro H
  exact probe4_breaks_typing (H Δ₀ hB₀ hB₄ Δ₀_B rfl [] eA _ (by decide))

/-- Re-typing kills every existing client reference, by uniqueness of typing:
    a reference that had type `τ` cannot have it once the hole's expected type
    is `τ' ≠ τ`. -/
theorem retype_kills_ref {Δ' : HoleEnv} {Γ : Ctx} {x : HoleId} {τ τ' : Ty}
    (h' : Δ'.tyView x = some τ') (hne : τ ≠ τ') :
    ¬ HasType Δ' Γ (.holeRef x) τ :=
  fun h'' => hne (h''.unique (.holeRef h'))

/-! ### Probe 5 — drop an obligation of `B`

Typing is *not* affected (the type view is unchanged) — which is exactly why
this failure is dangerous: nothing in the type system notices. -/

def hB₅ : DesignHole := .unresolved B specB   -- `monotone` forgotten again

theorem probe5_typing_kept : HasType ((Δ₀.update hB₁).update hB₅) [] eA (.arr .nat .bool) := by
  decide

/-- The hole through which `λx. (λy. c) (h x)` is monotone, if the term has
    that shape. -/
def monoVia : Expr → Option HoleId
  | .lam _ (.app (.lam _ (.boolLit _)) (.app (.holeRef h) (.var 0))) => some h
  | _ => none

def isIdNat : Expr → Bool
  | .lam .nat (.var 0) => true
  | _ => false

/-- Compositional evidence: `λx. (λy. c) (h x)` is monotone whenever `h` is
    *committed* to be monotone (a constant is monotone); the identity is
    monotone; lambdas are total.  It consults only the presence of
    obligations, so it is monotone under environment refinement. -/
def compEvB (Δ : HoleEnv) (e : Expr) : PropertyId → Bool
  | .monotone =>
    (match monoVia e with
     | some h => (Δ h).any fun dh => decide (PropertyId.monotone ∈ dh.spec.obligations)
     | none => false) || isIdNat e
  | .total => match e with | .lam _ _ => true | _ => false
  | .bounded => false

def compEv : Evidence := fun Δ e p => compEvB Δ e p = true

instance : ∀ Δ e p, Decidable (compEv Δ e p) :=
  fun Δ e p => inferInstanceAs (Decidable (compEvB Δ e p = true))

theorem compEv_mono : compEv.Monotone := by
  intro Δ₁ Δ₂ e p er h
  unfold compEv at *
  cases p with
  | total => exact h
  | bounded => exact h
  | monotone =>
    simp only [compEvB, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · left
      cases hw : monoVia e with
      | none => simp [hw] at h
      | some x =>
        rw [hw] at h
        cases hx : Δ₁ x with
        | none => simp [hx] at h
        | some dh =>
          obtain ⟨dh₂, hx₂, le⟩ := er x dh hx
          simp [hx] at h
          simp [hx₂]
          exact le.spec_refines.obligations_subset h
    · right; exact h

/-- `A` committed to `monotone`, discharged compositionally through `B`'s commitment. -/
def hA_mon  : DesignHole := ⟨A, specA.addObligation .monotone, some eA⟩
def hB_mon  : DesignHole := .unresolved B (specB.addObligation .monotone)
def Δ₅      : HoleEnv := .ofList [hA_mon, hB_mon]

theorem Δ₅_wf : GlobalWF compEv Δ₅ := GlobalWF.ofList (by decide)

/-- Forget `B`'s `monotone`.  `A`'s text and `A`'s type are untouched … -/
def Δ₅' : HoleEnv := .ofList [hA_mon, .unresolved B specB]

example : HasType Δ₅' [] eA (.arr .nat .bool) := by decide

/-- … but `A`'s commitment is now unsupported.  A design-level commitment of
    a *client* was silently invalidated by editing a *dependency*. -/
theorem probe5_breaks_commitment : ¬ WellFormedHole compEv Δ₅' [] hA_mon := by decide

theorem probe5_not_globally_wf : ¬ GlobalWF compEv Δ₅' :=
  fun g => probe5_breaks_commitment (g.wellFormed (by decide : Δ₅' A = some hA_mon))

/-! ### Probe 6 — non-monotone evidence

The preservation theorem assumes `Evidence.Monotone`.  Here is why: evidence
that consults the *absence* of information ("`A` is total while `B` is
unresolved") is destroyed by a perfectly valid realization of `B`. -/

def badEv : Evidence := fun Δ e p => p = .total ∧ e = eA ∧ Δ.realizationOf B = none

instance : ∀ Δ e p, Decidable (badEv Δ e p) := fun Δ e p =>
  inferInstanceAs (Decidable (p = .total ∧ e = eA ∧ Δ.realizationOf B = none))

def hA_tot : DesignHole := ⟨A, specA.addObligation .total, some eA⟩
def Δ₆ : HoleEnv := .ofList [hA_tot, hB₀]
def hB₆ : DesignHole := ⟨B, specB, some idNat⟩

theorem Δ₆_wf : GlobalWF badEv Δ₆ := GlobalWF.ofList (by decide)
theorem probe6_step : HoleRefines badEv Δ₆ [] hB₀ hB₆ := .realize (by decide)

theorem probe6_breaks : ¬ GlobalWF badEv (Δ₆.update hB₆) :=
  fun g => absurd (g.wellFormed (by decide : (Δ₆.update hB₆) A = some hA_tot)) (by decide)

/-- Hence `badEv` is not monotone (otherwise the theorem would apply), and the
    monotonicity hypothesis is necessary, not decorative. -/
theorem badEv_not_mono : ¬ badEv.Monotone :=
  fun mono => probe6_breaks (local_refinement_preserves_global_wf mono Δ₆_wf (by decide) probe6_step)

/-! ## Part 2 — cycles -/

/-- Self-reference: `S := S`.  Well typed — the reference is typed by the
    signature — but it has no unfolding. -/
def S : HoleId := ⟨20⟩
def hS : DesignHole := ⟨S, ⟨.nat, []⟩, some (.holeRef S)⟩
def Δself : HoleEnv := .ofList [hS]

theorem self_wf : GlobalWF ev Δself := GlobalWF.ofList (by decide)
theorem self_cyclic : Reaches Δself S S := .single (by decide)
theorem self_no_unfolding : ¬ ∃ e', Unfolds Δself (.holeRef S) e' :=
  Unfolds.not_of_cyclic self_cyclic

/-- Mutual recursion: `P := Q`, `Q := P`.  Same. -/
def P : HoleId := ⟨21⟩
def Q : HoleId := ⟨22⟩
def Δmut : HoleEnv := .ofList [⟨P, ⟨.nat, []⟩, some (.holeRef Q)⟩, ⟨Q, ⟨.nat, []⟩, some (.holeRef P)⟩]

theorem mut_wf : GlobalWF ev Δmut := GlobalWF.ofList (by decide)
theorem mut_cyclic : Reaches Δmut P P := ⟨Q, by decide, .single (by decide)⟩
theorem mut_no_unfolding : ¬ ∃ e', Unfolds Δmut (.holeRef P) e' :=
  Unfolds.not_of_cyclic mut_cyclic

/-- The realized design of probes 1–2 is acyclic (rank `A` above `B`), hence
    every term over it unfolds. -/
theorem probe2_acyclic : Acyclic (Δ₀.update hB₂) := by
  refine ⟨fun x => if x = A then 1 else 0, ?_⟩
  intro a b hab
  obtain ⟨e, he, hb⟩ := DependsOn.iff.mp hab
  simp only [HoleEnv.realizationOf, Option.bind_eq_some_iff] at he
  obtain ⟨dh, hdh, hre⟩ := he
  simp only [HoleEnv.update] at hdh
  split at hdh
  · -- a = B: its realization `idNat` refers to nothing
    cases hdh
    simp [hB₂] at hre
    subst hre
    simp [idNat, Expr.refs] at hb
  · -- a is looked up in Δ₀
    obtain ⟨hmem, hid⟩ := HoleEnv.ofList_some hdh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · -- a = A, e = eA, so b = B
      simp [hA] at hre
      subst hre
      have hbB : b = B := by simpa [eA, f, Expr.refs] using hb
      subst hbB
      subst hid
      decide
    · -- B is unresolved in Δ₀
      simp [hB₀, DesignHole.unresolved] at hre

example : ∃ e', Unfolds (Δ₀.update hB₂) eA e' := Unfolds.exists_of_acyclic probe2_acyclic eA

end BDL.Experiments
