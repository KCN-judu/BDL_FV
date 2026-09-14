import BDL.Core.Dependency

/-!
# Experiments — declarations, cross-declaration references, and their counterexamples

Part 0 — Phase-0 examples and counterexamples, ported (environment `.empty`).

Part 1 — the Phase-1 probes.  `A := λx. f (B x)` is realized while `B` is
still unresolved.  We then do each of the five things to `B` and watch `A`:

| probe                     | typing of A | commitments of A | theorem / counterexample |
|---------------------------|-------------|------------------|--------------------------|
| 1 strengthen B's interface| kept        | kept             | `probe1_*`               |
| 2 realize B               | kept        | kept             | `probe2_*`               |
| 3 re-identify B           | **broken**  | —                | `probe3_*`               |
| 4 change B's type         | **broken**  | —                | `probe4_*`               |
| 5 drop B's commitment     | kept        | **broken**       | `probe5_*`               |
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

def dId : DeclId := ⟨0⟩
def S₀ : DeclInterface := ⟨.arr .nat .nat, []⟩
def S₁ : DeclInterface := S₀.addCommitment .total
def S₂ : DeclInterface := S₁.addCommitment .monotone
def idNat : Expr := .lam .nat (.var 0)
def constZero : Expr := .lam .nat (.natLit 0)

def h₀ : DesignDecl := .unresolved dId S₀
def h₁ : DesignDecl := .unresolved dId S₁
def h₂ : DesignDecl := .unresolved dId S₂
def h₃ : DesignDecl := ⟨dId, S₂, some idNat⟩

theorem step₀₁ : DeclRefines ev ConceptEnv.empty .empty [] h₀ h₁ := .refine (by decide)
theorem step₁₂ : DeclRefines ev ConceptEnv.empty .empty [] h₁ h₂ := .refine (by decide)
theorem step₂₃ : DeclRefines ev ConceptEnv.empty .empty [] h₂ h₃ := .realize (by decide)
theorem lifecycle : DeclRefinesStar ev ConceptEnv.empty .empty [] h₀ h₃ :=
  .step step₀₁ (.step step₁₂ (.single step₂₃))

example : h₀.id = h₃.id := lifecycle.id_eq
example : Satisfies ev ConceptEnv.empty .empty [] idNat S₀ :=
  lifecycle.final_realization_satisfies_all (WellFormedDecl.unresolved ev _ _ [] dId S₀) rfl
example : Satisfies ev ConceptEnv.empty .empty [] constZero S₁ := by decide
example : ¬ Satisfies ev ConceptEnv.empty .empty [] constZero S₂ := by decide

/-- A. Type-changing "refinement" breaks Theorem 5. -/
def LooseRefines (old new : DeclInterface) : Prop := old.commitments ⊆ new.commitments

theorem loose_breaks_theorem5 :
    ¬ ∀ (ev : Evidence) (Δ : DeclEnv) (Γ : Ctx) (e : Expr) (S₀ S₁ : DeclInterface),
        LooseRefines S₀ S₁ → Satisfies ev ConceptEnv.empty Δ Γ e S₁ → Satisfies ev ConceptEnv.empty Δ Γ e S₀ := by
  intro h
  have hs := h (fun _ _ _ => True) .empty [] (.boolLit true) ⟨.nat, []⟩ ⟨.bool, []⟩
    (List.Subset.refl _) ⟨.boolLit, fun _ _ => trivial⟩
  exact absurd hs.1 (by decide)

/-- B. Commitment-dropping "refinement" breaks Theorem 5. -/
def ForgetfulRefines (old new : DeclInterface) : Prop := old.expectedType = new.expectedType

theorem forgetful_breaks_theorem5 :
    ¬ ∀ (ev : Evidence) (Δ : DeclEnv) (Γ : Ctx) (e : Expr) (S₀ S₁ : DeclInterface),
        ForgetfulRefines S₀ S₁ → Satisfies ev ConceptEnv.empty Δ Γ e S₁ → Satisfies ev ConceptEnv.empty Δ Γ e S₀ := by
  intro h
  have hs := h (fun _ _ _ => False) .empty [] (.natLit 7) ⟨.nat, [.bounded]⟩ ⟨.nat, []⟩
    rfl ⟨.natLit, fun _ hp => nomatch hp⟩
  exact hs.2 .bounded (List.mem_singleton.mpr rfl)

/-- D. Strengthening a realized declaration without re-verification breaks Theorem 4. -/
inductive NaiveDeclRefines (ev : Evidence) (Θ : ConceptEnv) (Δ : DeclEnv) (Γ : Ctx) : DesignDecl → DesignDecl → Prop where
  | refine {id S S'} (h : InterfaceRefines S S') :
      NaiveDeclRefines ev Θ Δ Γ ⟨id, S, none⟩ ⟨id, S', none⟩
  | realize {id S e} (hs : Satisfies ev Θ Δ Γ e S) :
      NaiveDeclRefines ev Θ Δ Γ ⟨id, S, none⟩ ⟨id, S, some e⟩
  | strengthen {id S S' e} (h : InterfaceRefines S S') :
      NaiveDeclRefines ev Θ Δ Γ ⟨id, S, some e⟩ ⟨id, S', some e⟩

theorem naive_breaks_wellformedness :
    ¬ ∀ (h₁ h₂ : DesignDecl),
        WellFormedDecl ev ConceptEnv.empty .empty [] h₁ → NaiveDeclRefines ev ConceptEnv.empty .empty [] h₁ h₂ →
        WellFormedDecl ev ConceptEnv.empty .empty [] h₂ := by
  intro h
  have wf₁ : WellFormedDecl ev ConceptEnv.empty .empty [] ⟨dId, S₁, some constZero⟩ := by decide
  have step : NaiveDeclRefines ev ConceptEnv.empty .empty [] ⟨dId, S₁, some constZero⟩ ⟨dId, S₂, some constZero⟩ :=
    .strengthen (InterfaceRefines_addCommitment S₁ .monotone)
  exact absurd (h _ _ wf₁ step) (by decide)

example : InterfaceEquiv ⟨.nat, [.total, .total]⟩ ⟨.nat, [.total]⟩ ∧
    (⟨.nat, [.total, .total]⟩ : DeclInterface) ≠ ⟨.nat, [.total]⟩ := by decide

/-! ## Part 1 — cross-declaration references

    A : nat → bool          A := λx. f (B x)      f := λy. true : nat → bool
    B : nat → nat           B unresolved
-/

def A : DeclId := ⟨10⟩
def B : DeclId := ⟨11⟩

def f  : Expr := .lam .nat (.boolLit true)
def eA : Expr := .lam .nat (.app f (.app (.declRef B) (.var 0)))

def specA : DeclInterface := ⟨.arr .nat .bool, []⟩
def specB : DeclInterface := ⟨.arr .nat .nat, []⟩

def dA  : DesignDecl := ⟨A, specA, some eA⟩
def hB₀ : DesignDecl := .unresolved B specB

/-- The initial design: `A` realized in terms of the still-unresolved `B`. -/
def Δ₀ : DeclEnv := .ofList [dA, hB₀]

/-- `A` types against `B`'s *signature*; it cannot type without `B` declared. -/
example : HasType ConceptEnv.empty Δ₀ Grant.none [] eA (.arr .nat .bool) := by decide
example : ¬ HasType ConceptEnv.empty .empty Grant.none [] eA (.arr .nat .bool) := by decide

theorem Δ₀_wf : GlobalWF ev ConceptEnv.empty Δ₀ := GlobalWF.ofList (by decide)
theorem Δ₀_B : Δ₀ hB₀.id = some hB₀ := by decide

/-- Which declarations `A` depends on, as a finite graph. -/
example : depEdges [dA, hB₀] = [(A, B)] := by decide
example : DependsOn Δ₀ A B ∧ ¬ DependsOn Δ₀ B A := by decide

/-! ### Probe 1 — strengthen `B`'s specification -/

def hB₁ : DesignDecl := .unresolved B (specB.addCommitment .monotone)

theorem probe1_step : DeclRefines ev ConceptEnv.empty Δ₀ [] hB₀ hB₁ := .refine (by decide)

/-- `A` is untouched and still well typed, by the theorem … -/
theorem probe1_typing : HasType ConceptEnv.empty (Δ₀.update hB₁) Grant.none [] eA (.arr .nat .bool) :=
  local_refinement_preserves_global_typing Δ₀_B probe1_step.toLeq (by decide)

/-- … and the whole design is still well formed. -/
theorem probe1_wf : GlobalWF ev ConceptEnv.empty (Δ₀.update hB₁) :=
  local_refinement_preserves_global_wf ev_mono Δ₀_wf Δ₀_B probe1_step

/-! ### Probe 2 — realize `B` -/

def hB₂ : DesignDecl := ⟨B, specB.addCommitment .monotone, some idNat⟩

theorem probe2_step : DeclRefines ev ConceptEnv.empty Δ₀ [] hB₁ hB₂ := .realize (by decide)

theorem probe2_lifecycle : DeclRefinesStar ev ConceptEnv.empty Δ₀ [] hB₀ hB₂ := .of_two probe1_step probe2_step

theorem probe2_wf : GlobalWF ev ConceptEnv.empty (Δ₀.update hB₂) :=
  local_lifecycle_preserves_global_wf ev_mono Δ₀_wf Δ₀_B probe2_lifecycle

/-- After realization `A` unfolds to a reference-free program … -/
def eA_flat : Expr := .lam .nat (.app f (.app idNat (.var 0)))

theorem probe2_unfolds : Unfolds (Δ₀.update hB₂) eA eA_flat :=
  .lam (.app (.lam (.boolLit _)) (.app (.refRealized (by decide) (.lam (.var 0))) (.var 0)))

example : eA_flat.RefFree := by decide

/-- … of the same type, now independent of any environment. -/
example : HasType ConceptEnv.empty .empty Grant.all [] eA_flat (.arr .nat .bool) :=
  (probe2_unfolds.preserves_typing probe2_wf
    (DeclEnv.DelayFree.ofList_update (by decide))
    (local_refinement_preserves_global_typing (G := Grant.none) Δ₀_B probe2_lifecycle.toLeq (by decide)))
    |>.refFree_env_irrelevant (by decide)
where
  DeclEnv.DelayFree.ofList_update {l : List DesignDecl} {h : DesignDecl}
      (hall : ∀ dh ∈ h :: l, ∀ e, dh.realization = some e → e.DelayFree) :
      DeclEnv.DelayFree ((DeclEnv.ofList l).update h) := by
    intro d e he
    simp only [DeclEnv.realizationOf, DeclEnv.update, Option.bind_eq_some_iff] at he
    obtain ⟨dh, hdh, hre⟩ := he
    split at hdh
    · cases hdh; exact hall _ (List.mem_cons_self) e hre
    · exact hall _ (List.mem_cons_of_mem _ (DeclEnv.ofList_some hdh).1) e hre

/-- Before realization, unfolding is stuck at `B`: the design is well typed
    but not executable.  ("Well-typed partial" vs "executable".) -/
theorem probe0_stuck : Unfolds Δ₀ eA eA :=
  .lam (.app (.lam (.boolLit _)) (.app (.refStuck (by decide)) (.var 0)))

/-! ### Probe 3 — re-identify `B` on realization

Realization mints a fresh id `B'` instead of keeping `B`. -/

def B' : DeclId := ⟨12⟩
def hB' : DesignDecl := ⟨B', specB, some idNat⟩

/-- (a) If `B'` *replaces* `B`, `A` — unchanged — is no longer well typed:
    it has a dangling reference. -/
def Δ₃a : DeclEnv := .ofList [dA, hB']

theorem probe3a_breaks_typing : ¬ HasType ConceptEnv.empty Δ₃a Grant.none [] eA (.arr .nat .bool) := by decide

/-- (b) If `B'` is added *beside* `B`, `A` types, but it still depends on the
    stale unresolved `B`, never on the realized `B'`: the realization is
    invisible to every client, and the design can never become executable
    without editing `A`. -/
def Δ₃b : DeclEnv := .ofList [dA, hB₀, hB']

example : HasType ConceptEnv.empty Δ₃b Grant.none [] eA (.arr .nat .bool) := by decide
theorem probe3b_stale : DependsOn Δ₃b A B ∧ ¬ DependsOn Δ₃b A B' := by decide
theorem probe3b_stuck : Unfolds Δ₃b eA eA :=
  .lam (.app (.lam (.boolLit _)) (.app (.refStuck (by decide)) (.var 0)))
theorem probe3b_not_executable : ¬ Δ₃b.FullyRealized := by
  intro fr
  obtain ⟨e, he⟩ := fr B hB₀ (by decide)
  exact nomatch he

/-! ### Probe 4 — change `B`'s expected type (id preserved) -/

def hB₄ : DesignDecl := .unresolved B ⟨.arr .nat .bool, []⟩

/-- Not a structural step, so the preservation theorem does not apply … -/
example : ¬ DeclLeq hB₀ hB₄ := by decide

/-- … and indeed `A` breaks. -/
theorem probe4_breaks_typing : ¬ HasType ConceptEnv.empty (Δ₀.update hB₄) Grant.none [] eA (.arr .nat .bool) := by decide

/-- The theorem's `DeclLeq` hypothesis cannot be weakened to "same id":
    identity alone does not protect clients. -/
theorem probe4_id_alone_insufficient :
    ¬ ∀ (Δ : DeclEnv) (h h' : DesignDecl), Δ h.id = some h → h.id = h'.id →
        ∀ Γ e τ, HasType ConceptEnv.empty Δ Grant.none Γ e τ → HasType ConceptEnv.empty (Δ.update h') Grant.none Γ e τ := by
  intro H
  exact probe4_breaks_typing (H Δ₀ hB₀ hB₄ Δ₀_B rfl [] eA _ (by decide))

/-- Re-typing kills every existing client reference, by uniqueness of typing:
    a reference that had type `τ` cannot have it once the declaration's expected type
    is `τ' ≠ τ`. -/
theorem retype_kills_ref {Δ' : DeclEnv} {Γ : Ctx} {x : DeclId} {τ τ' : Ty}
    (h' : Δ'.tyView x = some τ') (hne : τ ≠ τ') :
    ¬ HasType ConceptEnv.empty Δ' Grant.none Γ (.declRef x) τ :=
  fun h'' => hne (h''.unique (.declRef h'))

/-! ### Probe 5 — drop a commitment of `B`

Typing is *not* affected (the type view is unchanged) — which is exactly why
this failure is dangerous: nothing in the type system notices. -/

def hB₅ : DesignDecl := .unresolved B specB   -- `monotone` forgotten again

theorem probe5_typing_kept : HasType ConceptEnv.empty ((Δ₀.update hB₁).update hB₅) Grant.none [] eA (.arr .nat .bool) := by
  decide

/-- The declaration through which `λx. (λy. c) (h x)` is monotone, if the term has
    that shape. -/
def monoVia : Expr → Option DeclId
  | .lam _ (.app (.lam _ (.boolLit _)) (.app (.declRef h) (.var 0))) => some h
  | _ => none

def isIdNat : Expr → Bool
  | .lam .nat (.var 0) => true
  | _ => false

/-- Compositional evidence: `λx. (λy. c) (h x)` is monotone whenever `h` is
    *committed* to be monotone (a constant is monotone); the identity is
    monotone; lambdas are total.  It consults only the presence of
    commitments, so it is monotone under environment refinement. -/
def compEvB (Δ : DeclEnv) (e : Expr) : PropertyId → Bool
  | .monotone =>
    (match monoVia e with
     | some h => (Δ h).any fun dh => decide (PropertyId.monotone ∈ dh.interface.commitments)
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
          exact le.interface_refines.commitments_subset h
    · right; exact h

/-- `A` committed to `monotone`, discharged compositionally through `B`'s commitment. -/
def dA_mon  : DesignDecl := ⟨A, specA.addCommitment .monotone, some eA⟩
def dB_mon  : DesignDecl := .unresolved B (specB.addCommitment .monotone)
def Δ₅      : DeclEnv := .ofList [dA_mon, dB_mon]

theorem Δ₅_wf : GlobalWF compEv ConceptEnv.empty Δ₅ := GlobalWF.ofList (by decide)

/-- Forget `B`'s `monotone`.  `A`'s text and `A`'s type are untouched … -/
def Δ₅' : DeclEnv := .ofList [dA_mon, .unresolved B specB]

example : HasType ConceptEnv.empty Δ₅' Grant.none [] eA (.arr .nat .bool) := by decide

/-- … but `A`'s commitment is now unsupported.  A design-level commitment of
    a *client* was silently invalidated by editing a *dependency*. -/
theorem probe5_breaks_commitment : ¬ WellFormedDecl compEv ConceptEnv.empty Δ₅' [] dA_mon := by decide

theorem probe5_not_globally_wf : ¬ GlobalWF compEv ConceptEnv.empty Δ₅' :=
  fun g => probe5_breaks_commitment (g.wellFormed (by decide : Δ₅' A = some dA_mon))

/-! ### Probe 6 — non-monotone evidence

The preservation theorem assumes `Evidence.Monotone`.  Here is why: evidence
that consults the *absence* of information ("`A` is total while `B` is
unresolved") is destroyed by a perfectly valid realization of `B`. -/

def badEv : Evidence := fun Δ e p => p = .total ∧ e = eA ∧ Δ.realizationOf B = none

instance : ∀ Δ e p, Decidable (badEv Δ e p) := fun Δ e p =>
  inferInstanceAs (Decidable (p = .total ∧ e = eA ∧ Δ.realizationOf B = none))

def dA_tot : DesignDecl := ⟨A, specA.addCommitment .total, some eA⟩
def Δ₆ : DeclEnv := .ofList [dA_tot, hB₀]
def hB₆ : DesignDecl := ⟨B, specB, some idNat⟩

theorem Δ₆_wf : GlobalWF badEv ConceptEnv.empty Δ₆ := GlobalWF.ofList (by decide)
theorem probe6_step : DeclRefines badEv ConceptEnv.empty Δ₆ [] hB₀ hB₆ := .realize (by decide)

theorem probe6_breaks : ¬ GlobalWF badEv ConceptEnv.empty (Δ₆.update hB₆) :=
  fun g => absurd (g.wellFormed (by decide : (Δ₆.update hB₆) A = some dA_tot)) (by decide)

/-- Hence `badEv` is not monotone (otherwise the theorem would apply), and the
    monotonicity hypothesis is necessary, not decorative. -/
theorem badEv_not_mono : ¬ badEv.Monotone :=
  fun mono => probe6_breaks (local_refinement_preserves_global_wf mono Δ₆_wf (by decide) probe6_step)

/-! ## Part 2 — cycles -/

/-- Self-reference: `S := S`.  Well typed — the reference is typed by the
    signature — but it has no unfolding. -/
def S : DeclId := ⟨20⟩
def dS : DesignDecl := ⟨S, ⟨.nat, []⟩, some (.declRef S)⟩
def Δself : DeclEnv := .ofList [dS]

theorem self_wf : GlobalWF ev ConceptEnv.empty Δself := GlobalWF.ofList (by decide)
theorem self_cyclic : Reaches Δself S S := .single (by decide)
theorem self_no_unfolding : ¬ ∃ e', Unfolds Δself (.declRef S) e' :=
  Unfolds.not_of_cyclic self_cyclic

/-- Mutual recursion: `P := Q`, `Q := P`.  Same. -/
def P : DeclId := ⟨21⟩
def Q : DeclId := ⟨22⟩
def Δmut : DeclEnv := .ofList [⟨P, ⟨.nat, []⟩, some (.declRef Q)⟩, ⟨Q, ⟨.nat, []⟩, some (.declRef P)⟩]

theorem mut_wf : GlobalWF ev ConceptEnv.empty Δmut := GlobalWF.ofList (by decide)
theorem mut_cyclic : Reaches Δmut P P := ⟨Q, by decide, .single (by decide)⟩
theorem mut_no_unfolding : ¬ ∃ e', Unfolds Δmut (.declRef P) e' :=
  Unfolds.not_of_cyclic mut_cyclic

/-- The realized design of probes 1–2 is acyclic (rank `A` above `B`), hence
    every term over it unfolds. -/
theorem probe2_acyclic : Acyclic (Δ₀.update hB₂) := by
  refine ⟨fun x => if x = A then 1 else 0, ?_⟩
  intro a b hab
  obtain ⟨e, he, hb⟩ := DependsOn.iff.mp hab
  simp only [DeclEnv.realizationOf, Option.bind_eq_some_iff] at he
  obtain ⟨dh, hdh, hre⟩ := he
  simp only [DeclEnv.update] at hdh
  split at hdh
  · -- a = B: its realization `idNat` refers to nothing
    cases hdh
    simp [hB₂] at hre
    subst hre
    simp [idNat, Expr.refs] at hb
  · -- a is looked up in Δ₀
    obtain ⟨hmem, dId⟩ := DeclEnv.ofList_some hdh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · -- a = A, e = eA, so b = B
      simp [dA] at hre
      subst hre
      have hbB : b = B := by simpa [eA, f, Expr.refs] using hb
      subst hbB
      subst dId
      decide
    · -- B is unresolved in Δ₀
      simp [hB₀, DesignDecl.unresolved] at hre

example : ∃ e', Unfolds (Δ₀.update hB₂) eA e' := Unfolds.exists_of_acyclic probe2_acyclic eA

end BDL.Experiments
