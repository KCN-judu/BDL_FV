import BDL.Behavior.Preservation

/-!
# Substitution — refining a component preserves the composition

**Theorem (substitutability, §21–22).**  If instance `k` of a well-formed
system is replaced by a component whose interface *refines* the original
(`IfaceRefines`: same required/provided/parameter ports with the same
types and clocks, stronger provided commitments, weaker required ones,
possibly additional open required ports), which realizes its interface,
keeps the same identity partition and concept bindings, and drives no
external sink the original did not, then the system is still well formed.

The statement is structural and evidence-aware: it says nothing about
behavioural equivalence of the two components, only that every binding
that was type-, commitment-, and clock-compatible remains so, and that
every global condition the composition checked still holds.
-/

namespace BDL
open BDL.Output (OutputId OutputSpec)

namespace BehaviorSystem

variable {ev : Evidence} {S : BehaviorSystem}

/-- Replace instance `k`. -/
def replace (S : BehaviorSystem) (k : Nat) (I' : Inst) : BehaviorSystem :=
  { S with insts := S.insts.set k I' }

theorem instAt_replace_self {k : Nat} {I' : Inst} (hk : k < S.insts.length) :
    (S.replace k I').instAt k = some I' := by
  simp [replace, instAt, hk]

theorem instAt_replace_other {k k' : Nat} {I' : Inst} (hne : k ≠ k') :
    (S.replace k I').instAt k' = S.instAt k' := by
  simp [replace, instAt, List.getElem?_set_ne hne]

/-- The conditions under which `I'` may stand in for `I` at position `k`. -/
structure Substitutable (ev : Evidence) (S : BehaviorSystem) (k : Nat) (I I' : Inst) : Prop where
  atk : S.instAt k = some I
  iface : IfaceRefines I.comp.iface I'.comp.iface
  sameκ : I'.κ = I.κ
  sameSem : I'.comp.internalSem = I.comp.internalSem
  sameOut : I'.comp.internalOut = I.comp.internalOut
  sameΘ : I'.comp.design.Θ = I.comp.design.Θ
  realizes : I'.comp.Realizes ev
  width : I'.comp.width ≤ S.W
  sinks : ∀ o spec, I'.comp.design.Ω o = some spec → I'.comp.internalOut o = false →
    o.n < S.W ∧ S.Ωg o = some (OutputSpec.rename (S.ren k I') spec)
  noNewDrives : ∀ d o, I'.comp.design.β d = some o → I'.comp.internalOut o = false → I.comp.design.β d = some o

theorem Substitutable.internalClock_eq {k : Nat} {I I' : Inst} (h : Substitutable ev S k I I') :
    I'.comp.internalClock = I.comp.internalClock := by
  funext c
  simp [BehaviorComponent.internalClock, h.iface.clocks]

theorem Substitutable.ren_eq {k : Nat} {I I' : Inst} (h : Substitutable ev S k I I') :
    S.ren k I' = S.ren k I := by
  simp only [ren, Ren.inst, h.sameκ, h.sameSem, h.sameOut, h.internalClock_eq]

theorem Substitutable.lt_length {k : Nat} {I I' : Inst} (h : Substitutable ev S k I I') : k < S.insts.length := by
  have := h.atk
  simp only [instAt] at this
  exact (List.getElem?_eq_some_iff.mp this).1

/-- The shared-concept environment is unchanged by the substitution. -/
theorem Substitutable.unionΘ_eq {k : Nat} {I I' : Inst} (h : Substitutable ev S k I I') :
    (S.replace k I').unionΘ = S.unionΘ := by
  funext s
  unfold unionΘ
  show (match decode S.W s.n with
    | some (k', n) => match (S.replace k I').instAt k' with
      | some J => if J.comp.internalSem ⟨n⟩ then (J.comp.design.Θ ⟨n⟩).map (Ty.rename ((S.replace k I').ren k' J).s) else none
      | none => none
    | none => S.Θg s) = _
  cases decode S.W s.n with
  | none => rfl
  | some kn =>
    obtain ⟨k', n⟩ := kn
    dsimp only
    by_cases hk : k = k'
    · subst hk
      rw [instAt_replace_self h.lt_length, h.atk]
      have hr : (S.replace k I').ren k I' = S.ren k I := by
        simp only [replace, ren, Ren.inst, h.sameκ, h.sameSem, h.sameOut, h.internalClock_eq]
      dsimp only
      rw [hr, h.sameSem, h.sameΘ]
    · rw [instAt_replace_other hk]; rfl

/-- **Substitutability.**  Replacing an instance by an interface-refining
    component preserves the composition judgment. -/
theorem substitute_composeWF (c : ComposeWF ev S) {k : Nat} {I I' : Inst} (h : Substitutable ev S k I I') :
    ComposeWF ev (S.replace k I') := by
  have hren : (S.replace k I').ren k I' = S.ren k I := by
    simp only [replace, ren, Ren.inst, h.sameκ, h.sameSem, h.sameOut, h.internalClock_eq]
  have hren' : ∀ k' J, (S.replace k I').ren k' J = S.ren k' J := fun _ _ => rfl
  have hdecl : ∀ k' d, (S.replace k I').declOf k' d = S.declOf k' d := fun _ _ => rfl
  refine ⟨c.width, ?_, c.globalsWF, c.globalsBound, ?_, c.dstNodup, ?_⟩
  · -- every instance is still valid
    intro k' J hJ
    by_cases hk : k = k'
    · subst hk
      rw [instAt_replace_self h.lt_length] at hJ
      cases hJ
      obtain ⟨-, -, hκ, hg, -⟩ := c.insts k I h.atk
      refine ⟨h.realizes, h.width, ?_, ?_, ?_⟩
      · intro cc hcc
        rw [h.sameκ]
        exact hκ cc (by rwa [h.internalClock_eq] at hcc)
      · intro s R hs hi
        rw [h.sameΘ] at hs; rw [h.sameSem] at hi
        exact hg s R hs hi
      · intro o spec hΩ hi
        rw [hren]
        exact (h.ren_eq ▸ h.sinks o spec hΩ hi)
    · rw [instAt_replace_other hk] at hJ
      exact c.insts k' J hJ
  · -- every binding is still compatible: ports are looked up through the refined interface
    intro b hb
    obtain ⟨Id, hId, pd, hpd, hpid, hsrc⟩ := c.bindings b hb
    unfold BindingWF
    rw [h.unionΘ_eq]
    -- the destination instance after substitution, and a matching port
    have hdst : ∃ Id' pd', (S.replace k I').instAt b.dstInst = some Id' ∧
        pd' ∈ Id'.comp.iface.required ++ Id'.comp.iface.params ∧ pd'.id = b.dst ∧
        pd'.iface.expectedType = pd.iface.expectedType ∧ pd'.iface.commitments ⊆ pd.iface.commitments ∧
        pd'.clock = pd.clock ∧ (S.replace k I').ren b.dstInst Id' = S.ren b.dstInst Id := by
      by_cases hk : k = b.dstInst
      · subst hk
        have hatk := h.atk; rw [hatk] at hId; cases hId
        have hport : ∃ pd' ∈ I'.comp.iface.required ++ I'.comp.iface.params,
            pd'.id = pd.id ∧ pd'.iface.expectedType = pd.iface.expectedType ∧
            pd'.iface.commitments ⊆ pd.iface.commitments ∧ pd'.clock = pd.clock := by
          rcases List.mem_append.mp hpd with hr | hr
          · obtain ⟨p', hp', e1, e2, e3, e4⟩ := h.iface.required pd hr
            exact ⟨p', List.mem_append_left _ hp', e1, e2, e3, e4⟩
          · obtain ⟨p', hp', e1, e2, e3, e4⟩ := h.iface.params pd hr
            exact ⟨p', List.mem_append_right _ hp', e1, e2, e3, e4⟩
        obtain ⟨pd', hpd', e1, e2, e3, e4⟩ := hport
        exact ⟨I', pd', instAt_replace_self h.lt_length, hpd', e1.trans hpid, e2, e3, e4, hren⟩
      · exact ⟨Id, pd, by rw [instAt_replace_other hk]; exact hId, hpd, hpid, rfl, List.Subset.refl _, rfl, rfl⟩
    obtain ⟨Id', pd', hId', hpd', hpid', ety, hcom, eclk, eren⟩ := hdst
    refine ⟨Id', hId', pd', hpd', hpid', ?_⟩
    cases hs : b.src with
    | const e =>
      rw [hs] at hsrc
      obtain ⟨h1, h2, h3, h4, h5⟩ := hsrc
      refine ⟨h1, h2, h3, ?_, fun p hp Δ => h5 p (hcom hp) Δ⟩
      rw [eren, ety]; exact h4
    | port ks id =>
      rw [hs] at hsrc
      obtain ⟨Is, hIs, psrc, hpsrc, hpsid, hty, hcom', hclk⟩ := hsrc
      -- the source instance after substitution, and a matching provided port
      have hsrc' : ∃ Is' ps', (S.replace k I').instAt ks = some Is' ∧ ps' ∈ Is'.comp.iface.provided ∧
          ps'.id = id ∧ ps'.iface.expectedType = psrc.iface.expectedType ∧
          psrc.iface.commitments ⊆ ps'.iface.commitments ∧ ps'.clock = psrc.clock ∧
          (S.replace k I').ren ks Is' = S.ren ks Is := by
        by_cases hk : k = ks
        · subst hk
          have hatk := h.atk; rw [hatk] at hIs; cases hIs
          obtain ⟨p', hp', e1, e2, e3, e4⟩ := h.iface.provided psrc hpsrc
          exact ⟨I', p', instAt_replace_self h.lt_length, hp', e1.trans hpsid, e2, e3, e4, hren⟩
        · exact ⟨Is, psrc, by rw [instAt_replace_other hk]; exact hIs, hpsrc, hpsid, rfl, List.Subset.refl _, rfl, rfl⟩
      obtain ⟨Is', ps', hIs', hps', hpsid', ety', hcom'', eclk', eren'⟩ := hsrc'
      refine ⟨Is', hIs', ps', hps', hpsid', ?_, fun p hp => hcom'' (hcom' (hcom hp)), ?_⟩
      · rw [eren', eren, ety', ety]; exact hty
      · cases ht : b.transport with
        | none =>
          rw [ht] at hclk
          rw [eren', eren, eclk', eclk]; exact hclk
        | some init =>
          rw [ht] at hclk
          obtain ⟨⟨cd, hcd⟩, ⟨cs, hcs⟩, h1, h2, h3, h4⟩ := hclk
          refine ⟨⟨cd, eclk ▸ hcd⟩, ⟨cs, eclk' ▸ hcs⟩, h1, h2, ?_, ?_⟩
          · rw [eren, ety]; exact h3
          · rw [eren, ety]; exact h4
  · -- external sinks: the replacement drives no external sink the original did not
    intro k₁ I₁ d₁ k₂ I₂ d₂ o hI₁ hI₂ hβ₁ hi₁ hβ₂ hi₂
    -- reduce a drive of the replacement to a drive of the original
    have red : ∀ k' J d, (S.replace k I').instAt k' = some J → J.comp.design.β d = some o →
        J.comp.internalOut o = false → ∃ J₀, S.instAt k' = some J₀ ∧ J₀.comp.design.β d = some o ∧
          J₀.comp.internalOut o = false := by
      intro k' J d hJ hβ hi
      by_cases hk : k = k'
      · subst hk
        rw [instAt_replace_self h.lt_length] at hJ; cases hJ
        refine ⟨I, h.atk, h.noNewDrives d o hβ hi, ?_⟩
        rw [← h.sameOut]; exact hi
      · rw [instAt_replace_other hk] at hJ
        exact ⟨J, hJ, hβ, hi⟩
    obtain ⟨J₁, hJ₁, hβ₁', hi₁'⟩ := red k₁ I₁ d₁ hI₁ hβ₁ hi₁
    obtain ⟨J₂, hJ₂, hβ₂', hi₂'⟩ := red k₂ I₂ d₂ hI₂ hβ₂ hi₂
    exact c.external k₁ J₁ d₁ k₂ J₂ d₂ o hJ₁ hJ₂ hβ₁' hi₁' hβ₂' hi₂'

end BehaviorSystem
end BDL
