import BDL.Behavior.Component

/-!
# Instantiate — fresh identities for every instance

Instance `k` of a component in a system of *width* `W` (a bound above every
global identity and every template width) receives, for each internal local
identity `n < W`, the fresh identity

    fresh W k n = W * (k + 1) + n .

Fresh identities are `≥ W`, hence disjoint from every global identity, and
`decode` recovers `(k, n)` from a fresh identity, so instances never alias
(**Theorem A**).  Identity is arithmetic here only because the kernel's
identities are wrapped naturals; nothing depends on the particular encoding
beyond injectivity and decodability.
-/

namespace BDL
open BDL.Output (OutputId OutputSpec OutputEnv DriveEnv)
open BDL.Clock (ClockEnv)

/-! ## Fresh identities and their decoding -/

def fresh (W k n : Nat) : Nat := W * (k + 1) + n

/-- Which instance owns identity `m`, and which local identity it renames.
    `none` for global identities (`m < W`). -/
def decode (W m : Nat) : Option (Nat × Nat) :=
  if 0 < W ∧ W ≤ m then some (m / W - 1, m % W) else none

theorem fresh_ge {W k n : Nat} (_hW : 0 < W) : W ≤ fresh W k n := by
  unfold fresh
  have : W * 1 ≤ W * (k + 1) := Nat.mul_le_mul_left W (by omega)
  omega

theorem decode_fresh {W k n : Nat} (hW : 0 < W) (hn : n < W) : decode W (fresh W k n) = some (k, n) := by
  unfold decode
  rw [if_pos ⟨hW, fresh_ge hW⟩]
  unfold fresh
  rw [Nat.mul_add_div hW, Nat.div_eq_of_lt hn, Nat.mul_add_mod, Nat.mod_eq_of_lt hn]
  simp

theorem decode_some {W m k n : Nat} (h : decode W m = some (k, n)) : m = fresh W k n ∧ n < W ∧ 0 < W := by
  unfold decode at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hk, hn⟩ := h
    refine ⟨?_, hn ▸ Nat.mod_lt m hc.1, hc.1⟩
    have hdiv : 1 ≤ m / W := by
      have := Nat.le_div_iff_mul_le hc.1 |>.mpr (by omega : 1 * W ≤ m)
      exact this
    have := Nat.div_add_mod m W
    unfold fresh
    rw [← hk, ← hn, Nat.sub_add_cancel hdiv]
    omega
  · exact nomatch h

theorem decode_global {W m : Nat} (h : m < W) : decode W m = none := by
  unfold decode
  rw [if_neg]; omega

/-- **Theorem A (arithmetic core).**  Fresh identities of distinct instances
    are distinct, and fresh identities of one instance are injective in the
    local identity. -/
theorem fresh_inj {W k₁ n₁ k₂ n₂ : Nat} (hW : 0 < W) (h₁ : n₁ < W) (h₂ : n₂ < W)
    (h : fresh W k₁ n₁ = fresh W k₂ n₂) : k₁ = k₂ ∧ n₁ = n₂ := by
  have e := decode_fresh (k := k₁) hW h₁
  rw [h, decode_fresh hW h₂] at e
  simpa using e.symm

/-! ## The instance renaming -/

/-- The renaming of instance `k` of `C` in a system of width `W`, with the
    clock parameters mapped by `κ`.  Internal identities are freshened;
    global concepts and external sinks are fixed; clock parameters are
    substituted. -/
def Ren.inst (C : BehaviorComponent) (W k : Nat) (κ : ClockId → ClockId) : Ren where
  d := fun d => ⟨fresh W k d.n⟩
  s := fun s => if C.internalSem s then ⟨fresh W k s.n⟩ else s
  c := fun c => if C.internalClock c then ⟨fresh W k c.n⟩ else κ c
  o := fun o => if C.internalOut o then ⟨fresh W k o.n⟩ else o

/-- An instance: a component with a clock-parameter assignment.  The
    instance index is its position in the system's instance list. -/
structure Inst where
  comp : BehaviorComponent
  κ : ClockId → ClockId

/-! ## Theorem A — fresh-instance disjointness -/

/-- Declarations of two distinct instances never coincide. -/
theorem inst_decl_disjoint {C₁ C₂ : BehaviorComponent} {W k₁ k₂ : Nat} {κ₁ κ₂ : ClockId → ClockId}
    (hW : 0 < W) {d₁ d₂ : DeclId} (h₁ : d₁.n < W) (h₂ : d₂.n < W)
    (h : (Ren.inst C₁ W k₁ κ₁).d d₁ = (Ren.inst C₂ W k₂ κ₂).d d₂) : k₁ = k₂ ∧ d₁ = d₂ := by
  simp only [Ren.inst, DeclId.mk.injEq] at h
  obtain ⟨hk, hn⟩ := fresh_inj hW h₁ h₂ h
  exact ⟨hk, by cases d₁; cases d₂; simp_all⟩

/-- Internal concepts of two distinct instances never coincide, and never
    coincide with a global concept. -/
theorem inst_sem_disjoint {C₁ C₂ : BehaviorComponent} {W k₁ k₂ : Nat} {κ₁ κ₂ : ClockId → ClockId}
    (hW : 0 < W) {s₁ s₂ : SemanticId} (i₁ : C₁.internalSem s₁ = true) (i₂ : C₂.internalSem s₂ = true)
    (h₁ : s₁.n < W) (h₂ : s₂.n < W)
    (h : (Ren.inst C₁ W k₁ κ₁).s s₁ = (Ren.inst C₂ W k₂ κ₂).s s₂) : k₁ = k₂ ∧ s₁ = s₂ := by
  simp only [Ren.inst, i₁, i₂, if_true, SemanticId.mk.injEq] at h
  obtain ⟨hk, hn⟩ := fresh_inj hW h₁ h₂ h
  exact ⟨hk, by cases s₁; cases s₂; simp_all⟩

theorem inst_sem_not_global {C : BehaviorComponent} {W k : Nat} {κ : ClockId → ClockId} (hW : 0 < W)
    {s g : SemanticId} (i : C.internalSem s = true) (hg : g.n < W) : (Ren.inst C W k κ).s s ≠ g := by
  simp only [Ren.inst, i, if_true]
  intro h
  have := fresh_ge (W := W) (k := k) (n := s.n) hW
  cases g; simp only [SemanticId.mk.injEq] at h; simp only at hg; omega

theorem inst_out_disjoint {C₁ C₂ : BehaviorComponent} {W k₁ k₂ : Nat} {κ₁ κ₂ : ClockId → ClockId}
    (hW : 0 < W) {o₁ o₂ : OutputId} (i₁ : C₁.internalOut o₁ = true) (i₂ : C₂.internalOut o₂ = true)
    (h₁ : o₁.n < W) (h₂ : o₂.n < W)
    (h : (Ren.inst C₁ W k₁ κ₁).o o₁ = (Ren.inst C₂ W k₂ κ₂).o o₂) : k₁ = k₂ ∧ o₁ = o₂ := by
  simp only [Ren.inst, i₁, i₂, if_true, BDL.Output.OutputId.mk.injEq] at h
  obtain ⟨hk, hn⟩ := fresh_inj hW h₁ h₂ h
  exact ⟨hk, by cases o₁; cases o₂; simp_all⟩

theorem inst_out_not_global {C : BehaviorComponent} {W k : Nat} {κ : ClockId → ClockId} (hW : 0 < W)
    {o g : OutputId} (i : C.internalOut o = true) (hg : g.n < W) : (Ren.inst C W k κ).o o ≠ g := by
  simp only [Ren.inst, i, if_true]
  intro h
  have := fresh_ge (W := W) (k := k) (n := o.n) hW
  cases g; simp only [BDL.Output.OutputId.mk.injEq] at h; simp only at hg; omega

theorem inst_clock_disjoint {C₁ C₂ : BehaviorComponent} {W k₁ k₂ : Nat} {κ₁ κ₂ : ClockId → ClockId}
    (hW : 0 < W) {c₁ c₂ : ClockId} (i₁ : C₁.internalClock c₁ = true) (i₂ : C₂.internalClock c₂ = true)
    (h₁ : c₁.n < W) (h₂ : c₂.n < W)
    (h : (Ren.inst C₁ W k₁ κ₁).c c₁ = (Ren.inst C₂ W k₂ κ₂).c c₂) : k₁ = k₂ ∧ c₁ = c₂ := by
  simp only [Ren.inst, i₁, i₂, if_true, ClockId.mk.injEq] at h
  obtain ⟨hk, hn⟩ := fresh_inj hW h₁ h₂ h
  exact ⟨hk, by cases c₁; cases c₂; simp_all⟩

end BDL
