import BDL.Surface.Buffer

/-!
# Capacity — finite buffers are a validation obligation (Phase 9a)

The kernel semantics of the buffered transport is the unbounded list
(`Buffer.buffer_window_correspondence`).  A deployment has finite memory,
so it must show that no window ever exceeds its capacity; otherwise the
implementation *must* change behaviour, and the change is observable.

* `CapacitySufficient S src dst cap T` — every window up to horizon `T`
  fits (decidable for a finite horizon);
* `requiredCapacity` — the least sufficient capacity for a finite horizon;
* for **periodic** schedules an infinite-horizon bound: a window never
  holds more than one destination period of source activations;
* the overflow *policies* — drop oldest, drop newest — as explicit
  functions of the unbounded window: under sufficient capacity they are
  the identity (`sufficient_capacity_preserves`); under insufficient
  capacity they change the trace (`insufficient_capacity_counterexample`,
  in the experiments).  Only *rejecting* an insufficient deployment keeps
  the unbounded semantics.
-/

namespace BDL.Validation.Capacity
open BDL BDL.Clock

def windowLen (S : Sched) (src dst : ClockId) (t : Nat) : Nat := (windowTicks S src dst t).length

/-- Every window up to the horizon fits in `cap`. -/
def CapacitySufficient (S : Sched) (src dst : ClockId) (cap T : Nat) : Prop :=
  ∀ t, t ≤ T → windowLen S src dst t ≤ cap

instance (S : Sched) (src dst : ClockId) (cap T : Nat) : Decidable (CapacitySufficient S src dst cap T) :=
  inferInstanceAs (Decidable (∀ t, t ≤ T → windowLen S src dst t ≤ cap))

/-- The least sufficient capacity for a finite horizon. -/
def requiredCapacity (S : Sched) (src dst : ClockId) (T : Nat) : Nat :=
  (List.range (T + 1)).foldl (fun m t => max m (windowLen S src dst t)) 0

theorem foldl_max_ge (f : Nat → Nat) (l : List Nat) (a : Nat) :
    ∀ t ∈ l, f t ≤ l.foldl (fun m t => max m (f t)) a := by
  induction l generalizing a with
  | nil => intro t h; simp at h
  | cons x xs ih =>
    intro t ht
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ht with rfl | ht
    · exact Nat.le_trans (Nat.le_max_right a (f t)) (foldl_max_le_foldl _ _ _)
    · exact ih _ t ht
where
  foldl_max_le_foldl (f : Nat → Nat) (l : List Nat) (a : Nat) : a ≤ l.foldl (fun m t => max m (f t)) a := by
    induction l generalizing a with
    | nil => exact Nat.le_refl _
    | cons x xs ih => exact Nat.le_trans (Nat.le_max_left a (f x)) (ih _)

/-- **`requiredCapacity` is sufficient** for its horizon. -/
theorem requiredCapacity_sufficient (S : Sched) (src dst : ClockId) (T : Nat) :
    CapacitySufficient S src dst (requiredCapacity S src dst T) T := by
  intro t ht
  exact foldl_max_ge (windowLen S src dst) (List.range (T + 1)) 0 t (List.mem_range.mpr (Nat.lt_succ_of_le ht))

/-! ## Overflow policies, as functions of the unbounded window -/

/-- Keep the newest `cap` entries. -/
def dropOldest {α : Type} (cap : Nat) (w : List α) : List α := w.drop (w.length - cap)
/-- Keep the oldest `cap` entries. -/
def dropNewest {α : Type} (cap : Nat) (w : List α) : List α := w.take cap

/-- **`sufficient_capacity_preserves`**: when the window fits, both
    policies return the unbounded window — the list semantics is kept. -/
theorem sufficient_capacity_preserves {α : Type} {cap : Nat} {w : List α} (h : w.length ≤ cap) :
    dropOldest cap w = w ∧ dropNewest cap w = w := by
  constructor
  · simp [dropOldest, Nat.sub_eq_zero_of_le h]
  · simp [dropNewest, List.take_of_length_le h]

/-- Under a sufficient capacity, a bounded implementation of the buffered
    transport agrees with the unbounded one at every tick of the horizon. -/
theorem bounded_buffer_agrees (S : Sched) (src dst : ClockId) {cap T : Nat}
    (hcap : CapacitySufficient S src dst cap T) (I : Reactive.Input) (d : DeclId) {t : Nat} (ht : t ≤ T) :
    dropOldest cap ((windowTicks S src dst t).map (I d)) = (windowTicks S src dst t).map (I d) ∧
    dropNewest cap ((windowTicks S src dst t).map (I d)) = (windowTicks S src dst t).map (I d) :=
  sufficient_capacity_preserves (by rw [List.length_map]; exact hcap t ht)

/-! ## Periodic schedules: an infinite-horizon bound -/

theorem prevAct_spec (S : Sched) (c : ClockId) :
    ∀ t t₀, prevAct S c t = some t₀ → S c t₀ = true ∧ t₀ < t ∧ ∀ u, t₀ < u → u < t → S c u = false
  | 0, _, h => by simp [prevAct] at h
  | t + 1, t₀, h => by
    simp only [prevAct] at h
    split at h
    · rename_i hs
      cases h
      exact ⟨hs, Nat.lt_succ_self _, fun u h₁ h₂ => by omega⟩
    · rename_i hs
      obtain ⟨h₁, h₂, h₃⟩ := prevAct_spec S c t t₀ h
      refine ⟨h₁, Nat.lt_succ_of_lt h₂, fun u hu₁ hu₂ => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hu₂) with hu | rfl
      · exact h₃ u hu₁ hu
      · simpa using hs

theorem prevAct_none_spec (S : Sched) (c : ClockId) :
    ∀ t, prevAct S c t = none → ∀ u, u < t → S c u = false
  | 0, _, u, hu => absurd hu (Nat.not_lt_zero _)
  | t + 1, h, u, hu => by
    simp only [prevAct] at h
    split at h
    · exact nomatch h
    · rename_i hs
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hu) with hu | rfl
      · exact prevAct_none_spec S c t h u hu
      · simpa using hs

theorem filter_eq_nil_of {α : Type} (p : α → Bool) :
    ∀ l : List α, (∀ a ∈ l, p a = false) → l.filter p = []
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filter_cons_of_neg (by simp [h a (List.mem_cons_self ..)])]
    exact filter_eq_nil_of p l (fun b hb => h b (List.mem_cons_of_mem a hb))

/-- A window over `[lo, hi)` has at most `hi − lo` entries. -/
theorem srcTicks_length_le (S : Sched) (c : ClockId) (lo hi : Nat) : (srcTicks S c lo hi).length ≤ hi - lo := by
  unfold srcTicks
  rcases Nat.lt_or_ge hi lo with h | h
  · have : ((List.range hi).filter fun u => decide (lo ≤ u) && S c u) = [] := by
      apply filter_eq_nil_of
      intro u hu
      have := List.mem_range.mp hu
      simp [Nat.not_le.mpr (Nat.lt_trans this h)]
    rw [this]; exact Nat.zero_le _
  · obtain ⟨k, rfl⟩ : ∃ k, hi = lo + k := ⟨hi - lo, (Nat.add_sub_cancel' h).symm⟩
    have h1 : ((List.range lo).filter fun u => decide (lo ≤ u) && S c u) = [] := by
      apply filter_eq_nil_of
      intro u hu
      have := List.mem_range.mp hu
      simp [Nat.not_le.mpr this]
    rw [List.range_add, List.filter_append, h1, List.nil_append, Nat.add_sub_cancel_left]
    exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- **Periodic bound.**  With the destination periodic of period `p > 0`,
    no window at any tick holds more than `p` source activations. -/
theorem periodic_window_bound (per : ClockId → Nat) (src dst : ClockId) (hp : 0 < per dst) (t : Nat) :
    windowLen (Sched.periodic per) src dst t ≤ per dst := by
  unfold windowLen windowTicks
  cases hpa : prevAct (Sched.periodic per) dst t with
  | none =>
    -- tick 0 is an activation of every periodic domain, so `t = 0`
    have h0 : t = 0 := by
      cases t with
      | zero => rfl
      | succ t =>
        have := prevAct_none_spec _ dst (t + 1) hpa 0 (Nat.succ_pos t)
        simp [Sched.periodic] at this
    subst h0
    simp [srcTicks]
  | some t₀ =>
    obtain ⟨hact, hlt, hgap⟩ := prevAct_spec _ dst t t₀ hpa
    simp only [Option.getD_some]
    refine Nat.le_trans (srcTicks_length_le _ _ _ _) ?_
    -- the gap after `t₀` contains no multiple of the period
    rcases Nat.lt_or_ge (per dst) (t - t₀) with hbig | hsmall
    · exfalso
      have hbig' : t₀ + per dst < t := by omega
      have := hgap (t₀ + per dst) (by omega) hbig'
      simp only [Sched.periodic, decide_eq_false_iff_not, decide_eq_true_eq] at this hact
      exact this (by rw [Nat.add_mod, hact, Nat.mod_self, Nat.zero_add, Nat.zero_mod])
    · exact hsmall

/-- **`periodic_capacity_sufficient`**: for periodic schedules a capacity of
    one destination period is sufficient at every horizon. -/
theorem periodic_capacity_sufficient (per : ClockId → Nat) (src dst : ClockId) (hp : 0 < per dst) (T : Nat) :
    CapacitySufficient (Sched.periodic per) src dst (per dst) T :=
  fun t _ => periodic_window_bound per src dst hp t

end BDL.Validation.Capacity
