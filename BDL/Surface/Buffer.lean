import BDL.Core.ListData

/-!
# Buffer — lossless cross-domain event transport as surface elaboration (Phase 9a)

Phase 5 proved, on tick sets, that the destination's *window* — the source
activations since the destination's previous activation — is the source
log read now, minus the log length read at the previous destination
activation (`buffer_from_log_and_cursor`).  It could not write that
construction in the object language for want of list data.  With
`Ty.list` (Phase 9a) the construction is five ordinary declarations:

    log     @src :  cons src (delay nil log)             -- source-side accumulator
    logD    @dst :  sync src nil log                     -- the log, transported
    seen    @dst :  length logD                          -- log length now
    cursor  @dst :  delay 0 seen                         -- log length at the previous activation
    window  @dst :  reverse (take (seen − cursor) logD)  -- the new entries, oldest first

Nothing new is evaluated: `delay`, `sync`, and registered operators.  The
strictly-before rule is untouched — the window at `t` contains source
activations `< t` only.

**Theorem M** (`buffer_window_correspondence`): at every tick, in the
destination domain, `window` evaluates to exactly the source's values at
the Phase-5 window ticks, in order and with multiplicity.
-/

namespace BDL.Buffer
open BDL BDL.Reactive BDL.Clock

/-! ## Log ticks and previous activations -/

theorem logTicks_zero (S : Sched) (c : ClockId) : logTicks S c 0 = [] := rfl

theorem logTicks_succ (S : Sched) (c : ClockId) (t : Nat) :
    logTicks S c (t + 1) = logTicks S c t ++ (if S c t then [t] else []) := by
  simp only [logTicks, srcTicks, List.range_succ, List.filter_append, List.filter_cons, List.filter_nil,
    Nat.zero_le, decide_true, Bool.true_and]

theorem logTicks_of_prevAct_none (S : Sched) (c : ClockId) :
    ∀ t, prevAct S c t = none → logTicks S c t = []
  | 0, _ => rfl
  | t + 1, h => by
    simp only [prevAct] at h
    split at h
    · exact nomatch h
    · rename_i hs
      rw [logTicks_succ, logTicks_of_prevAct_none S c t h, if_neg hs]; rfl

theorem logTicks_of_prevAct_some (S : Sched) (c : ClockId) :
    ∀ t u, prevAct S c t = some u → logTicks S c t = logTicks S c u ++ [u]
  | 0, _, h => by simp [prevAct] at h
  | t + 1, u, h => by
    simp only [prevAct] at h
    split at h
    · rename_i hs
      cases h
      rw [logTicks_succ, if_pos hs]
    · rename_i hs
      rw [logTicks_succ, if_neg hs, List.append_nil]
      exact logTicks_of_prevAct_some S c t u h

theorem logTicks_length_mono (S : Sched) (c : ClockId) {t₀ t : Nat} (h : t₀ ≤ t) :
    (logTicks S c t₀).length ≤ (logTicks S c t).length := by
  obtain ⟨k, rfl⟩ : ∃ k, t = t₀ + k := ⟨t - t₀, (Nat.add_sub_cancel' h).symm⟩
  clear h
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    rw [← Nat.add_assoc, logTicks_succ, List.length_append]
    exact Nat.le_trans ih (Nat.le_add_right _ _)

/-! ## The elaboration -/

/-- The declarations a buffered transport introduces. -/
structure Ids where
  src : DeclId
  log : DeclId
  logD : DeclId
  seen : DeclId
  cursor : DeclId
  window : DeclId

def Q0 : Ty := .q Dim.zero

def nilE (τ : Ty) : Expr := .prim (.nil τ)
def consE (τ : Ty) (x l : Expr) : Expr := .app (.app (.prim (.cons τ)) x) l
def lenE (τ : Ty) (l : Expr) : Expr := .app (.prim (.length τ)) l
def takeE (τ : Ty) (k l : Expr) : Expr := .app (.app (.prim (.take τ)) k) l
def revE (τ : Ty) (l : Expr) : Expr := .app (.prim (.reverse τ)) l
def subE (a b : Expr) : Expr := .app (.app (.prim (.sub Dim.zero)) a) b
def zeroE : Expr := .prim (.lit Dim.zero 0)

variable (τ : Ty) (cs : ClockId) (ids : Ids)

def logBody : Expr := consE τ (.declRef ids.src) (.delay (nilE τ) (.declRef ids.log))
def logDBody : Expr := .sync cs (nilE τ) (.declRef ids.log)
def seenBody : Expr := lenE τ (.declRef ids.logD)
def cursorBody : Expr := .delay zeroE (.declRef ids.seen)
def windowBody : Expr := revE τ (takeE τ (subE (.declRef ids.seen) (.declRef ids.cursor)) (.declRef ids.logD))

def logDecl : DesignDecl := ⟨ids.log, ⟨.list τ, []⟩, some (logBody τ ids)⟩
def logDDecl : DesignDecl := ⟨ids.logD, ⟨.list τ, []⟩, some (logDBody τ cs ids)⟩
def seenDecl : DesignDecl := ⟨ids.seen, ⟨Q0, []⟩, some (seenBody τ ids)⟩
def cursorDecl : DesignDecl := ⟨ids.cursor, ⟨Q0, []⟩, some (cursorBody ids)⟩
def windowDecl : DesignDecl := ⟨ids.window, ⟨.list τ, []⟩, some (windowBody τ ids)⟩

/-- The five declarations of a buffered transport of `src : τ`. -/
def decls : List DesignDecl := [logDecl τ ids, logDDecl τ cs ids, seenDecl τ ids, cursorDecl ids, windowDecl τ ids]

/-! ## K — well typed -/

/-- **`buffer_elaboration_well_typed`.**  In any environment whose type
    view has `src : τ` and the five declarations at their types, each body
    has its declared type (for data `τ`).  Commitments are empty. -/
theorem buffer_elaboration_well_typed (Θ : ConceptEnv) (Δ : DeclEnv) (G : Grant) (hd : τ.Data)
    (hsrc : Δ.tyView ids.src = some τ) (hlog : Δ.tyView ids.log = some (.list τ))
    (hlogD : Δ.tyView ids.logD = some (.list τ)) (hseen : Δ.tyView ids.seen = some Q0)
    (hcursor : Δ.tyView ids.cursor = some Q0) :
    HasType Θ Δ G [] (logBody τ ids) (.list τ) ∧ HasType Θ Δ G [] (logDBody τ cs ids) (.list τ) ∧
    HasType Θ Δ G [] (seenBody τ ids) Q0 ∧ HasType Θ Δ G [] (cursorBody ids) Q0 ∧
    HasType Θ Δ G [] (windowBody τ ids) (.list τ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact .app (.app .prim (.declRef hsrc)) (.delay hd .prim (.declRef hlog))
  · exact .sync hd .prim (.declRef hlog)
  · exact .app .prim (.declRef hlogD)
  · exact .delay trivial .prim (.declRef hseen)
  · exact .app .prim (.app (.app .prim (.app (.app .prim (.declRef hseen)) (.declRef hcursor))) (.declRef hlogD))

/-! ## L — well clocked -/

/-- **`buffer_elaboration_well_clocked`.**  With `src` and `log` in the
    source domain and the other four in the destination domain, every body
    is clocked in its declaration's domain; the only cross-domain read is
    the explicit `sync` in `logD`. -/
theorem buffer_elaboration_well_clocked (Κ : ClockEnv) (cd : ClockId)
    (hsrc : Κ ids.src = some cs ∨ Κ ids.src = none) (hlog : Κ ids.log = some cs)
    (hlogD : Κ ids.logD = some cd) (hseen : Κ ids.seen = some cd) (hcursor : Κ ids.cursor = some cd) :
    Clocked Κ (some cs) (logBody τ ids) ∧ Clocked Κ (some cd) (logDBody τ cs ids) ∧
    Clocked Κ (some cd) (seenBody τ ids) ∧ Clocked Κ (some cd) (cursorBody ids) ∧
    Clocked Κ (some cd) (windowBody τ ids) := by
  unfold Clocked
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hsrc with h | h <;> simp [logBody, consE, nilE, clockedB, h, hlog]
  · simp [logDBody, nilE, clockedB, hlog]
  · simp [seenBody, lenE, clockedB, hlogD]
  · simp [cursorBody, zeroE, clockedB, hseen]
  · simp [windowBody, revE, takeE, subE, clockedB, hseen, hcursor, hlogD]

/-! ## Evaluation helpers -/

theorem mev_cons {S : Sched} {Δ : DeclEnv} {I : Input} {c t : Nat} {ρ : List Value} {x l : Expr} {v : Value} {vs : List Value}
    (hx : MEv S Δ I ⟨c⟩ t ρ x v) (hl : MEv S Δ I ⟨c⟩ t ρ l (.list vs)) :
    MEv S Δ I ⟨c⟩ t ρ (consE τ x l) (.list (v :: vs)) := by
  have := MEv.appPrim (MEv.appPrim (MEv.prim (p := .cons τ)) hx) hl
  simpa [consE, lenE, takeE, revE, subE, nilE, zeroE, applyPrim, Prim.arity, Prim.compute] using this

theorem mev_len {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat} {ρ : List Value} {l : Expr} {vs : List Value}
    (hl : MEv S Δ I c t ρ l (.list vs)) : MEv S Δ I c t ρ (lenE τ l) (.nat vs.length) := by
  have := MEv.appPrim (MEv.prim (p := .length τ)) hl
  simpa [consE, lenE, takeE, revE, subE, nilE, zeroE, applyPrim, Prim.arity, Prim.compute] using this

theorem mev_take {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat} {ρ : List Value} {k l : Expr}
    {n : Nat} {vs : List Value} (hk : MEv S Δ I c t ρ k (.nat n)) (hl : MEv S Δ I c t ρ l (.list vs)) :
    MEv S Δ I c t ρ (takeE τ k l) (.list (vs.take n)) := by
  have := MEv.appPrim (MEv.appPrim (MEv.prim (p := .take τ)) hk) hl
  simpa [consE, lenE, takeE, revE, subE, nilE, zeroE, applyPrim, Prim.arity, Prim.compute] using this

theorem mev_rev {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat} {ρ : List Value} {l : Expr} {vs : List Value}
    (hl : MEv S Δ I c t ρ l (.list vs)) : MEv S Δ I c t ρ (revE τ l) (.list vs.reverse) := by
  have := MEv.appPrim (MEv.prim (p := .reverse τ)) hl
  simpa [consE, lenE, takeE, revE, subE, nilE, zeroE, applyPrim, Prim.arity, Prim.compute] using this

theorem mev_sub {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat} {ρ : List Value} {a b : Expr} {m n : Nat}
    (ha : MEv S Δ I c t ρ a (.nat m)) (hb : MEv S Δ I c t ρ b (.nat n)) :
    MEv S Δ I c t ρ (subE a b) (.nat (m - n)) := by
  have := MEv.appPrim (MEv.appPrim (MEv.prim (p := .sub Dim.zero)) ha) hb
  simpa [consE, lenE, takeE, revE, subE, nilE, zeroE, applyPrim, Prim.arity, Prim.compute] using this

theorem mev_nil {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat} {ρ : List Value} :
    MEv S Δ I c t ρ (nilE τ) (.list []) := by
  have := MEv.prim (S := S) (Δ := Δ) (I := I) (c := c) (t := t) (ρ := ρ) (p := .nil τ)
  simpa [consE, lenE, takeE, revE, subE, nilE, zeroE, applyPrim, Prim.arity, Prim.compute] using this

theorem mev_zero {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat} {ρ : List Value} :
    MEv S Δ I c t ρ zeroE (.nat 0) := by
  have := MEv.prim (S := S) (Δ := Δ) (I := I) (c := c) (t := t) (ρ := ρ) (p := .lit Dim.zero 0)
  simpa [consE, lenE, takeE, revE, subE, nilE, zeroE, applyPrim, Prim.arity, Prim.compute] using this

/-! ## M — the correspondence theorem -/

/-- The environment realizes the five declarations and leaves `src` an input. -/
structure Realized (Δ : DeclEnv) : Prop where
  src : Δ.realizationOf ids.src = none
  log : Δ.realizationOf ids.log = some (logBody τ ids)
  logD : Δ.realizationOf ids.logD = some (logDBody τ cs ids)
  seen : Δ.realizationOf ids.seen = some (seenBody τ ids)
  cursor : Δ.realizationOf ids.cursor = some (cursorBody ids)
  window : Δ.realizationOf ids.window = some (windowBody τ ids)

variable {τ cs ids}

/-- The source log at tick `u`, read in the source domain: the source's
    value now, then its values at every earlier source activation, newest
    first. -/
theorem log_at {S : Sched} {Δ : DeclEnv} {I : Input} (R : Realized τ cs ids Δ) :
    ∀ u, MEv S Δ I cs u [] (.declRef ids.log) (.list ((u :: (logTicks S cs u).reverse).map (I ids.src))) := by
  intro u
  induction u using Nat.strongRecOn with
  | ind u ih =>
    refine .refRealized R.log ?_
    unfold logBody
    refine mev_cons τ (.refInput R.src) ?_
    cases hp : prevAct S cs u with
    | none =>
      rw [logTicks_of_prevAct_none S cs u hp]
      simp only [List.reverse_nil, List.map_nil]
      exact .delayNone hp (mev_nil τ)
    | some u' =>
      have hlt := prevAct_lt hp
      have := ih u' hlt
      rw [logTicks_of_prevAct_some S cs u u' hp]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
        List.map_cons]
      exact .delaySome hp this

/-- The transported log at tick `t`, read in the destination domain: the
    source's values at all source activations strictly before `t`, newest
    first. -/
theorem logD_at {S : Sched} {Δ : DeclEnv} {I : Input} (R : Realized τ cs ids Δ) (cd : ClockId) (t : Nat) :
    MEv S Δ I cd t [] (.declRef ids.logD) (.list ((logTicks S cs t).reverse.map (I ids.src))) := by
  refine .refRealized R.logD ?_
  unfold logDBody
  cases hp : prevAct S cs t with
  | none =>
    rw [logTicks_of_prevAct_none S cs t hp]
    exact .syncNone hp (mev_nil τ)
  | some u =>
    rw [logTicks_of_prevAct_some S cs t u hp]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    exact .syncSome hp (log_at R u)

theorem seen_at {S : Sched} {Δ : DeclEnv} {I : Input} (R : Realized τ cs ids Δ) (cd : ClockId) (t : Nat) :
    MEv S Δ I cd t [] (.declRef ids.seen) (.nat (logTicks S cs t).length) := by
  refine .refRealized R.seen ?_
  unfold seenBody
  have := mev_len τ (logD_at (S := S) (I := I) R cd t)
  simpa using this

theorem cursor_at {S : Sched} {Δ : DeclEnv} {I : Input} (R : Realized τ cs ids Δ) (cd : ClockId) (t : Nat) :
    MEv S Δ I cd t [] (.declRef ids.cursor) (.nat (logTicks S cs ((prevAct S cd t).getD 0)).length) := by
  refine .refRealized R.cursor ?_
  unfold cursorBody
  cases hp : prevAct S cd t with
  | none => exact .delayNone hp mev_zero
  | some t₀ => exact .delaySome hp (seen_at R cd t₀)

/-- The list identity behind the window: the newest `|l| − m` entries of
    a newest-first log, put back in order, are the entries after the first `m`. -/
theorem take_reverse_drop {α : Type} (l : List α) (m : Nat) (hm : m ≤ l.length) :
    (l.reverse.take (l.length - m)).reverse = l.drop m := by
  rw [List.take_reverse, List.reverse_reverse, Nat.sub_sub_self hm]

theorem take_reverse_map_drop {α β : Type} (f : α → β) (l : List α) (m : Nat) (hm : m ≤ l.length) :
    ((l.reverse.map f).take (l.length - m)).reverse = (l.drop m).map f := by
  rw [List.map_reverse, ← List.map_reverse, ← List.map_take, ← List.map_reverse, take_reverse_drop l m hm, List.map_drop]

/-- **Theorem M — `buffer_window_correspondence`.**  At every tick `t`, in
    the destination domain, `window` is the list of the source's values at
    the Phase-5 window ticks `windowTicks S src dst t` — the source
    activations since the destination's previous activation — in order and
    with multiplicity.

    Assumptions: the six declarations are realized as elaborated
    (`Realized`) and `src` is an input.  No assumption on the schedules:
    the statement holds at activation and non-activation ticks alike. -/
theorem buffer_window_correspondence {S : Sched} {Δ : DeclEnv} {I : Input} (R : Realized τ cs ids Δ)
    (cd : ClockId) (t : Nat) :
    MEv S Δ I cd t [] (.declRef ids.window) (.list ((windowTicks S cs cd t).map (I ids.src))) := by
  refine .refRealized R.window ?_
  unfold windowBody
  have hlogD := logD_at (S := S) (I := I) R cd t
  have hseen := seen_at (S := S) (I := I) R cd t
  have hcursor := cursor_at (S := S) (I := I) R cd t
  have hwin := mev_rev τ (mev_take τ (mev_sub hseen hcursor) hlogD)
  -- t₀ ≤ t, so the cursor is a prefix length of the log
  have ht₀ : (prevAct S cd t).getD 0 ≤ t := by
    cases hp : prevAct S cd t with
    | none => exact Nat.zero_le _
    | some t₀ => exact Nat.le_of_lt (prevAct_lt hp)
  have hle := logTicks_length_mono S cs ht₀
  rw [take_reverse_map_drop _ _ _ hle] at hwin
  unfold windowTicks
  rw [buffer_from_log_and_cursor S cs _ t ht₀]
  exact hwin

/-! ## N — losslessness -/

/-- A *summary* of a window is any function of its value list. -/
def Summary := List Value → Value

/-- A summary is lossless when it is injective on windows. -/
def Summary.Lossless (f : Summary) : Prop := ∀ w₁ w₂, f w₁ = f w₂ → w₁ = w₂

/-- The list representation itself. -/
def asList : Summary := Value.list

/-- **`buffer_lossless`**: the window's list representation is injective —
    windows differing in length, order, or any value have different
    representations. -/
theorem buffer_lossless : asList.Lossless := fun _ _ h => Value.list.inj h

theorem pairwise_lt_range : ∀ n, (List.range n).Pairwise (· < ·)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.pairwise_append]
    refine ⟨pairwise_lt_range n, by simp, ?_⟩
    intro a ha b hb
    simp at hb; subst hb
    exact List.mem_range.mp ha

/-- Window ticks are strictly increasing: the source's activation order. -/
theorem windowTicks_sorted (S : Sched) (src dst : ClockId) (t : Nat) : (windowTicks S src dst t).Pairwise (· < ·) :=
  List.Pairwise.filter _ (pairwise_lt_range t)

/-- **`window_to_list_preserves_order`**: the represented list is indexed
    by the window ticks in strictly increasing order — its `i`-th entry is
    the source's value at the `i`-th activation of the window. -/
theorem window_to_list_preserves_order (S : Sched) (src dst : ClockId) (I : Input) (d : DeclId) (t : Nat) :
    (windowTicks S src dst t).Pairwise (· < ·) ∧
    ∀ i (h : i < (windowTicks S src dst t).length),
      ((windowTicks S src dst t).map (I d))[i]'(by simpa using h) = I d (windowTicks S src dst t)[i] :=
  ⟨windowTicks_sorted S src dst t, fun _ _ => List.getElem_map ..⟩

/-- **`window_to_list_preserves_multiplicity`**: for every observable
    property of a value, the number of entries with that property equals
    the number of window activations whose source value has it. -/
theorem window_to_list_preserves_multiplicity (S : Sched) (src dst : ClockId) (I : Input) (d : DeclId) (t : Nat)
    (p : Value → Bool) :
    (((windowTicks S src dst t).map (I d)).filter p).length =
      ((windowTicks S src dst t).filter (p ∘ I d)).length := by
  rw [List.filter_map, List.length_map]

def latest : Summary := fun w => match w.getLast? with | some v => .some v | none => .none
def count : Summary := fun w => .nat w.length
def sumNat : Summary := fun w => .nat (w.foldl (fun acc v => match v with | .nat n => acc + n | _ => acc) 0)

/-- **`latest_not_lossless`**: `[1, 2]` and `[2]` have the same latest value. -/
theorem latest_not_lossless : ¬ latest.Lossless := by
  intro h
  have := h [.nat 1, .nat 2] [.nat 2] rfl
  simp at this

/-- **`count_not_lossless`**: `[1, 2]` and `[2, 1]` (order) and `[3, 4]`
    (values) have the same count. -/
theorem count_not_lossless : ¬ count.Lossless := by
  intro h
  have := h [.nat 1, .nat 2] [.nat 2, .nat 1] rfl
  simp at this

/-- `sum` collides whenever two windows have equal totals: `[1, 4]` and `[2, 3]`. -/
theorem sum_not_lossless : ¬ sumNat.Lossless := by
  intro h
  have := h [.nat 1, .nat 4] [.nat 2, .nat 3] rfl
  simp at this

/-- A lossless summary can be inverted on windows, so *every* summary that
    is a function of the list — including any coalescing fold — is
    recoverable from the list.  Lossless summaries are exactly the
    injective ones, by definition; the list is one, and it is the one the
    transport carries. -/
theorem lossless_iff_injective (f : Summary) : f.Lossless ↔ Function.Injective f := Iff.rfl

end BDL.Buffer
