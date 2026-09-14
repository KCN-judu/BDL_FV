import BDL.Core.Env

/-!
# Dependency — the reference graph and the unfolding semantics

`DependsOn Δ a b`: the realization of `a` refers to `b`.  (Specs in this
model contain no references, so there is no spec-level dependency yet.)

The semantics of a design at this phase is *unfolding*: replace every
reference to a realized hole by its realization, recursively, stopping at
unresolved holes.  A fully realized, well-typed design unfolds to a
hole-free program of the same type (`Unfolds.holeFree_of_executable`).

Cycles: a reference cycle through realized holes has **no unfolding at all**
(`Unfolds.not_of_cyclic`).  This is the Phase-1 sense in which a structural
cycle is harmful: the pure fragment has no fixpoints, so a cyclic definition
denotes nothing.  Whether some cycles become harmless once a delay operator
exists is deferred to the temporal phases.
-/

namespace BDL

/-! ## Dependency relation -/

/-- `a`'s realization refers to `b`.  Decidable by construction. -/
def dependsOn (Δ : HoleEnv) (a b : HoleId) : Bool :=
  match Δ.realizationOf a with
  | some e => decide (b ∈ e.refs)
  | none => false

def DependsOn (Δ : HoleEnv) (a b : HoleId) : Prop := dependsOn Δ a b = true

instance (Δ : HoleEnv) (a b : HoleId) : Decidable (DependsOn Δ a b) :=
  inferInstanceAs (Decidable (dependsOn Δ a b = true))

theorem DependsOn.iff {Δ : HoleEnv} {a b : HoleId} :
    DependsOn Δ a b ↔ ∃ e, Δ.realizationOf a = some e ∧ b ∈ e.refs := by
  unfold DependsOn dependsOn
  cases h : Δ.realizationOf a with
  | none => simp
  | some e => simp

/-- Only realized holes have outgoing edges: a cycle can never pass through
    an unresolved declaration. -/
theorem DependsOn.realized {Δ : HoleEnv} {a b : HoleId} (h : DependsOn Δ a b) :
    ∃ e, Δ.realizationOf a = some e :=
  let ⟨e, he, _⟩ := DependsOn.iff.mp h; ⟨e, he⟩

/-- Finite view of the graph, for display. -/
def depEdges (l : List DesignHole) : List (HoleId × HoleId) :=
  l.flatMap fun dh =>
    match dh.realization with
    | some e => e.refs.map (dh.id, ·)
    | none => []

/-- Transitive closure of `DependsOn`. -/
def Reaches (Δ : HoleEnv) (a b : HoleId) : Prop :=
  ∃ c, DependsOn Δ a c ∧ Star (DependsOn Δ) c b

theorem Reaches.single {Δ : HoleEnv} {a b : HoleId} (h : DependsOn Δ a b) : Reaches Δ a b :=
  ⟨b, h, .refl b⟩

theorem Reaches.star_left {Δ : HoleEnv} {a b c : HoleId}
    (h : Star (DependsOn Δ) a b) (r : Reaches Δ b c) : Reaches Δ a c := by
  induction h with
  | refl _ => exact r
  | step hab _ ih =>
    obtain ⟨d, hd, hs⟩ := ih r
    exact ⟨_, hab, .step hd hs⟩

theorem Reaches.toStar {Δ : HoleEnv} {a b : HoleId} (r : Reaches Δ a b) : Star (DependsOn Δ) a b :=
  let ⟨_, h, hs⟩ := r; .step h hs

/-- A cycle: some hole reaches itself. -/
def Cyclic (Δ : HoleEnv) : Prop := ∃ a, Reaches Δ a a

/-- Acyclicity, witnessed by a rank that strictly decreases along edges. -/
def Acyclic (Δ : HoleEnv) : Prop :=
  ∃ rank : HoleId → Nat, ∀ a b, DependsOn Δ a b → rank b < rank a

theorem Acyclic.not_cyclic {Δ : HoleEnv} (h : Acyclic Δ) : ¬ Cyclic Δ := by
  obtain ⟨rank, hr⟩ := h
  rintro ⟨a, c, hac, hca⟩
  have : ∀ {x y}, Star (DependsOn Δ) x y → rank y ≤ rank x := by
    intro x y hs
    induction hs with
    | refl _ => exact Nat.le_refl _
    | step hxy _ ih => exact Nat.le_trans ih (Nat.le_of_lt (hr _ _ hxy))
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hr _ _ hac) (this hca))

/-! ## Unfolding semantics -/

/-- Replace references to realized holes by their realizations, recursively;
    references to unresolved (or undeclared) holes are left in place. -/
inductive Unfolds (Δ : HoleEnv) : Expr → Expr → Prop where
  | var (i : Nat) : Unfolds Δ (.var i) (.var i)
  | boolLit (b : Bool) : Unfolds Δ (.boolLit b) (.boolLit b)
  | natLit (n : Nat) : Unfolds Δ (.natLit n) (.natLit n)
  | lam {dom : Ty} {b b' : Expr} : Unfolds Δ b b' → Unfolds Δ (.lam dom b) (.lam dom b')
  | app {f f' a a' : Expr} : Unfolds Δ f f' → Unfolds Δ a a' → Unfolds Δ (.app f a) (.app f' a')
  | refStuck {h : HoleId} : Δ.realizationOf h = none → Unfolds Δ (.holeRef h) (.holeRef h)
  | refRealized {h : HoleId} {e e' : Expr} :
      Δ.realizationOf h = some e → Unfolds Δ e e' → Unfolds Δ (.holeRef h) e'

/-- Unfolding is deterministic. -/
theorem Unfolds.det {Δ : HoleEnv} {e e₁ e₂ : Expr}
    (h₁ : Unfolds Δ e e₁) (h₂ : Unfolds Δ e e₂) : e₁ = e₂ := by
  induction h₁ generalizing e₂ with
  | var _ | boolLit _ | natLit _ => cases h₂; rfl
  | lam _ ih => cases h₂ with | lam hb => rw [ih hb]
  | app _ _ ihf iha => cases h₂ with | app hf ha => rw [ihf hf, iha ha]
  | refStuck hn =>
    cases h₂ with
    | refStuck _ => rfl
    | refRealized hs _ => rw [hn] at hs; exact nomatch hs
  | refRealized hs _ ih =>
    cases h₂ with
    | refStuck hn => rw [hn] at hs; exact nomatch hs
    | refRealized hs' hu => rw [hs] at hs'; cases hs'; exact ih hu

/-- Whatever references remain after unfolding are to unrealized holes. -/
theorem Unfolds.refs_stuck {Δ : HoleEnv} {e e' : Expr} (h : Unfolds Δ e e') :
    ∀ x ∈ e'.refs, Δ.realizationOf x = none := by
  induction h with
  | var _ | boolLit _ | natLit _ => intro x hx; simp [Expr.refs] at hx
  | lam _ ih => exact ih
  | app _ _ ihf iha =>
    intro x hx
    simp only [Expr.refs, List.mem_append] at hx
    exact hx.elim (ihf x) (iha x)
  | refStuck hn => intro x hx; simp [Expr.refs] at hx; subst hx; exact hn
  | refRealized _ _ ih => exact ih

/-- **Type preservation.**  In a globally well-formed design, unfolding
    preserves typing.  Uses `HasType.of_closed`: a realization is typed at
    top level and may be inlined under binders. -/
theorem Unfolds.preserves_typing {ev : Evidence} {Δ : HoleEnv} (g : GlobalWF ev Δ)
    {e e' : Expr} (hu : Unfolds Δ e e') :
    ∀ {Γ : Ctx} {τ : Ty}, HasType Δ Γ e τ → HasType Δ Γ e' τ := by
  induction hu with
  | var _ | boolLit _ | natLit _ => intro _ _ ht; exact ht
  | lam _ ih =>
    intro Γ τ ht
    cases ht with | lam hb => exact .lam (ih hb)
  | app _ _ ihf iha =>
    intro Γ τ ht
    cases ht with | app hf ha => exact .app (ihf hf) (iha ha)
  | refStuck _ => intro _ _ ht; exact ht
  | refRealized hs _ ih =>
    intro Γ τ ht
    cases ht with
    | holeRef htv =>
      simp only [HoleEnv.realizationOf, HoleEnv.tyView, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at hs htv
      obtain ⟨dh, hh, hre⟩ := hs
      obtain ⟨dh', hh', hty⟩ := htv
      rw [hh] at hh'; cases hh'
      subst hty
      exact ih (((g.wellFormed hh) _ hre).1.of_closed Γ)

/-- Every declared hole is realized. -/
def HoleEnv.FullyRealized (Δ : HoleEnv) : Prop :=
  ∀ id dh, Δ id = some dh → ∃ e, dh.realization = some e

/-- **Executable designs flatten.**  A well-typed term in a fully realized
    environment unfolds (if it unfolds at all — see cycles) to a hole-free
    term. -/
theorem Unfolds.holeFree_of_fullyRealized {ev : Evidence} {Δ : HoleEnv} (g : GlobalWF ev Δ)
    (fr : Δ.FullyRealized) {Γ : Ctx} {e e' : Expr} {τ : Ty}
    (ht : HasType Δ Γ e τ) (hu : Unfolds Δ e e') : e'.HoleFree := by
  have ht' := hu.preserves_typing g ht
  unfold Expr.HoleFree
  cases hr : e'.refs with
  | nil => rfl
  | cons x xs =>
    exfalso
    have hx : x ∈ e'.refs := by rw [hr]; exact List.mem_cons_self
    obtain ⟨τ', htv⟩ := ht'.refs_declared x hx
    have hstuck := hu.refs_stuck x hx
    unfold HoleEnv.tyView at htv
    unfold HoleEnv.realizationOf at hstuck
    cases hh : Δ x with
    | none => simp [hh] at htv
    | some dh =>
      obtain ⟨ex, hex⟩ := fr x dh hh
      simp [hh, hex] at hstuck

/-! ## Cycles block unfolding -/

/-- Any term that unfolds refers only to holes that are not on a cycle. -/
theorem Unfolds.refs_not_cyclic {Δ : HoleEnv} {e e' : Expr} (hu : Unfolds Δ e e') :
    ∀ x ∈ e.refs, ¬ Reaches Δ x x := by
  induction hu with
  | var _ | boolLit _ | natLit _ => intro x hx; simp [Expr.refs] at hx
  | lam _ ih => exact ih
  | app _ _ ihf iha =>
    intro x hx
    simp only [Expr.refs, List.mem_append] at hx
    exact hx.elim (ihf x) (iha x)
  | refStuck hn =>
    intro x hx hr
    simp [Expr.refs] at hx; subst hx
    obtain ⟨c, hc, _⟩ := hr
    obtain ⟨_, he⟩ := hc.realized
    rw [hn] at he; exact nomatch he
  | refRealized hs _ ih =>
    intro x hx hr
    simp [Expr.refs] at hx; subst hx
    -- x → c →* x.  Then c is in the realization's refs, and c →* x → c.
    obtain ⟨c, hc, hcx⟩ := hr
    obtain ⟨e₀, he₀, hcmem⟩ := DependsOn.iff.mp hc
    rw [hs] at he₀; cases he₀
    exact ih c hcmem (Reaches.star_left hcx (Reaches.single hc))

/-- **A cyclic reference has no unfolding.** -/
theorem Unfolds.not_of_cyclic {Δ : HoleEnv} {a : HoleId} (hc : Reaches Δ a a) :
    ¬ ∃ e', Unfolds Δ (.holeRef a) e' := by
  rintro ⟨e', hu⟩
  exact hu.refs_not_cyclic a (by simp [Expr.refs]) hc

/-! ## Acyclic designs unfold -/

/-- Every element of a list is below its `max (rank + 1)` fold. -/
theorem lt_rankBound (rank : HoleId → Nat) :
    ∀ (l : List HoleId), ∀ x ∈ l, rank x < l.foldr (fun y acc => max (rank y + 1) acc) 0
  | [], _, hx => by simp at hx
  | y :: ys, x, hx => by
    simp only [List.foldr]
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (lt_rankBound rank ys x hmem) (Nat.le_max_right _ _)

/-- In an acyclic environment every term unfolds. -/
theorem Unfolds.exists_of_acyclic {Δ : HoleEnv} (ha : Acyclic Δ) (e : Expr) :
    ∃ e', Unfolds Δ e e' := by
  obtain ⟨rank, hr⟩ := ha
  -- strong induction on a bound for the ranks of the referenced holes
  suffices key : ∀ n, ∀ e : Expr, (∀ x ∈ e.refs, rank x < n) → ∃ e', Unfolds Δ e e' from
    key _ e (lt_rankBound rank e.refs)
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihn =>
    intro e hb
    induction e with
    | var i => exact ⟨_, .var i⟩
    | boolLit b => exact ⟨_, .boolLit b⟩
    | natLit k => exact ⟨_, .natLit k⟩
    | lam dom b ih => obtain ⟨b', hb'⟩ := ih hb; exact ⟨_, .lam hb'⟩
    | app f a ihf iha =>
      obtain ⟨f', hf'⟩ := ihf fun x hx => hb x (by simp [Expr.refs, hx])
      obtain ⟨a', ha'⟩ := iha fun x hx => hb x (by simp [Expr.refs, hx])
      exact ⟨_, .app hf' ha'⟩
    | holeRef h =>
      cases hs : Δ.realizationOf h with
      | none => exact ⟨_, .refStuck hs⟩
      | some e₀ =>
        -- every hole `e₀` refers to has rank < rank h < n
        have hh : rank h < n := hb h (by simp [Expr.refs])
        obtain ⟨e₀', he₀'⟩ := ihn (rank h) hh e₀ fun x hx =>
          hr h x (DependsOn.iff.mpr ⟨e₀, hs, hx⟩)
        exact ⟨_, .refRealized hs he₀'⟩

end BDL
