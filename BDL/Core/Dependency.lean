import BDL.Core.Env

/-!
# Dependency — the reference graph and the unfolding semantics

`DependsOn Δ a b`: the realization of `a` refers to `b`.  (Specs in this
model contain no references, so there is no interface-level dependency yet;
that is future work.)

The semantics of a design at this phase is *unfolding*: replace every
reference to a realized declaration by its body, recursively, stopping at
unresolved declarations.  A fully realized, well-typed design unfolds to a
reference-free program of the same type (`Unfolds.refFree_of_fullyRealized`).

Cycles: a reference cycle through realized declarations has **no unfolding
at all** (`Unfolds.not_of_cyclic`).  This is the Phase-1 sense in which a
structural cycle is harmful: the pure fragment has no fixpoints, so a cyclic
definition denotes nothing.  Whether some cycles become harmless once a
delay operator exists is deferred to the temporal phases.
-/

namespace BDL

/-! ## Dependency relation -/

/-- `a`'s realization refers to `b`.  Decidable by construction. -/
def dependsOn (Δ : DeclEnv) (a b : DeclId) : Bool :=
  match Δ.realizationOf a with
  | some e => decide (b ∈ e.refs)
  | none => false

def DependsOn (Δ : DeclEnv) (a b : DeclId) : Prop := dependsOn Δ a b = true

instance (Δ : DeclEnv) (a b : DeclId) : Decidable (DependsOn Δ a b) :=
  inferInstanceAs (Decidable (dependsOn Δ a b = true))

theorem DependsOn.iff {Δ : DeclEnv} {a b : DeclId} :
    DependsOn Δ a b ↔ ∃ e, Δ.realizationOf a = some e ∧ b ∈ e.refs := by
  unfold DependsOn dependsOn
  cases h : Δ.realizationOf a with
  | none => simp
  | some e => simp

/-- Only realized declarations have outgoing edges: a cycle can never pass
    through an unresolved declaration. -/
theorem DependsOn.realized {Δ : DeclEnv} {a b : DeclId} (h : DependsOn Δ a b) :
    ∃ e, Δ.realizationOf a = some e :=
  let ⟨e, he, _⟩ := DependsOn.iff.mp h; ⟨e, he⟩

/-- Finite view of the graph, for display. -/
def depEdges (l : List DesignDecl) : List (DeclId × DeclId) :=
  l.flatMap fun dh =>
    match dh.realization with
    | some e => e.refs.map (dh.id, ·)
    | none => []

/-- Transitive closure of `DependsOn`. -/
def Reaches (Δ : DeclEnv) (a b : DeclId) : Prop :=
  ∃ c, DependsOn Δ a c ∧ Star (DependsOn Δ) c b

theorem Reaches.single {Δ : DeclEnv} {a b : DeclId} (h : DependsOn Δ a b) : Reaches Δ a b :=
  ⟨b, h, .refl b⟩

theorem Reaches.star_left {Δ : DeclEnv} {a b c : DeclId}
    (h : Star (DependsOn Δ) a b) (r : Reaches Δ b c) : Reaches Δ a c := by
  induction h with
  | refl _ => exact r
  | step hab _ ih =>
    obtain ⟨d, hd, hs⟩ := ih r
    exact ⟨_, hab, .step hd hs⟩

theorem Reaches.toStar {Δ : DeclEnv} {a b : DeclId} (r : Reaches Δ a b) : Star (DependsOn Δ) a b :=
  let ⟨_, h, hs⟩ := r; .step h hs

/-- A cycle: some declaration reaches itself. -/
def Cyclic (Δ : DeclEnv) : Prop := ∃ a, Reaches Δ a a

/-- Acyclicity, witnessed by a rank that strictly decreases along edges. -/
def Acyclic (Δ : DeclEnv) : Prop :=
  ∃ rank : DeclId → Nat, ∀ a b, DependsOn Δ a b → rank b < rank a

theorem Acyclic.not_cyclic {Δ : DeclEnv} (h : Acyclic Δ) : ¬ Cyclic Δ := by
  obtain ⟨rank, hr⟩ := h
  rintro ⟨a, c, hac, hca⟩
  have : ∀ {x y}, Star (DependsOn Δ) x y → rank y ≤ rank x := by
    intro x y hs
    induction hs with
    | refl _ => exact Nat.le_refl _
    | step hxy _ ih => exact Nat.le_trans ih (Nat.le_of_lt (hr _ _ hxy))
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hr _ _ hac) (this hca))

/-! ## Instantaneous dependency and causality (Phase 4)

`DependsOn` counts every reference; `InstDependsOn` counts only references
not under a `delay`.  Structural cycles that pass through a delay are not
instantaneous cycles.  `Causal` is `Acyclic` for the instantaneous graph,
with a bound on ranks (needed so that delayed operands can be evaluated at
the previous tick under any rank). -/

def instDependsOn (Δ : DeclEnv) (a b : DeclId) : Bool :=
  match Δ.realizationOf a with
  | some e => decide (b ∈ e.instRefs)
  | none => false

def InstDependsOn (Δ : DeclEnv) (a b : DeclId) : Prop := instDependsOn Δ a b = true

instance (Δ : DeclEnv) (a b : DeclId) : Decidable (InstDependsOn Δ a b) :=
  inferInstanceAs (Decidable (instDependsOn Δ a b = true))

theorem InstDependsOn.iff {Δ : DeclEnv} {a b : DeclId} :
    InstDependsOn Δ a b ↔ ∃ e, Δ.realizationOf a = some e ∧ b ∈ e.instRefs := by
  unfold InstDependsOn instDependsOn
  cases h : Δ.realizationOf a with
  | none => simp
  | some e => simp

/-- Instantaneous dependency is a sub-relation of structural dependency. -/
theorem InstDependsOn.toDependsOn {Δ : DeclEnv} {a b : DeclId} (h : InstDependsOn Δ a b) : DependsOn Δ a b := by
  obtain ⟨e, he, hb⟩ := InstDependsOn.iff.mp h
  exact DependsOn.iff.mpr ⟨e, he, instRefs_sub hb⟩
where
  instRefs_sub {e : Expr} {b : DeclId} : b ∈ e.instRefs → b ∈ e.refs := by
    induction e with
    | var _ | boolLit _ | natLit _ | prim _ | declRef _ => intro h; simp_all [Expr.instRefs, Expr.refs]
    | lam _ b ih => exact ih
    | app f a ihf iha =>
      intro h
      simp only [Expr.instRefs, Expr.refs, List.mem_append] at h ⊢
      exact h.elim (fun h => .inl (ihf h)) (fun h => .inr (iha h))
    | rep e ih => exact ih
    | mk _ e ih => exact ih
    | delay i e ihi _ =>
      intro h
      simp only [Expr.instRefs, Expr.refs, List.mem_append] at h ⊢
      exact .inl (ihi h)
    | sync _ i e ihi _ =>
      intro h
      simp only [Expr.instRefs, Expr.refs, List.mem_append] at h ⊢
      exact .inl (ihi h)
    | fold f z l ihf ihz ihl =>
      intro h
      simp only [Expr.instRefs, Expr.refs, List.mem_append] at h ⊢
      rcases h with (h | h) | h
      · exact .inl (.inl (ihf h))
      · exact .inl (.inr (ihz h))
      · exact .inr (ihl h)

/-- Every realization is delay-free: the Phase-1 timeless fragment. -/
def DeclEnv.DelayFree (Δ : DeclEnv) : Prop :=
  ∀ d e, Δ.realizationOf d = some e → e.DelayFree

theorem DeclEnv.DelayFree.ofList {l : List DesignDecl}
    (h : ∀ dh ∈ l, ∀ e, dh.realization = some e → e.DelayFree) : DeclEnv.DelayFree (.ofList l) := by
  intro d e he
  simp only [DeclEnv.realizationOf, Option.bind_eq_some_iff] at he
  obtain ⟨dh, hdh, hre⟩ := he
  exact h dh (DeclEnv.ofList_some hdh).1 e hre

/-- In the timeless fragment the two graphs coincide. -/
theorem InstDependsOn_iff_DependsOn_of_delayFree {Δ : DeclEnv} (h : Δ.DelayFree) (a b : DeclId) :
    InstDependsOn Δ a b ↔ DependsOn Δ a b := by
  rw [InstDependsOn.iff, DependsOn.iff]
  constructor
  · rintro ⟨e, he, hb⟩; exact ⟨e, he, by rw [← Expr.instRefs_of_delayFree (h a e he)]; exact hb⟩
  · rintro ⟨e, he, hb⟩; exact ⟨e, he, by rw [Expr.instRefs_of_delayFree (h a e he)]; exact hb⟩

/-- **Causality**: the instantaneous graph is acyclic, witnessed by a bounded
    rank. -/
def Causal (Δ : DeclEnv) : Prop :=
  ∃ (rank : DeclId → Nat) (R : Nat), (∀ d, rank d < R) ∧ ∀ a b, InstDependsOn Δ a b → rank b < rank a

/-- Structural acyclicity (with a bounded rank) implies causality: every
    Phase-1-acceptable design is causal. -/
theorem Causal.of_acyclic_bounded {Δ : DeclEnv} (rank : DeclId → Nat) (R : Nat) (hR : ∀ d, rank d < R)
    (h : ∀ a b, DependsOn Δ a b → rank b < rank a) : Causal Δ :=
  ⟨rank, R, hR, fun a b hab => h a b hab.toDependsOn⟩

/-- In the timeless fragment causality is exactly (bounded) acyclicity. -/
theorem Causal_iff_acyclic_of_delayFree {Δ : DeclEnv} (h : Δ.DelayFree) :
    Causal Δ ↔ ∃ (rank : DeclId → Nat) (R : Nat), (∀ d, rank d < R) ∧ ∀ a b, DependsOn Δ a b → rank b < rank a := by
  constructor
  · rintro ⟨rank, R, hR, hr⟩
    exact ⟨rank, R, hR, fun a b hab => hr a b ((InstDependsOn_iff_DependsOn_of_delayFree h a b).mpr hab)⟩
  · rintro ⟨rank, R, hR, hr⟩
    exact ⟨rank, R, hR, fun a b hab => hr a b ((InstDependsOn_iff_DependsOn_of_delayFree h a b).mp hab)⟩

/-! ## Unfolding semantics -/

/-- Replace references to realized declarations by their bodies, recursively;
    references to unresolved (or undeclared) declarations are left in place. -/
inductive Unfolds (Δ : DeclEnv) : Expr → Expr → Prop where
  | var (i : Nat) : Unfolds Δ (.var i) (.var i)
  | boolLit (b : Bool) : Unfolds Δ (.boolLit b) (.boolLit b)
  | natLit (n : Nat) : Unfolds Δ (.natLit n) (.natLit n)
  | lam {dom : Ty} {b b' : Expr} : Unfolds Δ b b' → Unfolds Δ (.lam dom b) (.lam dom b')
  | app {f f' a a' : Expr} : Unfolds Δ f f' → Unfolds Δ a a' → Unfolds Δ (.app f a) (.app f' a')
  | refStuck {h : DeclId} : Δ.realizationOf h = none → Unfolds Δ (.declRef h) (.declRef h)
  | refRealized {h : DeclId} {e e' : Expr} :
      Δ.realizationOf h = some e → Unfolds Δ e e' → Unfolds Δ (.declRef h) e'
  | rep {e e' : Expr} : Unfolds Δ e e' → Unfolds Δ (.rep e) (.rep e')
  | mk {s : ConceptId} {e e' : Expr} : Unfolds Δ e e' → Unfolds Δ (.mk s e) (.mk s e')
  | prim (p : Prim) : Unfolds Δ (.prim p) (.prim p)
  | delay {i i' e e' : Expr} : Unfolds Δ i i' → Unfolds Δ e e' → Unfolds Δ (.delay i e) (.delay i' e')
  | sync {c : ClockId} {i i' e e' : Expr} : Unfolds Δ i i' → Unfolds Δ e e' → Unfolds Δ (.sync c i e) (.sync c i' e')
  | fold {f f' z z' l l' : Expr} :
      Unfolds Δ f f' → Unfolds Δ z z' → Unfolds Δ l l' → Unfolds Δ (.fold f z l) (.fold f' z' l')

/-- Unfolding is deterministic. -/
theorem Unfolds.det {Δ : DeclEnv} {e e₁ e₂ : Expr}
    (h₁ : Unfolds Δ e e₁) (h₂ : Unfolds Δ e e₂) : e₁ = e₂ := by
  induction h₁ generalizing e₂ with
  | var _ | boolLit _ | natLit _ | prim _ => cases h₂; rfl
  | lam _ ih => cases h₂ with | lam hb => rw [ih hb]
  | app _ _ ihf iha => cases h₂ with | app hf ha => rw [ihf hf, iha ha]
  | rep _ ih => cases h₂ with | rep he => rw [ih he]
  | mk _ ih => cases h₂ with | mk he => rw [ih he]
  | delay _ _ ihi ihe => cases h₂ with | delay hi he => rw [ihi hi, ihe he]
  | sync _ _ ihi ihe => cases h₂ with | sync hi he => rw [ihi hi, ihe he]
  | fold _ _ _ ihf ihz ihl => cases h₂ with | fold hf hz hl => rw [ihf hf, ihz hz, ihl hl]
  | refStuck hn =>
    cases h₂ with
    | refStuck _ => rfl
    | refRealized hs _ => rw [hn] at hs; exact nomatch hs
  | refRealized hs _ ih =>
    cases h₂ with
    | refStuck hn => rw [hn] at hs; exact nomatch hs
    | refRealized hs' hu => rw [hs] at hs'; cases hs'; exact ih hu

/-- Whatever references remain after unfolding are to unrealized declarations. -/
theorem Unfolds.refs_stuck {Δ : DeclEnv} {e e' : Expr} (h : Unfolds Δ e e') :
    ∀ x ∈ e'.refs, Δ.realizationOf x = none := by
  induction h with
  | var _ | boolLit _ | natLit _ | prim _ => intro x hx; simp [Expr.refs] at hx
  | rep _ ih => exact ih
  | mk _ ih => exact ih
  | lam _ ih => exact ih
  | app _ _ ihf iha =>
    intro x hx
    simp only [Expr.refs, List.mem_append] at hx
    exact hx.elim (ihf x) (iha x)
  | delay _ _ ihi ihe =>
    intro x hx
    simp only [Expr.refs, List.mem_append] at hx
    exact hx.elim (ihi x) (ihe x)
  | sync _ _ ihi ihe =>
    intro x hx
    simp only [Expr.refs, List.mem_append] at hx
    exact hx.elim (ihi x) (ihe x)
  | fold _ _ _ ihf ihz ihl =>
    intro x hx
    simp only [Expr.refs, List.mem_append] at hx
    exact hx.elim (fun h => h.elim (ihf x) (ihz x)) (ihl x)
  | refStuck hn => intro x hx; simp [Expr.refs] at hx; subst hx; exact hn
  | refRealized _ _ ih => exact ih

/-- **Type preservation.**  In a globally well-formed design, unfolding
    preserves typing — under the universal grant.  Each inlined body was
    typed under the grant of its *own* signature, so the flattened term
    carries constructions that were individually authorized at their
    declarations; the unfolded program is the implementation, where the
    design-time isolation has been discharged, not violated
    (`HasType.constructs_granted` holds for every inlined body separately). -/
theorem Unfolds.preserves_typing {ev : Evidence} {Θ : ConceptEnv} {Δ : DeclEnv} (g : GlobalWF ev Θ Δ)
    (hd : Δ.DelayFree) {e e' : Expr} (hu : Unfolds Δ e e') :
    ∀ {G : Grant} {Γ : Ctx} {τ : Ty}, HasType Θ Δ G Γ e τ → HasType Θ Δ Grant.all Γ e' τ := by
  induction hu with
  | var _ | boolLit _ | natLit _ | prim _ => intro _ _ _ ht; exact ht.to_all
  | lam _ ih =>
    intro G Γ τ ht
    cases ht with | lam hb => exact .lam (ih hb)
  | app _ _ ihf iha =>
    intro G Γ τ ht
    cases ht with | app hf ha => exact .app (ihf hf) (iha ha)
  | rep _ ih =>
    intro G Γ τ ht
    cases ht with | rep hΘ he => exact .rep hΘ (ih he)
  | mk _ ih =>
    intro G Γ τ ht
    cases ht with | mk _ hΘ he => exact .mk trivial hΘ (ih he)
  | delay _ _ ihi ihe =>
    intro G Γ τ ht
    cases ht with | delay hd hi he => exact .delay hd (ihi hi) (ihe he)
  | sync _ _ ihi ihe =>
    intro G Γ τ ht
    cases ht with | sync hd hi he => exact .sync hd (ihi hi) (ihe he)
  | fold _ _ _ ihf ihz ihl =>
    intro G Γ τ ht
    cases ht with | fold hf hz hl => exact .fold (ihf hf) (ihz hz) (ihl hl)
  | refStuck _ => intro _ _ _ ht; exact ht.to_all
  | @refRealized d b _ hs _ ih =>
    intro G Γ τ ht
    cases ht with
    | declRef htv =>
      have hdf := hd d b hs
      simp only [DeclEnv.realizationOf, DeclEnv.tyView, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at hs htv
      obtain ⟨dh, hh, hre⟩ := hs
      obtain ⟨dh', hh', hty⟩ := htv
      rw [hh] at hh'; cases hh'
      subst hty
      exact ih (((g.wellFormed hh) _ hre).1.of_closed hdf Γ)

/-- Every declaration is realized. -/
def DeclEnv.FullyRealized (Δ : DeclEnv) : Prop :=
  ∀ id dh, Δ id = some dh → ∃ e, dh.realization = some e

/-- **Executable designs flatten.**  A well-typed term in a fully realized
    environment unfolds (if it unfolds at all — see cycles) to a
    reference-free term. -/
theorem Unfolds.refFree_of_fullyRealized {ev : Evidence} {Θ : ConceptEnv} {Δ : DeclEnv} (g : GlobalWF ev Θ Δ)
    (hd : Δ.DelayFree) (fr : Δ.FullyRealized) {G : Grant} {Γ : Ctx} {e e' : Expr} {τ : Ty}
    (ht : HasType Θ Δ G Γ e τ) (hu : Unfolds Δ e e') : e'.RefFree := by
  have ht' := hu.preserves_typing g hd ht
  unfold Expr.RefFree
  cases hr : e'.refs with
  | nil => rfl
  | cons x xs =>
    exfalso
    have hx : x ∈ e'.refs := by rw [hr]; exact List.mem_cons_self
    obtain ⟨τ', htv⟩ := ht'.refs_declared x hx
    have hstuck := hu.refs_stuck x hx
    unfold DeclEnv.tyView at htv
    unfold DeclEnv.realizationOf at hstuck
    cases hh : Δ x with
    | none => simp [hh] at htv
    | some dh =>
      obtain ⟨ex, hex⟩ := fr x dh hh
      simp [hh, hex] at hstuck

/-! ## Cycles block unfolding -/

/-- Any term that unfolds refers only to declarations that are not on a cycle. -/
theorem Unfolds.refs_not_cyclic {Δ : DeclEnv} {e e' : Expr} (hu : Unfolds Δ e e') :
    ∀ x ∈ e.refs, ¬ Reaches Δ x x := by
  induction hu with
  | var _ | boolLit _ | natLit _ | prim _ => intro x hx; simp [Expr.refs] at hx
  | rep _ ih => exact ih
  | mk _ ih => exact ih
  | lam _ ih => exact ih
  | app _ _ ihf iha =>
    intro x hx
    simp only [Expr.refs, List.mem_append] at hx
    exact hx.elim (ihf x) (iha x)
  | delay _ _ ihi ihe =>
    intro x hx
    simp only [Expr.refs, List.mem_append] at hx
    exact hx.elim (ihi x) (ihe x)
  | sync _ _ ihi ihe =>
    intro x hx
    simp only [Expr.refs, List.mem_append] at hx
    exact hx.elim (ihi x) (ihe x)
  | fold _ _ _ ihf ihz ihl =>
    intro x hx
    simp only [Expr.refs, List.mem_append] at hx
    exact hx.elim (fun h => h.elim (ihf x) (ihz x)) (ihl x)
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
theorem Unfolds.not_of_cyclic {Δ : DeclEnv} {a : DeclId} (hc : Reaches Δ a a) :
    ¬ ∃ e', Unfolds Δ (.declRef a) e' := by
  rintro ⟨e', hu⟩
  exact hu.refs_not_cyclic a (by simp [Expr.refs]) hc

/-! ## Acyclic designs unfold -/

/-- Every element of a list is below its `max (rank + 1)` fold. -/
theorem lt_rankBound (rank : DeclId → Nat) :
    ∀ (l : List DeclId), ∀ x ∈ l, rank x < l.foldr (fun y acc => max (rank y + 1) acc) 0
  | [], _, hx => by simp at hx
  | y :: ys, x, hx => by
    simp only [List.foldr]
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (lt_rankBound rank ys x hmem) (Nat.le_max_right _ _)

/-- In an acyclic environment every term unfolds. -/
theorem Unfolds.exists_of_acyclic {Δ : DeclEnv} (ha : Acyclic Δ) (e : Expr) :
    ∃ e', Unfolds Δ e e' := by
  obtain ⟨rank, hr⟩ := ha
  -- strong induction on a bound for the ranks of the referenced declarations
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
    | rep e ih => obtain ⟨e', he'⟩ := ih hb; exact ⟨_, .rep he'⟩
    | mk s e ih => obtain ⟨e', he'⟩ := ih hb; exact ⟨_, .mk he'⟩
    | prim p => exact ⟨_, .prim p⟩
    | delay i e ihi ihe =>
      obtain ⟨i', hi'⟩ := ihi fun x hx => hb x (by simp [Expr.refs, hx])
      obtain ⟨e', he'⟩ := ihe fun x hx => hb x (by simp [Expr.refs, hx])
      exact ⟨_, .delay hi' he'⟩
    | sync c i e ihi ihe =>
      obtain ⟨i', hi'⟩ := ihi fun x hx => hb x (by simp [Expr.refs, hx])
      obtain ⟨e', he'⟩ := ihe fun x hx => hb x (by simp [Expr.refs, hx])
      exact ⟨_, .sync hi' he'⟩
    | fold f z l ihf ihz ihl =>
      obtain ⟨f', hf'⟩ := ihf fun x hx => hb x (by simp [Expr.refs, hx])
      obtain ⟨z', hz'⟩ := ihz fun x hx => hb x (by simp [Expr.refs, hx])
      obtain ⟨l', hl'⟩ := ihl fun x hx => hb x (by simp [Expr.refs, hx])
      exact ⟨_, .fold hf' hz' hl'⟩
    | declRef h =>
      cases hs : Δ.realizationOf h with
      | none => exact ⟨_, .refStuck hs⟩
      | some e₀ =>
        -- every declaration `e₀` refers to has rank < rank h < n
        have hh : rank h < n := hb h (by simp [Expr.refs])
        obtain ⟨e₀', he₀'⟩ := ihn (rank h) hh e₀ fun x hx =>
          hr h x (DependsOn.iff.mpr ⟨e₀, hs, hx⟩)
        exact ⟨_, .refRealized hs he₀'⟩

end BDL
