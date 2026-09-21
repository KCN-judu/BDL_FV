import BDL.Behavior.System
import BDL.Core.Producer

/-!
# Producer uniqueness under composition (Phase 20)

The invariant `ProducerUnique` (`Core/Producer`) survives flattening under a
boundary rule that mirrors `ExternalSingleDriver` for sinks: **a shared
concept is originated by at most one instance**, where a required port or a
parameter — a placeholder the system fills — counts as no origin; internal
concepts are freshened per instance and cannot collide
(`inst_sem_disjoint`).  Bindings relay (their bodies are typed under
`Grant.none`, so they construct nothing) and therefore add no origin.

* `ExternalSingleProducer S` — the boundary rule.
* `PortsBound S` — every required port and parameter is bound.
* `flatten_producerUnique` — templates unique + the rule + bound ports ⇒
  the flattened design is unique.
-/

namespace BDL

theorem Expr.rename_mkSet (r : Ren) : ∀ e : Expr, (e.rename r).mkSet = e.mkSet.map r.s
  | .var _ | .boolLit _ | .natLit _ | .declRef _ | .prim _ => by simp [Expr.rename, Expr.mkSet]
  | .lam _ b => by simp [Expr.rename, Expr.mkSet, Expr.rename_mkSet r b]
  | .app f a => by simp [Expr.rename, Expr.mkSet, Expr.rename_mkSet r f, Expr.rename_mkSet r a]
  | .rep e => by simp [Expr.rename, Expr.mkSet, Expr.rename_mkSet r e]
  | .mk s e => by simp [Expr.rename, Expr.mkSet, Expr.rename_mkSet r e]
  | .delay i e => by simp [Expr.rename, Expr.mkSet, Expr.rename_mkSet r i, Expr.rename_mkSet r e]
  | .sync _ i e => by simp [Expr.rename, Expr.mkSet, Expr.rename_mkSet r i, Expr.rename_mkSet r e]
  | .fold f z l => by
    simp [Expr.rename, Expr.mkSet, Expr.rename_mkSet r f, Expr.rename_mkSet r z, Expr.rename_mkSet r l]

theorem Expr.rename_originSet (r : Ren) : ∀ e : Expr, (e.rename r).originSet = e.originSet.map r.s
  | .var _ | .boolLit _ | .natLit _ | .declRef _ | .prim _ => by simp [Expr.rename, Expr.originSet]
  | .lam _ b => by simp [Expr.rename, Expr.originSet, Expr.rename_originSet r b]
  | .app f a => by simp [Expr.rename, Expr.originSet, Expr.rename_originSet r f, Expr.rename_originSet r a]
  | .rep e => by simp [Expr.rename, Expr.originSet, Expr.rename_originSet r e]
  | .mk s e => by simp [Expr.rename, Expr.originSet, Expr.rename_originSet r e]
  | .delay i e => by simp [Expr.rename, Expr.originSet, Expr.rename_originSet r e]
  | .sync _ i e => by simp [Expr.rename, Expr.originSet, Expr.rename_originSet r e]
  | .fold f z l => by
    simp [Expr.rename, Expr.originSet, Expr.rename_originSet r f, Expr.rename_originSet r z, Expr.rename_originSet r l]

theorem DesignDecl.rename_origins (r : Ren) (h : DesignDecl) : (h.rename r).origins = h.origins.map r.s := by
  cases hr : h.realization with
  | none => simp [DesignDecl.rename, DesignDecl.origins, hr, DeclInterface.rename, Ty.rename_grant]
  | some b => simp [DesignDecl.rename, DesignDecl.origins, hr, Expr.rename_originSet]

/-- A term typed under no grant originates nothing. -/
theorem Expr.originSet_nil_of_noGrant {Θ : ConceptEnv} {Δ : DeclEnv} {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : HasType Θ Δ Grant.none Γ e τ) : e.originSet = [] := by
  cases hm : e.originSet with
  | nil => rfl
  | cons s _ =>
    have : e.constructs s := Expr.constructs_of_mem_originSet s e (by rw [hm]; exact List.mem_cons_self)
    exact (h.constructs_granted s this).elim

namespace BehaviorSystem

/-- A required port or a parameter: a placeholder the system fills. -/
def IsPort (C : BehaviorComponent) (d : DeclId) : Prop :=
  ∃ p ∈ C.iface.required ++ C.iface.params, p.id = d

/-- **The boundary rule**: at most one instance — and one declaration of it
    — originates each shared concept, ports not counting. -/
def ExternalSingleProducer (S : BehaviorSystem) : Prop :=
  ∀ k₁ I₁ d₁ k₂ I₂ d₂ C, S.instAt k₁ = some I₁ → S.instAt k₂ = some I₂ →
    Produces I₁.comp.design.Δ d₁ C → I₁.comp.internalSem C = false → ¬ IsPort I₁.comp d₁ →
    Produces I₂.comp.design.Δ d₂ C → I₂.comp.internalSem C = false → ¬ IsPort I₂.comp d₂ →
    k₁ = k₂ ∧ d₁ = d₂

/-- Every required port and parameter of every instance is bound. -/
def PortsBound (S : BehaviorSystem) : Prop :=
  ∀ k I p, S.instAt k = some I → p ∈ I.comp.iface.required ++ I.comp.iface.params →
    ∃ b ∈ S.bindings, b.dstInst = k ∧ b.dst = p.id

/-- Every declaration is stored under its own identity. -/
def StoredId (Δ : DeclEnv) : Prop := ∀ id h, Δ id = some h → h.id = id

theorem storedId_update {Δ : DeclEnv} (hs : StoredId Δ) {h' : DesignDecl} : StoredId (Δ.update h') := by
  intro id h hd
  by_cases e : id = h'.id
  · subst e; rw [DeclEnv.update_self] at hd; cases hd; rfl
  · rw [DeclEnv.update_other _ _ e] at hd; exact hs id h hd

/-- An origin of the union is the renamed origin of one instance. -/
theorem produces_union {S : BehaviorSystem} {id : DeclId} {C : SemanticId}
    (h : Produces S.unionΔ id C) :
    ∃ k n I, decode S.W id.n = some (k, n) ∧ S.instAt k = some I ∧
      ∃ C₀, C = (S.ren k I).s C₀ ∧ Produces I.comp.design.Δ ⟨n⟩ C₀ := by
  obtain ⟨h, hd, hc⟩ := h
  unfold unionΔ at hd
  cases hdec : decode S.W id.n with
  | none => simp [hdec] at hd
  | some kn =>
    obtain ⟨k, n⟩ := kn
    simp only [hdec] at hd
    cases hI : S.instAt k with
    | none => simp [hI] at hd
    | some I =>
      simp only [hI] at hd
      cases hΔ : I.comp.design.Δ ⟨n⟩ with
      | none => simp [hΔ] at hd
      | some h₀ =>
        rw [hΔ] at hd
        simp only [Option.map_some, Option.some.injEq] at hd
        subst hd
        rw [DesignDecl.rename_origins, List.mem_map] at hc
        obtain ⟨C₀, hC₀, rfl⟩ := hc
        exact ⟨k, n, I, rfl, hI, C₀, rfl, h₀, hΔ, hC₀⟩

theorem storedId_union {S : BehaviorSystem} (hstored : ∀ k I, S.instAt k = some I → StoredId I.comp.design.Δ) :
    StoredId S.unionΔ := by
  intro id h hd
  unfold unionΔ at hd
  cases hdec : decode S.W id.n with
  | none => simp [hdec] at hd
  | some kn =>
    obtain ⟨k, n⟩ := kn
    simp only [hdec] at hd
    cases hI : S.instAt k with
    | none => simp [hI] at hd
    | some I =>
      simp only [hI] at hd
      cases hΔ : I.comp.design.Δ ⟨n⟩ with
      | none => simp [hΔ] at hd
      | some h₀ =>
        rw [hΔ] at hd
        simp only [Option.map_some, Option.some.injEq] at hd
        subst hd
        have := hstored k I hI ⟨n⟩ h₀ hΔ
        obtain ⟨hid, -, -⟩ := decode_some hdec
        simp only [DesignDecl.rename, ren, Ren.inst, this]
        cases id; simp only at hid; simp [hid]

/-- A binding's body constructs nothing. -/
theorem bindingBody_originSet {S : BehaviorSystem} {ev : Evidence} (cw : ComposeWF ev S) {b : Binding}
    (hb : b ∈ S.bindings) : (S.bindingBody b).originSet = [] := by
  obtain ⟨Id, -, pd, -, -, hsrc⟩ := cw.bindings b hb
  unfold bindingBody
  cases hs : b.src with
  | const e =>
    rw [hs] at hsrc
    obtain ⟨-, -, -, ht, -⟩ := hsrc
    exact Expr.originSet_nil_of_noGrant ht
  | port k id =>
    rw [hs] at hsrc
    obtain ⟨Is, -, ps, -, -, -, -, htr⟩ := hsrc
    cases htp : b.transport with
    | none => simp [Expr.originSet]
    | some init =>
      rw [htp] at htr
      obtain ⟨-, -, -, -, ht, -⟩ := htr
      have := Expr.originSet_nil_of_noGrant ht
      cases hK : S.unionΚ (S.declOf k id) <;> simp [hK, Expr.originSet]

/-- Through the bindings: an origin of the result was an origin before and
    is no binding's destination. -/
theorem produces_foldl {S : BehaviorSystem} (hrelay : ∀ b ∈ S.bindings, (S.bindingBody b).originSet = []) :
    ∀ (bs : List Binding) (Δ : DeclEnv), (∀ b ∈ bs, b ∈ S.bindings) → StoredId Δ →
      ∀ {id C}, Produces (bs.foldl (applyBinding S) Δ) id C →
        Produces Δ id C ∧ ∀ b ∈ bs, S.declOf b.dstInst b.dst ≠ id
  | [], Δ, _, _, _, _, h => ⟨h, fun _ hb => nomatch hb⟩
  | b :: bs, Δ, hsub, hs, id, C, h => by
    simp only [List.foldl_cons] at h
    have hsub' : ∀ b' ∈ bs, b' ∈ S.bindings := fun b' hb' => hsub b' (List.mem_cons_of_mem _ hb')
    have hs' : StoredId (applyBinding S Δ b) := by
      unfold applyBinding
      cases Δ (S.declOf b.dstInst b.dst) with
      | none => exact hs
      | some h => exact storedId_update hs
    obtain ⟨h₁, h₂⟩ := produces_foldl hrelay bs _ hsub' hs' h
    refine ⟨?_, ?_⟩
    · unfold applyBinding at h₁
      cases hΔ : Δ (S.declOf b.dstInst b.dst) with
      | none => simp only [hΔ] at h₁; exact h₁
      | some hd =>
        simp only [hΔ] at h₁
        rcases h₁.of_update with ⟨-, hc⟩ | ⟨-, hp⟩
        · simp [DesignDecl.origins, hrelay b (hsub b List.mem_cons_self)] at hc
        · exact hp
    · intro b' hb'
      rcases List.mem_cons.mp hb' with rfl | hb'
      · intro he
        unfold applyBinding at h₁
        cases hΔ : Δ (S.declOf b'.dstInst b'.dst) with
        | none =>
          simp only [hΔ] at h₁
          obtain ⟨_, hd, -⟩ := h₁
          rw [he] at hΔ; rw [hΔ] at hd; exact nomatch hd
        | some hd =>
          simp only [hΔ] at h₁
          have hid : hd.id = S.declOf b'.dstInst b'.dst := hs _ _ hΔ
          rcases h₁.of_update with ⟨-, hc⟩ | ⟨hne, -⟩
          · simp [DesignDecl.origins, hrelay b' (hsub b' List.mem_cons_self)] at hc
          · exact hne (he ▸ hid.symm)
      · exact h₂ b' hb'

/-- **Flattening preserves the invariant.**  Hypotheses: every template is
    stored under its own identities and producer-unique; the bindings relay;
    the boundary rule; every originated concept identity is below the width
    (a well-formedness fact taken as a hypothesis); every required port and
    parameter is bound. -/
theorem flatten_producerUnique {S : BehaviorSystem}
    (hstored : ∀ k I, S.instAt k = some I → StoredId I.comp.design.Δ)
    (hrelay : ∀ b ∈ S.bindings, (S.bindingBody b).originSet = [])
    (hT : ∀ k I, S.instAt k = some I → ProducerUnique I.comp.design.Δ)
    (hshared : ExternalSingleProducer S)
    (hbound : ∀ k I d C, S.instAt k = some I → Produces I.comp.design.Δ d C → C.n < S.W)
    (hports : PortsBound S) : ProducerUnique S.flattenΔ := by
  intro C id₁ id₂ p₁ p₂
  obtain ⟨u₁, nb₁⟩ := produces_foldl hrelay S.bindings S.unionΔ (fun _ h => h) (storedId_union hstored) p₁
  obtain ⟨u₂, nb₂⟩ := produces_foldl hrelay S.bindings S.unionΔ (fun _ h => h) (storedId_union hstored) p₂
  obtain ⟨k₁, n₁, I₁, dec₁, hI₁, C₁, hC₁, q₁⟩ := produces_union u₁
  obtain ⟨k₂, n₂, I₂, dec₂, hI₂, C₂, hC₂, q₂⟩ := produces_union u₂
  obtain ⟨e₁, lt₁, hW⟩ := decode_some dec₁
  obtain ⟨e₂, lt₂, -⟩ := decode_some dec₂
  have b₁ := hbound k₁ I₁ _ _ hI₁ q₁
  have b₂ := hbound k₂ I₂ _ _ hI₂ q₂
  have hren : (S.ren k₁ I₁).s C₁ = (S.ren k₂ I₂).s C₂ := hC₁ ▸ hC₂
  -- the instance and the local identity coincide
  suffices hk : k₁ = k₂ ∧ n₁ = n₂ by
    obtain ⟨rfl, rfl⟩ := hk
    cases id₁; cases id₂; simp only at e₁ e₂; simp [e₁, e₂]
  cases hi₁ : I₁.comp.internalSem C₁ with
  | true =>
    cases hi₂ : I₂.comp.internalSem C₂ with
    | true =>
      obtain ⟨rfl, rfl⟩ := inst_sem_disjoint hW hi₁ hi₂ b₁ b₂ hren
      rw [hI₁] at hI₂; cases hI₂
      have := hT k₁ I₁ hI₁ C₁ ⟨n₁⟩ ⟨n₂⟩ q₁ q₂
      exact ⟨rfl, by cases this; rfl⟩
    | false =>
      exfalso
      have : (S.ren k₂ I₂).s C₂ = C₂ := by simp [ren, Ren.inst, hi₂]
      rw [this] at hren
      exact inst_sem_not_global hW hi₁ b₂ hren
  | false =>
    cases hi₂ : I₂.comp.internalSem C₂ with
    | true =>
      exfalso
      have : (S.ren k₁ I₁).s C₁ = C₁ := by simp [ren, Ren.inst, hi₁]
      rw [this] at hren
      exact inst_sem_not_global hW hi₂ b₁ hren.symm
    | false =>
      have e : C₁ = C₂ := by simpa [ren, Ren.inst, hi₁, hi₂] using hren
      subst e
      -- neither is a port: a port is bound, and a bound destination is no origin
      have notPort : ∀ {k I n id}, S.instAt k = some I → id.n = fresh S.W k n →
          (∀ b ∈ S.bindings, S.declOf b.dstInst b.dst ≠ id) → ¬ IsPort I.comp ⟨n⟩ := by
        intro k I n id hI hid nb ⟨p, hp, hpid⟩
        obtain ⟨b, hb, hk, hd⟩ := hports k I p hI hp
        apply nb b hb
        simp only [declOf, hk, hd, hpid]
        cases id; simp only at hid; simp [hid]
      have := hshared k₁ I₁ ⟨n₁⟩ k₂ I₂ ⟨n₂⟩ C₁ hI₁ hI₂ q₁ hi₁ (notPort hI₁ e₁ nb₁) q₂ hi₂ (notPort hI₂ e₂ nb₂)
      exact ⟨this.1, by cases this.2; rfl⟩

/-- The same under the composition judgment, which supplies the stored
    identities (template well-formedness) and the relaying bindings (typed
    under `Grant.none`). -/
theorem flatten_producerUnique_of_composeWF {S : BehaviorSystem} {ev : Evidence} (cw : ComposeWF ev S)
    (hT : ∀ k I, S.instAt k = some I → ProducerUnique I.comp.design.Δ)
    (hshared : ExternalSingleProducer S)
    (hbound : ∀ k I d C, S.instAt k = some I → Produces I.comp.design.Δ d C → C.n < S.W)
    (hports : PortsBound S) : ProducerUnique S.flattenΔ :=
  flatten_producerUnique (fun k I hI id h hd => ((cw.insts k I hI).1.wf.global id h hd).1)
    (fun _ hb => bindingBody_originSet cw hb) hT hshared hbound hports

/-! ## The decision procedure for a finite system -/

/-- A finite presentation of the templates: instance `k`'s declarations as
    a list. -/
structure Finite (S : BehaviorSystem) where
  decls : Nat → List DesignDecl
  eq : ∀ k I, S.instAt k = some I → I.comp.design.Δ = .ofList (decls k)

theorem Finite.produces {S : BehaviorSystem} (F : Finite S) {k : Nat} {I : Inst} (hI : S.instAt k = some I)
    {d : DeclId} {C : SemanticId} (h : Produces I.comp.design.Δ d C) :
    ∃ h' ∈ F.decls k, h'.id = d ∧ C ∈ h'.origins := by
  obtain ⟨h', hd, hc⟩ := h
  rw [F.eq k I hI] at hd
  obtain ⟨hm, hid⟩ := DeclEnv.ofList_some hd
  exact ⟨h', hm, hid, hc⟩

theorem instAt_lt {S : BehaviorSystem} {k : Nat} {I : Inst} (h : S.instAt k = some I) : k < S.insts.length := by
  unfold instAt at h
  exact List.getElem?_eq_some_iff.mp h |>.1

def isPortB (C : BehaviorComponent) (d : DeclId) : Bool :=
  (C.iface.required ++ C.iface.params).any fun p => p.id == d

theorem isPortB_iff (C : BehaviorComponent) (d : DeclId) : isPortB C d = true ↔ IsPort C d := by
  simp only [isPortB, IsPort, List.any_eq_true, beq_iff_eq]

/-- The boundary rule, decided over the finite presentation. -/
def externalSingleProducerB (S : BehaviorSystem) (F : Finite S) : Bool :=
  (List.range S.insts.length).all fun k₁ => (List.range S.insts.length).all fun k₂ =>
    match S.instAt k₁, S.instAt k₂ with
    | some I₁, some I₂ =>
      (F.decls k₁).all fun h₁ => (F.decls k₂).all fun h₂ =>
        h₁.origins.all fun C =>
          I₁.comp.internalSem C || isPortB I₁.comp h₁.id || !(h₂.origins.contains C) ||
          I₂.comp.internalSem C || isPortB I₂.comp h₂.id || (k₁ == k₂ && h₁.id == h₂.id)
    | _, _ => true

theorem ExternalSingleProducer.ofB {S : BehaviorSystem} (F : Finite S) (h : externalSingleProducerB S F = true) :
    ExternalSingleProducer S := by
  intro k₁ I₁ d₁ k₂ I₂ d₂ C hI₁ hI₂ q₁ i₁ np₁ q₂ i₂ np₂
  obtain ⟨h₁, m₁, rfl, c₁⟩ := F.produces hI₁ q₁
  obtain ⟨h₂, m₂, rfl, c₂⟩ := F.produces hI₂ q₂
  have := List.all_eq_true.mp (List.all_eq_true.mp h k₁ (List.mem_range.mpr (instAt_lt hI₁))) k₂
    (List.mem_range.mpr (instAt_lt hI₂))
  simp only [hI₁, hI₂] at this
  have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp this h₁ m₁) h₂ m₂) C c₁
  simp only [Bool.or_eq_true, i₁, i₂, Bool.false_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, Bool.and_eq_true, beq_iff_eq, false_or, or_false] at this
  rcases this with ((p | p) | p) | p
  · exact absurd ((isPortB_iff _ _).mp p) np₁
  · exact absurd c₂ p
  · exact absurd ((isPortB_iff _ _).mp p) np₂
  · exact p

/-- Every originated concept identity below the width, decided. -/
def originsBoundB (S : BehaviorSystem) (F : Finite S) : Bool :=
  (List.range S.insts.length).all fun k => (F.decls k).all fun h => h.origins.all fun C => C.n < S.W

theorem originsBound_ofB {S : BehaviorSystem} (F : Finite S) (h : originsBoundB S F = true) :
    ∀ k I d C, S.instAt k = some I → Produces I.comp.design.Δ d C → C.n < S.W := by
  intro k I d C hI q
  obtain ⟨h', m, -, c⟩ := F.produces hI q
  have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h k (List.mem_range.mpr (instAt_lt hI))) h' m) C c
  simpa using this

/-- Every port bound, decided. -/
def portsBoundB (S : BehaviorSystem) : Bool :=
  (List.range S.insts.length).all fun k =>
    match S.instAt k with
    | some I => (I.comp.iface.required ++ I.comp.iface.params).all fun p =>
        S.bindings.any fun b => b.dstInst == k && b.dst == p.id
    | none => true

theorem PortsBound.ofB {S : BehaviorSystem} (h : portsBoundB S = true) : PortsBound S := by
  intro k I p hI hp
  have := List.all_eq_true.mp h k (List.mem_range.mpr (instAt_lt hI))
  simp only [hI] at this
  have := List.all_eq_true.mp this p hp
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at this
  exact this

/-- Every template producer-unique, decided. -/
def templatesUniqueB (S : BehaviorSystem) (F : Finite S) : Bool :=
  (List.range S.insts.length).all fun k => producerUniqueB (F.decls k)

theorem templatesUnique_ofB {S : BehaviorSystem} (F : Finite S) (h : templatesUniqueB S F = true) :
    ∀ k I, S.instAt k = some I → ProducerUnique I.comp.design.Δ := by
  intro k I hI
  rw [F.eq k I hI]
  exact ProducerUnique.ofList (List.all_eq_true.mp h k (List.mem_range.mpr (instAt_lt hI)))

/-- Bindings relay, decided. -/
def relayB (S : BehaviorSystem) : Bool := S.bindings.all fun b => (S.bindingBody b).originSet.isEmpty

theorem relay_ofB {S : BehaviorSystem} (h : relayB S = true) : ∀ b ∈ S.bindings, (S.bindingBody b).originSet = [] := by
  intro b hb
  have := List.all_eq_true.mp h b hb
  simpa using this

/-- **The checkable form**: one Boolean over the finite presentation
    decides that the flattened design is producer-unique. -/
theorem flatten_producerUnique_ofB {S : BehaviorSystem} (F : Finite S)
    (h : (templatesUniqueB S F && externalSingleProducerB S F && originsBoundB S F && portsBoundB S && relayB S) = true) :
    ProducerUnique S.flattenΔ := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hT, hs⟩, hb⟩, hp⟩, hr⟩ := h
  exact flatten_producerUnique (fun k I hI id h hd => by rw [F.eq k I hI] at hd; exact (DeclEnv.ofList_some hd).2)
    (relay_ofB hr) (templatesUnique_ofB F hT) (ExternalSingleProducer.ofB F hs) (originsBound_ofB F hb)
    (PortsBound.ofB hp)

end BehaviorSystem

end BDL
