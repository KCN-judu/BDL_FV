import BDL.Core.Env

/-!
# Producer — one producer per concept (Phase 20)

A concept `sem C` is a nominal type (Phase 2).  Phase 20 adds the global
invariant that in a design each concept has **at most one producer** — one
declaration that *originates* its values: a realization constructing `C`
(`mk C` anywhere in the body) or an unresolved declaration announcing `C`
in result position (a Source).  A wire (`declRef`), a transport (`sync`), a
memory (`delay`) or a selection of `C` values originates nothing: it relays;
the explicit initial value of a transport or a memory is the relay's
default, not an origin.

The invariant sits beside `SingleDriver` (Phase 6): that one constrains
declarations per output, this one origins per concept; neither implies the
other (Phase 19 `one_origin_two_outputs`).  Typing, evaluation and the
grant are untouched.  What the invariant buys is a *denotation for a
concept*: `producerOf Δ C` is a function, and a surface reference to a
concept elaborates to `declRef` of its producer (`Surface/ConceptRef`).

* `Expr.mkSet` — the concepts a term constructs, as a list
  (`mem_mkSet_iff` with `Expr.constructs`); `Expr.originSet` — the same
  outside initial-value positions.
* `DesignDecl.origins` — the concepts a declaration originates.
* `Produces Δ d C`, `ProducerUnique Δ`, `producerOf ids Δ C`.
* `ProducerUnique.refine` — realizing declarations never adds an origin.
* `ProducerUnique.update_relay` — realizing with a relaying body keeps it.
* `ProducerUnique.ofList` — the decision procedure for finite designs.
-/

namespace BDL

/-- The concepts a term constructs. -/
def Expr.mkSet : Expr → List SemanticId
  | .lam _ b => b.mkSet
  | .app f a => f.mkSet ++ a.mkSet
  | .rep e => e.mkSet
  | .mk s e => s :: e.mkSet
  | .delay i e => i.mkSet ++ e.mkSet
  | .sync _ i e => i.mkSet ++ e.mkSet
  | .fold f z l => f.mkSet ++ z.mkSet ++ l.mkSet
  | _ => []

theorem Expr.mem_mkSet_iff (s : SemanticId) : ∀ e : Expr, s ∈ e.mkSet ↔ e.constructs s
  | .var _ | .boolLit _ | .natLit _ | .declRef _ | .prim _ => by simp [Expr.mkSet, Expr.constructs]
  | .lam _ b => by simp [Expr.mkSet, Expr.constructs, Expr.mem_mkSet_iff s b]
  | .app f a => by simp [Expr.mkSet, Expr.constructs, Expr.mem_mkSet_iff s f, Expr.mem_mkSet_iff s a]
  | .rep e => by simp [Expr.mkSet, Expr.constructs, Expr.mem_mkSet_iff s e]
  | .mk s' e => by simp [Expr.mkSet, Expr.constructs, Expr.mem_mkSet_iff s e, eq_comm]
  | .delay i e => by simp [Expr.mkSet, Expr.constructs, Expr.mem_mkSet_iff s i, Expr.mem_mkSet_iff s e]
  | .sync _ i e => by simp [Expr.mkSet, Expr.constructs, Expr.mem_mkSet_iff s i, Expr.mem_mkSet_iff s e]
  | .fold f z l => by
    simp [Expr.mkSet, Expr.constructs, Expr.mem_mkSet_iff s f, Expr.mem_mkSet_iff s z, Expr.mem_mkSet_iff s l]

instance (s : SemanticId) (e : Expr) : Decidable (e.constructs s) :=
  decidable_of_iff _ (Expr.mem_mkSet_iff s e)

/-- The concepts a term *originates*: what it constructs outside the
    initial-value position of a memory or a transport.  An initial value is
    the relay's default — the value stood in before the first sample — and
    every transported concept value needs one (FVD-0038), so it is not a
    producer of the concept. -/
def Expr.originSet : Expr → List SemanticId
  | .lam _ b => b.originSet
  | .app f a => f.originSet ++ a.originSet
  | .rep e => e.originSet
  | .mk s e => s :: e.originSet
  | .delay _ e => e.originSet
  | .sync _ _ e => e.originSet
  | .fold f z l => f.originSet ++ z.originSet ++ l.originSet
  | _ => []

theorem Expr.constructs_of_mem_originSet (s : SemanticId) : ∀ e : Expr, s ∈ e.originSet → e.constructs s
  | .var _ | .boolLit _ | .natLit _ | .declRef _ | .prim _ => by simp [Expr.originSet]
  | .lam _ b => fun h => Expr.constructs_of_mem_originSet s b h
  | .app f a => fun h => by
    simp only [Expr.originSet, List.mem_append] at h
    exact h.elim (fun h => Or.inl (Expr.constructs_of_mem_originSet s f h))
      (fun h => Or.inr (Expr.constructs_of_mem_originSet s a h))
  | .rep e => fun h => Expr.constructs_of_mem_originSet s e h
  | .mk s' e => fun h => by
    simp only [Expr.originSet, List.mem_cons] at h
    exact h.elim (fun h => Or.inl h.symm) (fun h => Or.inr (Expr.constructs_of_mem_originSet s e h))
  | .delay _ e => fun h => Or.inr (Expr.constructs_of_mem_originSet s e h)
  | .sync _ _ e => fun h => Or.inr (Expr.constructs_of_mem_originSet s e h)
  | .fold f z l => fun h => by
    simp only [Expr.originSet, List.mem_append] at h
    rcases h with (h | h) | h
    · exact Or.inl (Expr.constructs_of_mem_originSet s f h)
    · exact Or.inr (Or.inl (Expr.constructs_of_mem_originSet s z h))
    · exact Or.inr (Or.inr (Expr.constructs_of_mem_originSet s l h))

/-- The concepts a declaration originates: what its body originates, or —
    unresolved — what its signature announces in result position. -/
def DesignDecl.origins (h : DesignDecl) : List SemanticId :=
  match h.realization with
  | some b => b.originSet
  | none => h.interface.expectedType.grant

/-- `d` originates values of `C` in `Δ`. -/
def Produces (Δ : DeclEnv) (d : DeclId) (C : SemanticId) : Prop :=
  ∃ h, Δ d = some h ∧ C ∈ h.origins

/-- `Produces` as a Boolean. -/
def producesB (Δ : DeclEnv) (d : DeclId) (C : SemanticId) : Bool :=
  match Δ d with
  | some h => h.origins.contains C
  | none => false

theorem producesB_iff (Δ : DeclEnv) (d : DeclId) (C : SemanticId) : producesB Δ d C = true ↔ Produces Δ d C := by
  cases hd : Δ d <;> simp [producesB, Produces, hd]

instance (Δ : DeclEnv) (d : DeclId) (C : SemanticId) : Decidable (Produces Δ d C) :=
  decidable_of_iff _ (producesB_iff Δ d C)

/-- **One producer per concept** — global, over origins only.  Relays are
    not producers. -/
def ProducerUnique (Δ : DeclEnv) : Prop :=
  ∀ C d₁ d₂, Produces Δ d₁ C → Produces Δ d₂ C → d₁ = d₂

/-- The producer of `C` among the identities `ids`. -/
def producerOf (ids : List DeclId) (Δ : DeclEnv) (C : SemanticId) : Option DeclId :=
  ids.find? fun d => decide (Produces Δ d C)

theorem producerOf_produces {ids : List DeclId} {Δ : DeclEnv} {C : SemanticId} {d : DeclId}
    (h : producerOf ids Δ C = some d) : Produces Δ d C := by
  have := List.find?_some h
  simpa using this

/-- Under the invariant the producer is *the* producer: whichever origin
    is found is the one there is. -/
theorem producerOf_eq {ids : List DeclId} {Δ : DeclEnv} {C : SemanticId} {d : DeclId}
    (hu : ProducerUnique Δ) (hp : Produces Δ d C) (hd : d ∈ ids) : producerOf ids Δ C = some d := by
  unfold producerOf
  cases hf : ids.find? (fun d => decide (Produces Δ d C)) with
  | none =>
    have := List.find?_eq_none.mp hf d hd
    simp [hp] at this
  | some d' =>
    have hp' : Produces Δ d' C := by simpa using List.find?_some hf
    rw [hu C d' d hp' hp]

/-- The invariant reduces the many-valued relation to a function. -/
theorem produces_iff_producerOf {ids : List DeclId} {Δ : DeclEnv} {C : SemanticId} {d : DeclId}
    (hu : ProducerUnique Δ) (hd : d ∈ ids) : Produces Δ d C ↔ producerOf ids Δ C = some d :=
  ⟨fun hp => producerOf_eq hu hp hd, producerOf_produces⟩

/-! ## Preservation -/

/-- An origin in a refined environment was an origin before: a declaration
    that became realized announced every concept its body may construct
    (`constructs_granted`), and a realized declaration keeps its body. -/
theorem Produces.of_refine {Θ : ConceptEnv} {ev : Evidence} {Δ₁ Δ₂ : DeclEnv} (g₂ : GlobalWF ev Θ Δ₂)
    (er : EnvRefines Δ₁ Δ₂) (dom : ∀ d, Δ₂ d ≠ none → Δ₁ d ≠ none) {d : DeclId} {C : SemanticId}
    (h : Produces Δ₂ d C) : Produces Δ₁ d C := by
  obtain ⟨h₂, hd₂, hp⟩ := h
  cases hd₁ : Δ₁ d with
  | none => exact absurd hd₁ (dom d (by rw [hd₂]; exact fun e => nomatch e))
  | some h₁ =>
    obtain ⟨h₂', hd₂', hle⟩ := er d h₁ hd₁
    rw [hd₂] at hd₂'; cases hd₂'
    have hty : h₁.interface.expectedType = h₂.interface.expectedType := hle.2.1.1
    refine ⟨h₁, hd₁, ?_⟩
    cases hr₁ : h₁.realization with
    | none =>
      simp only [DesignDecl.origins, hr₁, hty]
      cases hr₂ : h₂.realization with
      | none => simpa [DesignDecl.origins, hr₂] using hp
      | some b =>
        simp only [DesignDecl.origins, hr₂] at hp
        exact ((g₂.wellFormed hd₂) b hr₂).1.constructs_granted C (Expr.constructs_of_mem_originSet C b hp)
    | some b₁ =>
      have hb₂ : h₂.realization = some b₁ := hle.2.2 b₁ hr₁
      simpa [DesignDecl.origins, hr₁, hb₂] using hp

/-- **Refinement preserves the invariant**: realizing declarations (same
    domain) never adds an origin.  Adding a second producer is an edit. -/
theorem ProducerUnique.refine {Θ : ConceptEnv} {ev : Evidence} {Δ₁ Δ₂ : DeclEnv} (g₂ : GlobalWF ev Θ Δ₂)
    (er : EnvRefines Δ₁ Δ₂) (dom : ∀ d, Δ₂ d ≠ none → Δ₁ d ≠ none) (hu : ProducerUnique Δ₁) :
    ProducerUnique Δ₂ :=
  fun C d₁ d₂ h₁ h₂ => hu C d₁ d₂ (Produces.of_refine g₂ er dom h₁) (Produces.of_refine g₂ er dom h₂)

/-- The producer does not move under refinement. -/
theorem producerOf_refine {Θ : ConceptEnv} {ev : Evidence} {Δ₁ Δ₂ : DeclEnv} (g₂ : GlobalWF ev Θ Δ₂)
    (er : EnvRefines Δ₁ Δ₂) (dom : ∀ d, Δ₂ d ≠ none → Δ₁ d ≠ none) (hu : ProducerUnique Δ₁)
    {ids : List DeclId} {C : SemanticId} {d : DeclId} (h : producerOf ids Δ₂ C = some d) :
    producerOf ids Δ₁ C = some d :=
  producerOf_eq hu (Produces.of_refine g₂ er dom (producerOf_produces h)) (List.mem_of_find?_eq_some h)

theorem Produces.of_update {Δ : DeclEnv} {h' : DesignDecl} {d : DeclId} {C : SemanticId}
    (hp : Produces (Δ.update h') d C) : (d = h'.id ∧ C ∈ h'.origins) ∨ (d ≠ h'.id ∧ Produces Δ d C) := by
  obtain ⟨h, hd, hc⟩ := hp
  by_cases e : d = h'.id
  · subst e; rw [DeclEnv.update_self] at hd; cases hd; exact Or.inl ⟨rfl, hc⟩
  · rw [DeclEnv.update_other _ _ e] at hd; exact Or.inr ⟨e, h, hd, hc⟩

/-- Realizing a declaration with a body that constructs nothing (a wire, a
    transport, a memory, a selection) keeps the invariant: an origin is
    removed, none is added. -/
theorem ProducerUnique.update_relay {Δ : DeclEnv} (hu : ProducerUnique Δ) {h' : DesignDecl}
    (hrel : h'.origins = []) : ProducerUnique (Δ.update h') := by
  intro C d₁ d₂ h₁ h₂
  rcases h₁.of_update with ⟨_, hc⟩ | ⟨_, p₁⟩
  · simp [hrel] at hc
  rcases h₂.of_update with ⟨_, hc⟩ | ⟨_, p₂⟩
  · simp [hrel] at hc
  exact hu C d₁ d₂ p₁ p₂

/-! ## The decision procedure for finite designs -/

def producerUniqueB (l : List DesignDecl) : Bool :=
  l.all fun h₁ => l.all fun h₂ => h₁.id == h₂.id || h₁.origins.all fun C => !(h₂.origins.contains C)

theorem ProducerUnique.ofList {l : List DesignDecl} (h : producerUniqueB l = true) : ProducerUnique (.ofList l) := by
  intro C d₁ d₂ ⟨h₁, hd₁, hc₁⟩ ⟨h₂, hd₂, hc₂⟩
  obtain ⟨m₁, i₁⟩ := DeclEnv.ofList_some hd₁
  obtain ⟨m₂, i₂⟩ := DeclEnv.ofList_some hd₂
  have := List.all_eq_true.mp (List.all_eq_true.mp h h₁ m₁) h₂ m₂
  simp only [Bool.or_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at this
  rcases this with e | hall
  · exact i₁ ▸ i₂ ▸ e
  · exact absurd hc₂ (hall C hc₁)

end BDL
