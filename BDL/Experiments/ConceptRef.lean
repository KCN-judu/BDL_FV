import BDL.Validation.Producer
import BDL.Core.Clock

/-!
# Concept references (Phase 20; an experiment since Phase 21)

Phase 21 (FVD-0163) draws every edge to a Sem block — a declaration — so a
reference is `declRef` and no concept reference is needed; this module
remains as the elaboration a design with one Sem block per concept may use.

Under `ProducerUnique` a concept has a denotation: *the* value of `C` at a
tick is the value of its one producer.  The surface may therefore let a
formula — and the canvas an edge — name a **concept** where the kernel
names a declaration: a concept reference `cref C` elaborates to
`declRef (producerOf C)`.  The kernel is untouched; the elaboration is a
projection through `producerOf`, and it is stable under refinement.

* `SExpr` — `Expr` plus `cref`.
* `elabS ids Δ` — the elaboration; `elabS_cref`, `elabS_embed`, `elabS_none`.
* `elabS_refine` — a concept reference does not move while the design is
  realized; `elabS_congr` — it depends on the design only through
  `producerOf`.
* `ValueOf`, `valueOf_det` — the value of a concept at a tick, and its
  determinism, from `MEv.det`.
-/

namespace BDL.ConceptRef

/-- Surface terms: the kernel's forms and a reference to a concept. -/
inductive SExpr where
  | var (i : Nat)
  | boolLit (b : Bool)
  | natLit (n : Nat)
  | lam (dom : Ty) (body : SExpr)
  | app (f a : SExpr)
  | declRef (d : DeclId)
  /-- A reference to *the* value of concept `C`. -/
  | cref (C : SemanticId)
  | rep (e : SExpr)
  | mk (s : SemanticId) (e : SExpr)
  | prim (p : Prim)
  | delay (init e : SExpr)
  | sync (src : ClockId) (init e : SExpr)
  | fold (f z l : SExpr)

/-- The elaboration: every concept reference becomes a reference to the
    concept's producer among `ids`; a concept without a producer leaves the
    term open (`none`). -/
def elabS (ids : List DeclId) (Δ : DeclEnv) : SExpr → Option Expr
  | .var i => some (.var i)
  | .boolLit b => some (.boolLit b)
  | .natLit n => some (.natLit n)
  | .lam dom b => (elabS ids Δ b).map (.lam dom)
  | .app f a => do return .app (← elabS ids Δ f) (← elabS ids Δ a)
  | .declRef d => some (.declRef d)
  | .cref C => (producerOf ids Δ C).map .declRef
  | .rep e => (elabS ids Δ e).map .rep
  | .mk s e => (elabS ids Δ e).map (.mk s)
  | .prim p => some (.prim p)
  | .delay i e => do return .delay (← elabS ids Δ i) (← elabS ids Δ e)
  | .sync c i e => do return .sync c (← elabS ids Δ i) (← elabS ids Δ e)
  | .fold f z l => do return .fold (← elabS ids Δ f) (← elabS ids Δ z) (← elabS ids Δ l)

/-- A kernel term as a surface term. -/
def embed : Expr → SExpr
  | .var i => .var i
  | .boolLit b => .boolLit b
  | .natLit n => .natLit n
  | .lam dom b => .lam dom (embed b)
  | .app f a => .app (embed f) (embed a)
  | .declRef d => .declRef d
  | .rep e => .rep (embed e)
  | .mk s e => .mk s (embed e)
  | .prim p => .prim p
  | .delay i e => .delay (embed i) (embed e)
  | .sync c i e => .sync c (embed i) (embed e)
  | .fold f z l => .fold (embed f) (embed z) (embed l)

/-- Kernel terms elaborate to themselves: the surface is conservative. -/
theorem elabS_embed (ids : List DeclId) (Δ : DeclEnv) : ∀ e : Expr, elabS ids Δ (embed e) = some e
  | .var _ | .boolLit _ | .natLit _ | .declRef _ | .prim _ => rfl
  | .lam dom b => by simp [embed, elabS, elabS_embed ids Δ b]
  | .app f a => by simp [embed, elabS, elabS_embed ids Δ f, elabS_embed ids Δ a]
  | .rep e => by simp [embed, elabS, elabS_embed ids Δ e]
  | .mk s e => by simp [embed, elabS, elabS_embed ids Δ e]
  | .delay i e => by simp [embed, elabS, elabS_embed ids Δ i, elabS_embed ids Δ e]
  | .sync c i e => by simp [embed, elabS, elabS_embed ids Δ i, elabS_embed ids Δ e]
  | .fold f z l => by simp [embed, elabS, elabS_embed ids Δ f, elabS_embed ids Δ z, elabS_embed ids Δ l]

/-- **Reading a concept is reading its producer.** -/
theorem elabS_cref {ids : List DeclId} {Δ : DeclEnv} {C : SemanticId} {d : DeclId}
    (hu : ProducerUnique Δ) (hp : Produces Δ d C) (hd : d ∈ ids) :
    elabS ids Δ (.cref C) = some (.declRef d) := by
  simp [elabS, producerOf_eq hu hp hd]

/-- A concept nobody produces yet has no value to read: the term stays open. -/
theorem elabS_cref_none {ids : List DeclId} {Δ : DeclEnv} {C : SemanticId}
    (h : ∀ d ∈ ids, ¬ Produces Δ d C) : elabS ids Δ (.cref C) = none := by
  simp only [elabS, producerOf, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq]
  exact h

/-- The elaboration depends on the design only through `producerOf`. -/
theorem elabS_congr {ids : List DeclId} {Δ₁ Δ₂ : DeclEnv}
    (h : ∀ C, producerOf ids Δ₁ C = producerOf ids Δ₂ C) : ∀ s, elabS ids Δ₁ s = elabS ids Δ₂ s
  | .var _ | .boolLit _ | .natLit _ | .declRef _ | .prim _ => rfl
  | .cref C => by simp [elabS, h C]
  | .lam dom b => by simp [elabS, elabS_congr h b]
  | .app f a => by simp [elabS, elabS_congr h f, elabS_congr h a]
  | .rep e => by simp [elabS, elabS_congr h e]
  | .mk s e => by simp [elabS, elabS_congr h e]
  | .delay i e => by simp [elabS, elabS_congr h i, elabS_congr h e]
  | .sync c i e => by simp [elabS, elabS_congr h i, elabS_congr h e]
  | .fold f z l => by simp [elabS, elabS_congr h f, elabS_congr h z, elabS_congr h l]

/-- **A concept reference does not move under refinement**: whatever the
    refined design elaborates a surface term to, the design before the
    refinement elaborated it to the same kernel term.  (The converse needs
    only that the producer is not lost, which realizing never does — an
    unresolved producer stays one, a realized one keeps its body.) -/
theorem elabS_refine {Θ : ConceptEnv} {ev : Evidence} {Δ₁ Δ₂ : DeclEnv} (g₂ : GlobalWF ev Θ Δ₂)
    (er : EnvRefines Δ₁ Δ₂) (dom : ∀ d, Δ₂ d ≠ none → Δ₁ d ≠ none) (hu : ProducerUnique Δ₁)
    {ids : List DeclId} : ∀ {s : SExpr} {e : Expr}, elabS ids Δ₂ s = some e → elabS ids Δ₁ s = some e
  | .var _, _, h | .boolLit _, _, h | .natLit _, _, h | .declRef _, _, h | .prim _, _, h => h
  | .cref C, e, h => by
    simp only [elabS, Option.map_eq_some_iff] at h ⊢
    obtain ⟨d, hd, rfl⟩ := h
    exact ⟨d, producerOf_refine g₂ er dom hu hd, rfl⟩
  | .lam dom' b, e, h => by
    simp only [elabS, Option.map_eq_some_iff] at h ⊢
    obtain ⟨b', hb, rfl⟩ := h
    exact ⟨b', elabS_refine g₂ er dom hu hb, rfl⟩
  | .app f a, e, h => by
    simp only [elabS, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h ⊢
    obtain ⟨f', hf, a', ha, rfl⟩ := h
    exact ⟨f', elabS_refine g₂ er dom hu hf, a', elabS_refine g₂ er dom hu ha, rfl⟩
  | .rep e₀, e, h => by
    simp only [elabS, Option.map_eq_some_iff] at h ⊢
    obtain ⟨e', he, rfl⟩ := h
    exact ⟨e', elabS_refine g₂ er dom hu he, rfl⟩
  | .mk s e₀, e, h => by
    simp only [elabS, Option.map_eq_some_iff] at h ⊢
    obtain ⟨e', he, rfl⟩ := h
    exact ⟨e', elabS_refine g₂ er dom hu he, rfl⟩
  | .delay i e₀, e, h => by
    simp only [elabS, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h ⊢
    obtain ⟨i', hi, e', he, rfl⟩ := h
    exact ⟨i', elabS_refine g₂ er dom hu hi, e', elabS_refine g₂ er dom hu he, rfl⟩
  | .sync c i e₀, e, h => by
    simp only [elabS, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h ⊢
    obtain ⟨i', hi, e', he, rfl⟩ := h
    exact ⟨i', elabS_refine g₂ er dom hu hi, e', elabS_refine g₂ er dom hu he, rfl⟩
  | .fold f z l, e, h => by
    simp only [elabS, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h ⊢
    obtain ⟨f', hf, z', hz, l', hl, rfl⟩ := h
    exact ⟨f', elabS_refine g₂ er dom hu hf, z', elabS_refine g₂ er dom hu hz, l', elabS_refine g₂ er dom hu hl, rfl⟩

/-! ## The value of a concept -/

open BDL.Clock in
/-- *The* value of concept `C` in domain `c` at tick `t`: the value of its
    producer.  Meaningful under `ProducerUnique`; see `valueOf_det`. -/
def ValueOf (ids : List DeclId) (S : Sched) (Δ : DeclEnv) (I : Reactive.Input) (c : ClockId) (t : Nat)
    (C : SemanticId) (v : Reactive.Value) : Prop :=
  ∃ d, producerOf ids Δ C = some d ∧ MEv S Δ I c t [] (.declRef d) v

open BDL.Clock in
/-- A concept has at most one value at a tick. -/
theorem valueOf_det {ids : List DeclId} {S : Sched} {Δ : DeclEnv} {I : Reactive.Input} {c : ClockId} {t : Nat}
    {C : SemanticId} {v₁ v₂ : Reactive.Value} (h₁ : ValueOf ids S Δ I c t C v₁) (h₂ : ValueOf ids S Δ I c t C v₂) :
    v₁ = v₂ := by
  obtain ⟨d₁, hd₁, e₁⟩ := h₁
  obtain ⟨d₂, hd₂, e₂⟩ := h₂
  rw [hd₁] at hd₂; cases hd₂
  exact MEv.det e₁ e₂

open BDL.Clock in
/-- Under the invariant the value of a concept is the value of any of its
    producers — there is one. -/
theorem valueOf_of_produces {ids : List DeclId} {S : Sched} {Δ : DeclEnv} {I : Reactive.Input} {c : ClockId} {t : Nat}
    {C : SemanticId} {d : DeclId} {v : Reactive.Value} (hu : ProducerUnique Δ) (hp : Produces Δ d C) (hd : d ∈ ids)
    (e : MEv S Δ I c t [] (.declRef d) v) : ValueOf ids S Δ I c t C v :=
  ⟨d, producerOf_eq hu hp hd, e⟩

end BDL.ConceptRef
