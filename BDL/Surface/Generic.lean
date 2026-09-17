import BDL.Surface.Stdlib

/-!
# Generic — nominality and dimensions survive generic instantiation (Phase 9b)

A generic definition is a family of monomorphic terms.  Instantiating it at
`sem Brightness` yields a term whose type mentions `sem Brightness` exactly
where the type variable stood; typing then forbids an `Opacity` argument
just as it forbids it for any monomorphic term, because `sem s` and
`sem s'` are distinct types (Phase 2).  Nothing about the family — not
pairs, not lists, not `eq`/`lt`, not `map`/`fold` — can identify two
concepts with the same representation.

Also here: structural equality on closure-free values is real equality,
so `x ∈ {c₁, …, cₙ}` elaborated as `contains x [c₁, …, cₙ]` means list
membership (§12 of the brief).
-/

namespace BDL.Reactive
open BDL

/-! ## Structural equality is equality on closure-free values -/

mutual
theorem Value.eq_of_beq : ∀ {v w : Value}, Value.beq v w = true → v = w
  | .bool a, .bool b, h => by simp [Value.beq] at h; rw [h]
  | .nat a, .nat b, h => by simp [Value.beq] at h; rw [h]
  | .sem s v, .sem s' w, h => by
    simp only [Value.beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, Value.eq_of_beq h.2]
  | .none, .none, _ => rfl
  | .some v, .some w, h => by rw [Value.eq_of_beq (v := v) (w := w) h]
  | .pair a b, .pair c d, h => by
    simp only [Value.beq, Bool.and_eq_true] at h
    rw [Value.eq_of_beq h.1, Value.eq_of_beq h.2]
  | .list vs, .list ws, h => by rw [Value.eqList_of_beqList h]
  | .bool _, .nat _, h | .bool _, .sem _ _, h | .bool _, .none, h | .bool _, .some _, h | .bool _, .clo _ _, h
  | .bool _, .prim _ _, h | .bool _, .list _, h | .bool _, .pair _ _, h => by simp [Value.beq] at h
  | .nat _, .bool _, h | .nat _, .sem _ _, h | .nat _, .none, h | .nat _, .some _, h | .nat _, .clo _ _, h
  | .nat _, .prim _ _, h | .nat _, .list _, h | .nat _, .pair _ _, h => by simp [Value.beq] at h
  | .sem _ _, .bool _, h | .sem _ _, .nat _, h | .sem _ _, .none, h | .sem _ _, .some _, h | .sem _ _, .clo _ _, h
  | .sem _ _, .prim _ _, h | .sem _ _, .list _, h | .sem _ _, .pair _ _, h => by simp [Value.beq] at h
  | .none, .bool _, h | .none, .nat _, h | .none, .sem _ _, h | .none, .some _, h | .none, .clo _ _, h
  | .none, .prim _ _, h | .none, .list _, h | .none, .pair _ _, h => by simp [Value.beq] at h
  | .some _, .bool _, h | .some _, .nat _, h | .some _, .sem _ _, h | .some _, .none, h | .some _, .clo _ _, h
  | .some _, .prim _ _, h | .some _, .list _, h | .some _, .pair _ _, h => by simp [Value.beq] at h
  | .clo _ _, _, h => by simp [Value.beq] at h
  | .prim _ _, _, h => by simp [Value.beq] at h
  | .list _, .bool _, h | .list _, .nat _, h | .list _, .sem _ _, h | .list _, .none, h | .list _, .some _, h
  | .list _, .clo _ _, h | .list _, .prim _ _, h | .list _, .pair _ _, h => by simp [Value.beq] at h
  | .pair _ _, .bool _, h | .pair _ _, .nat _, h | .pair _ _, .sem _ _, h | .pair _ _, .none, h | .pair _ _, .some _, h
  | .pair _ _, .clo _ _, h | .pair _ _, .prim _ _, h | .pair _ _, .list _, h => by simp [Value.beq] at h
theorem Value.eqList_of_beqList : ∀ {vs ws : List Value}, Value.beqList vs ws = true → vs = ws
  | [], [], _ => rfl
  | v :: vs, w :: ws, h => by
    simp only [Value.beqList, Bool.and_eq_true] at h
    rw [Value.eq_of_beq h.1, Value.eqList_of_beqList h.2]
  | [], _ :: _, h => by simp [Value.beqList] at h
  | _ :: _, [], h => by simp [Value.beqList] at h
end

/-- A first-order value: no closure and no partially applied operator. -/
inductive Value.IsData : Value → Prop where
  | bool (b : Bool) : Value.IsData (.bool b)
  | nat (n : Nat) : Value.IsData (.nat n)
  | sem {s : SemanticId} {v : Value} : Value.IsData v → Value.IsData (.sem s v)
  | none : Value.IsData .none
  | some {v : Value} : Value.IsData v → Value.IsData (.some v)
  | list {vs : List Value} : (∀ w ∈ vs, Value.IsData w) → Value.IsData (.list vs)
  | pair {a b : Value} : Value.IsData a → Value.IsData b → Value.IsData (.pair a b)

theorem Value.IsData.noClo : ∀ {v : Value}, v.IsData → v.NoClo
  | _, .bool _ => fun hc => nomatch hc
  | _, .nat _ => fun hc => nomatch hc
  | _, .sem hv => fun hc => by cases hc with | semInner hc' => exact Value.IsData.noClo hv hc'
  | _, .none => fun hc => nomatch hc
  | _, .some hv => fun hc => by cases hc with | someInner hc' => exact Value.IsData.noClo hv hc'
  | _, .list hvs => fun hc => by cases hc with | listElem hm hc' => exact Value.IsData.noClo (hvs _ hm) hc'
  | _, .pair ha hb => fun hc => by
    cases hc with
    | pairFst hc' => exact Value.IsData.noClo ha hc'
    | pairSnd hc' => exact Value.IsData.noClo hb hc'

mutual
theorem Value.beq_self : ∀ {v : Value}, v.IsData → Value.beq v v = true
  | _, .bool b => by simp only [Value.beq]; exact decide_eq_true rfl
  | _, .nat n => by simp only [Value.beq]; exact decide_eq_true rfl
  | _, .sem hv => by simp only [Value.beq, Value.beq_self hv, Bool.and_true]; exact decide_eq_true rfl
  | _, .none => rfl
  | _, .some hv => by simp [Value.beq, Value.beq_self hv]
  | _, .pair ha hb => by simp [Value.beq, Value.beq_self ha, Value.beq_self hb]
  | _, .list hvs => Value.beqList_self hvs
theorem Value.beqList_self : ∀ {vs : List Value}, (∀ w ∈ vs, w.IsData) → Value.beqList vs vs = true
  | [], _ => rfl
  | v :: vs, h => by
    simp only [Value.beqList, Bool.and_eq_true]
    exact ⟨Value.beq_self (h v List.mem_cons_self), Value.beqList_self fun w hw => h w (List.mem_cons_of_mem _ hw)⟩
end

/-- **`beq_iff`**: on first-order values structural equality is equality. -/
theorem Value.beq_iff {v w : Value} (hv : v.IsData) : Value.beq v w = true ↔ v = w :=
  ⟨Value.eq_of_beq, fun h => h ▸ Value.beq_self hv⟩

end BDL.Reactive

namespace BDL.Generic
open BDL BDL.Reactive BDL.Stdlib

section Nominal
variable {Θ : ConceptEnv} {Δ : DeclEnv} {G : Grant} [DecidablePred G] {Γ : Ctx}

/-- **`generic_instantiation_preserves_identity`.**  Any family `g` typed at
    the scheme `α → α → α`, instantiated at concept `s`, rejects an argument
    of a different concept `s'` — whatever the representations of `s` and
    `s'` are (they are not even consulted). -/
theorem generic_preserves_identity (g : Ty → Expr)
    (hg : ∀ τ, HasType Θ Δ G Γ (g τ) (.arr τ (.arr τ τ)))
    {s s' : SemanticId} (hne : s ≠ s') {x y : Expr}
    (hx : HasType Θ Δ G Γ x (.sem s)) (hy : HasType Θ Δ G Γ y (.sem s')) :
    ¬ ∃ τ, HasType Θ Δ G Γ (app2 (g (.sem s)) x y) τ := by
  rintro ⟨τ, h⟩
  cases h with
  | app hf ha =>
    cases hf with
    | app hg' hx' =>
      have e := (hg (.sem s)).unique hg'
      simp only [Ty.arr.injEq] at e
      obtain ⟨_, hdom, _⟩ := e
      exact hne (Ty.sem.inj (hdom.trans (hy.unique ha).symm))

/-- The same for quantities: `min` at `q Length` rejects a `q Time`. -/
theorem generic_preserves_dimension (g : Ty → Expr)
    (hg : ∀ τ, HasType Θ Δ G Γ (g τ) (.arr τ (.arr τ τ)))
    {d d' : Dim} (hne : d ≠ d') {x y : Expr}
    (hx : HasType Θ Δ G Γ x (.q d)) (hy : HasType Θ Δ G Γ y (.q d')) :
    ¬ ∃ τ, HasType Θ Δ G Γ (app2 (g (.q d)) x y) τ := by
  rintro ⟨τ, h⟩
  cases h with
  | app hf ha =>
    cases hf with
    | app hg' hx' =>
      have e := (hg (.q d)).unique hg'
      simp only [Ty.arr.injEq] at e
      obtain ⟨_, hdom, _⟩ := e
      exact hne (Ty.q.inj (hdom.trans (hy.unique ha).symm))

/-- Through pairs: a pair of two concepts projects to each concept, never to
    the other (typing of `fst`/`snd` is positional). -/
theorem pair_projections_keep_concepts {s s' : SemanticId} {p : Expr}
    (hp : HasType Θ Δ G Γ p (.prod (.sem s) (.sem s'))) :
    HasType Θ Δ G Γ (fstE (.sem s) (.sem s') p) (.sem s) ∧ HasType Θ Δ G Γ (sndE (.sem s) (.sem s') p) (.sem s') ∧
    (s ≠ s' → ¬ HasType Θ Δ G Γ (fstE (.sem s) (.sem s') p) (.sem s')) :=
  ⟨.app .prim hp, .app .prim hp, fun hne h => hne (Ty.sem.inj ((HasType.app .prim hp).unique h))⟩

/-- Through lists and `map`: `map f` at `sem s → sem s'` yields `list (sem s')`
    and cannot be typed at `list (sem s)`. -/
theorem map_keeps_concepts {s s' : SemanticId} (hne : s ≠ s') {f xs : Expr}
    (hf : HasType Θ Δ G Γ f (.arr (.sem s) (.sem s'))) (hxs : HasType Θ Δ G Γ xs (.list (.sem s))) :
    HasType Θ Δ G Γ (app2 (mapF (.sem s) (.sem s')) f xs) (.list (.sem s')) ∧
    ¬ HasType Θ Δ G Γ (app2 (mapF (.sem s) (.sem s')) f xs) (.list (.sem s)) := by
  have h : HasType Θ Δ G Γ (app2 (mapF (.sem s) (.sem s')) f xs) (.list (.sem s')) :=
    .app (.app (mapF_typed _ _) hf) hxs
  exact ⟨h, fun h' => hne (Ty.sem.inj (Ty.list.inj (h'.unique h)))⟩

/-- Through `eq`: equality is typed at one concept; the two concepts cannot
    be compared even though both may be represented by the same `q Dim.zero`. -/
theorem eq_across_concepts_rejected {s s' : SemanticId} (hne : s ≠ s') {x y : Expr}
    (hx : HasType Θ Δ G Γ x (.sem s)) (hy : HasType Θ Δ G Γ y (.sem s')) :
    ¬ ∃ τ, HasType Θ Δ G Γ (eqE (.sem s) trivial x y) τ := by
  rintro ⟨τ, h⟩
  cases h with
  | app hf ha =>
    cases hf with
    | app hp _ =>
      cases hp
      have := hy.unique ha
      simp only [Ty.sem.injEq] at this
      exact hne this.symm

end Nominal

/-- **`oneOf_mem`**: `x ∈ {c₁, …, cₙ}`, elaborated as `contains x [c₁, …, cₙ]`,
    evaluates to `true` iff the value of `x` is a member of the values of
    the literal — a list with duplicates gives the same answer, so no
    uniqueness convention and no `Set` type is needed for membership. -/
theorem oneOf_mem {Δ : DeclEnv} {I : Input} {t : Nat} {ρ : List Value} (τ : Ty) (h : τ.Data) {x : Expr}
    {cs : List Expr} {vx : Value} {vs : List Value} (hx : Ev Δ I t ρ x vx) (hvx : vx.IsData)
    (hcs : ∀ i (h : i < cs.length) (h' : i < vs.length), Ev Δ I t ρ cs[i] vs[i]) (hl : cs.length = vs.length) :
    Ev Δ I t ρ (oneOfE τ h x cs) (.bool true) ↔ vx ∈ vs := by
  have hspec := contains_spec τ h hx (ev_listLit τ hcs hl)
  constructor
  · intro he
    have := hspec.det he
    simp only [Value.bool.injEq, List.any_eq_true] at this
    obtain ⟨w, hw, hb⟩ := this
    exact (Value.eq_of_beq hb) ▸ hw
  · intro hm
    have : vs.any (Value.beq vx) = true := List.any_eq_true.mpr ⟨vx, hm, Value.beq_self hvx⟩
    rwa [this] at hspec

/-- Duplicates do not change membership: the list-with-uniqueness convention
    is unnecessary for `oneOf`. -/
theorem oneOf_dup_irrelevant (vx c : Value) (vs : List Value) :
    ((c :: c :: vs).any (Value.beq vx)) = ((c :: vs).any (Value.beq vx)) := by
  simp [List.any_cons]

end BDL.Generic
