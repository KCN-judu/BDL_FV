import BDL.Surface.Poly
import BDL.Behavior.Rename

/-!
# Stdlib — the definitional equation library (Phase 9b)

Every designer-facing equation helper is a *closed kernel term*, indexed by
the types (and dimensions) it is used at: a rank-1 generic definition is a
family of monomorphic terms, instantiated by matching (`Poly.lean`).  The
kernel never sees a type variable.

Capabilities (Phase 9c): `eq` needs `Data` — the kernel's one proof
field; ordering is a *surface* capability `Ordered` — a quantity, or a
concept the designer declared ordered, compared through its representation
(`ltAt`).  No structural order exists on pairs, lists, options, booleans or
undeclared concepts: `min`, `max`, `clamp`, `inRange` take `Ordered`
evidence; `contains`, `oneOf` take the `Data` proof; `map`, `fold`, `any`,
`all`, `filter` need neither.

Three things are proved once, for the whole library (§21 of the brief):

* **typing at every instance** (`*_typed`): each entry has its scheme's
  type in every environment;
* **context-free evaluation** (`lib_eval_context_free`): a library term
  reads no declaration and no earlier tick, so its value is the same in
  every design, at every tick, under every input (`Ev.pure`);
* **no hidden privilege** (`lib_no_construction`, `lib_clocked`): a library
  term constructs no Sem value and is clocked in every domain.

And the collection operations are proved to compute the intended
mathematical functions (`any_spec`, `all_spec`, `contains_spec`,
`map_spec`, `min_spec`, …), so finite quantification over a list *is*
`List.any`/`List.all` (`forall_in_list`, `exists_in_list`).
-/

namespace BDL.Stdlib
open BDL BDL.Reactive BDL.Clock

/-! ## Builders -/

def app2 (f a b : Expr) : Expr := .app (.app f a) b
def app3 (f a b c : Expr) : Expr := .app (.app (.app f a) b) c

def iteE (τ : Ty) (c a b : Expr) : Expr := app3 (.prim (.ite τ)) c a b
def ltE (d : Dim) (a b : Expr) : Expr := app2 (.prim (.lt d)) a b
def eqE (τ : Ty) (h : τ.Data) (a b : Expr) : Expr := app2 (.prim (.eq τ h)) a b
def orE (a b : Expr) : Expr := app2 (.prim .or) a b
def andE (a b : Expr) : Expr := app2 (.prim .and) a b
def notE (a : Expr) : Expr := .app (.prim .not) a
def consE (τ : Ty) (x l : Expr) : Expr := app2 (.prim (.cons τ)) x l
def nilE (τ : Ty) : Expr := .prim (.nil τ)
def pairE (a b : Ty) (x y : Expr) : Expr := app2 (.prim (.pair a b)) x y
def fstE (a b : Ty) (p : Expr) : Expr := .app (.prim (.fst a b)) p
def sndE (a b : Ty) (p : Expr) : Expr := .app (.prim (.snd a b)) p
def someE (τ : Ty) (x : Expr) : Expr := .app (.prim (.some τ)) x
def noneE (τ : Ty) : Expr := .prim (.none τ)
def toListE (τ : Ty) (o : Expr) : Expr := .app (.prim (.toList τ)) o
def takeE (τ : Ty) (k l : Expr) : Expr := app2 (.prim (.take τ)) k l
def dropE (τ : Ty) (k l : Expr) : Expr := app2 (.prim (.drop τ)) k l
def revE (τ : Ty) (l : Expr) : Expr := .app (.prim (.reverse τ)) l
def litE (d : Dim) (n : Nat) : Expr := .prim (.lit d n)

/-- A list literal `[e₁, …, eₙ]`. -/
def listLit (τ : Ty) : List Expr → Expr
  | [] => nilE τ
  | e :: es => consE τ e (listLit τ es)

/-! ## The library, as closed combinators (de Bruijn) -/

/-- `id : α → α` -/
def idF (τ : Ty) : Expr := .lam τ (.var 0)
/-- `const : α → β → α` -/
def constF (τ σ : Ty) : Expr := .lam τ (.lam σ (.var 1))
/-- `swap : α × β → β × α` -/
def swapF (a b : Ty) : Expr := .lam (.prod a b) (pairE b a (sndE a b (.var 0)) (fstE a b (.var 0)))
/-! ### The `Ordered` capability (Phase 9c)

Evidence that a type has a designer-meaningful order: a quantity, or a
concept declared *ordered* whose representation is a quantity of
dimension `d`.  Nothing else: pairs, lists, options, booleans and
undeclared concepts have no order — their only comparison is equality. -/
inductive Ordered : Ty → Type where
  | q (d : Dim) : Ordered (.q d)
  | sem (s : ConceptId) (d : Dim) : Ordered (.sem s)

/-- `a < b` at an ordered type: directly on quantities, through the
    representation on an ordered concept.  The concept's identity is never
    lost: `min`/`max`/`clamp` return one of their arguments. -/
def ltAt : {τ : Ty} → Ordered τ → Expr → Expr → Expr
  | _, .q d, a, b => ltE d a b
  | _, .sem _ d, a, b => ltE d (.rep a) (.rep b)

/-- `min : α → α → α` for ordered `α` -/
def minF {τ : Ty} (o : Ordered τ) : Expr :=
  .lam τ (.lam τ (iteE τ (ltAt o (.var 1) (.var 0)) (.var 1) (.var 0)))
/-- `max : α → α → α` for ordered `α` -/
def maxF {τ : Ty} (o : Ordered τ) : Expr :=
  .lam τ (.lam τ (iteE τ (ltAt o (.var 1) (.var 0)) (.var 0) (.var 1)))
/-- `clamp x lo hi = max lo (min x hi)` -/
def clampF {τ : Ty} (o : Ordered τ) : Expr :=
  .lam τ (.lam τ (.lam τ (app2 (maxF o) (.var 1) (app2 (minF o) (.var 2) (.var 0)))))
/-- `inRange x lo hi = lo ≤ x ∧ x ≤ hi` -/
def inRangeF {τ : Ty} (o : Ordered τ) : Expr :=
  .lam τ (.lam τ (.lam τ (andE (notE (ltAt o (.var 2) (.var 1))) (notE (ltAt o (.var 0) (.var 2))))))
/-- An interval is a pair; membership is a function of the pair. -/
def inIntervalF {τ : Ty} (o : Ordered τ) : Expr :=
  .lam (.prod τ τ) (.lam τ (app3 (inRangeF o) (.var 0) (fstE τ τ (.var 1)) (sndE τ τ (.var 1))))
/-- `minBy : (α → α → bool) → α → α → α` — the comparator escape hatch: a
    designer-defined order without any class. -/
def minByF (τ : Ty) : Expr :=
  .lam (.arr τ (.arr τ .bool)) (.lam τ (.lam τ (iteE τ (app2 (.var 2) (.var 1) (.var 0)) (.var 1) (.var 0))))
def maxByF (τ : Ty) : Expr :=
  .lam (.arr τ (.arr τ .bool)) (.lam τ (.lam τ (iteE τ (app2 (.var 2) (.var 1) (.var 0)) (.var 0) (.var 1))))
/-- `foldr : (α → β → β) → β → list α → β` — the recursor as a function -/
def foldrF (τ σ : Ty) : Expr :=
  .lam (.arr τ (.arr σ σ)) (.lam σ (.lam (.list τ) (.fold (.var 2) (.var 1) (.var 0))))
/-- `any : (α → bool) → list α → bool` -/
def anyF (τ : Ty) : Expr :=
  .lam (.arr τ .bool) (.lam (.list τ)
    (.fold (.lam τ (.lam .bool (orE (.app (.var 3) (.var 1)) (.var 0)))) (.boolLit false) (.var 0)))
/-- `all : (α → bool) → list α → bool` -/
def allF (τ : Ty) : Expr :=
  .lam (.arr τ .bool) (.lam (.list τ)
    (.fold (.lam τ (.lam .bool (andE (.app (.var 3) (.var 1)) (.var 0)))) (.boolLit true) (.var 0)))
/-- `contains : α → list α → bool` for data `α` -/
def containsF (τ : Ty) (h : τ.Data) : Expr :=
  .lam τ (.lam (.list τ)
    (.fold (.lam τ (.lam .bool (orE (eqE τ h (.var 3) (.var 1)) (.var 0)))) (.boolLit false) (.var 0)))
/-- `map : (α → β) → list α → list β` -/
def mapF (τ σ : Ty) : Expr :=
  .lam (.arr τ σ) (.lam (.list τ)
    (.fold (.lam τ (.lam (.list σ) (consE σ (.app (.var 3) (.var 1)) (.var 0)))) (nilE σ) (.var 0)))
/-- `filter : (α → bool) → list α → list α` -/
def filterF (τ : Ty) : Expr :=
  .lam (.arr τ .bool) (.lam (.list τ)
    (.fold (.lam τ (.lam (.list τ) (iteE (.list τ) (.app (.var 3) (.var 1)) (consE τ (.var 1) (.var 0)) (.var 0))))
      (nilE τ) (.var 0)))
/-- `append : list α → list α → list α` -/
def appendF (τ : Ty) : Expr := .lam (.list τ) (.lam (.list τ) (.fold (.prim (.cons τ)) (.var 0) (.var 1)))
/-- `sum : list (q d) → q d` — dimension-generic by the family index -/
def sumF (d : Dim) : Expr := .lam (.list (.q d)) (.fold (.prim (.add d)) (litE d 0) (.var 0))
/-- `optElim : β → (α → β) → opt α → β` — options are lists of length ≤ 1 -/
def optElimF (τ σ : Ty) : Expr :=
  .lam σ (.lam (.arr τ σ) (.lam (.opt τ)
    (.fold (.lam τ (.lam σ (.app (.var 3) (.var 1)))) (.var 2) (toListE τ (.var 0)))))
/-- `mapOpt : (α → β) → opt α → opt β` -/
def mapOptF (τ σ : Ty) : Expr :=
  .lam (.arr τ σ) (.lam (.opt τ)
    (.fold (.lam τ (.lam (.opt σ) (someE σ (.app (.var 3) (.var 1))))) (noneE σ) (toListE τ (.var 0))))
/-- `getOrElse : opt α → α → α` is the registered `getD`. -/
def getOrElseF (τ : Ty) : Expr := .prim (.getD τ)
/-- `zip : list α → list β → list (α × β)` — a fold over `reverse xs` with
    the remaining `ys` and the result accumulated in a pair. -/
def zipF (a b : Ty) : Expr :=
  .lam (.list a) (.lam (.list b)
    (revE (.prod a b) (sndE (.list b) (.list (.prod a b))
      (.fold
        (.lam a (.lam (.prod (.list b) (.list (.prod a b)))
          (pairE (.list b) (.list (.prod a b))
            (dropE b (litE Dim.zero 1) (fstE (.list b) (.list (.prod a b)) (.var 0)))
            (.fold (.prim (.cons (.prod a b))) (sndE (.list b) (.list (.prod a b)) (.var 0))
              (.fold (.lam b (.lam (.list (.prod a b)) (consE (.prod a b) (pairE a b (.var 3) (.var 1)) (.var 0))))
                (nilE (.prod a b)) (takeE b (litE Dim.zero 1) (fstE (.list b) (.list (.prod a b)) (.var 0))))))))
        (pairE (.list b) (.list (.prod a b)) (.var 0) (nilE (.prod a b)))
        (revE a (.var 1))))))

/-- A finite set literal `x ∈ {c₁, …, cₙ}` is `contains x [c₁, …, cₙ]`. -/
def oneOfE (τ : Ty) (h : τ.Data) (x : Expr) (cs : List Expr) : Expr := app2 (containsF τ h) x (listLit τ cs)

/-! ## Records: labeled products elaborate to nested pairs -/

/-- The type of a record with the given field types (right-nested). -/
def recTy : List Ty → Ty
  | [] => .bool
  | [τ] => τ
  | τ :: rest => .prod τ (recTy rest)

/-- A record value from its fields. -/
def recE : List (Ty × Expr) → Expr
  | [] => .boolLit true
  | [(_, e)] => e
  | (τ, e) :: rest => pairE τ (recTy (rest.map Prod.fst)) e (recE rest)

/-- Projection of field `i` (positional; labels resolve to positions at elaboration). -/
def projE : List Ty → Nat → Expr → Expr
  | [], _, e => e
  | [_], _, e => e
  | τ :: rest, 0, e => fstE τ (recTy rest) e
  | τ :: rest, i + 1, e => projE rest i (sndE τ (recTy rest) e)

/-! ## Combinators: the library discipline -/

/-- A *combinator*: variables, literals, lambdas, applications, registered
    operators, the recursor and representation observation — no reference,
    no state, no transport, no semantic construction.  (`rep` is admitted
    since Phase 9c: an ordered concept compares through its representation;
    `rep` is free everywhere and constructs nothing.) -/
def _root_.BDL.Expr.Comb : Expr → Prop
  | .var _ | .boolLit _ | .natLit _ | .prim _ => True
  | .lam _ b => b.Comb
  | .app f a => f.Comb ∧ a.Comb
  | .fold f z l => f.Comb ∧ z.Comb ∧ l.Comb
  | .rep e => e.Comb
  | _ => False

instance : ∀ e : Expr, Decidable e.Comb
  | .var _ | .boolLit _ | .natLit _ | .prim _ => inferInstanceAs (Decidable True)
  | .declRef _ | .delay _ _ | .sync _ _ _ | .mk _ _ => inferInstanceAs (Decidable False)
  | .rep e => instDecidableComb e
  | .lam _ b => instDecidableComb b
  | .app f a =>
    have := instDecidableComb f
    have := instDecidableComb a
    inferInstanceAs (Decidable (f.Comb ∧ a.Comb))
  | .fold f z l =>
    have := instDecidableComb f
    have := instDecidableComb z
    have := instDecidableComb l
    inferInstanceAs (Decidable (f.Comb ∧ z.Comb ∧ l.Comb))

theorem _root_.BDL.Expr.Comb.pure : ∀ {e : Expr}, e.Comb → e.Pure
  | .var _, _ | .boolLit _, _ | .natLit _, _ | .prim _, _ => trivial
  | .lam _ b, h => Expr.Comb.pure (e := b) h
  | .rep e, h => Expr.Comb.pure (e := e) h
  | .app f a, h => ⟨Expr.Comb.pure (e := f) h.1, Expr.Comb.pure (e := a) h.2⟩
  | .fold f z l, h => ⟨Expr.Comb.pure (e := f) h.1, Expr.Comb.pure (e := z) h.2.1, Expr.Comb.pure (e := l) h.2.2⟩
  | .declRef _, h | .delay _ _, h | .sync _ _ _, h | .mk _ _, h => h.elim

theorem _root_.BDL.Expr.Comb.refFree : ∀ {e : Expr}, e.Comb → e.RefFree
  | .var _, _ | .boolLit _, _ | .natLit _, _ | .prim _, _ => rfl
  | .lam _ b, h => Expr.Comb.refFree (e := b) h
  | .rep e, h => Expr.Comb.refFree (e := e) h
  | .app f a, h => by
    simp only [Expr.RefFree, Expr.refs, List.append_eq_nil_iff]
    exact ⟨Expr.Comb.refFree (e := f) h.1, Expr.Comb.refFree (e := a) h.2⟩
  | .fold f z l, h => by
    simp only [Expr.RefFree, Expr.refs, List.append_eq_nil_iff]
    exact ⟨⟨Expr.Comb.refFree (e := f) h.1, Expr.Comb.refFree (e := z) h.2.1⟩, Expr.Comb.refFree (e := l) h.2.2⟩
  | .declRef _, h | .delay _ _, h | .sync _ _ _, h | .mk _ _, h => h.elim

theorem _root_.BDL.Expr.Comb.delayFree : ∀ {e : Expr}, e.Comb → e.DelayFree
  | .var _, _ | .boolLit _, _ | .natLit _, _ | .prim _, _ => trivial
  | .lam _ b, h => Expr.Comb.delayFree (e := b) h
  | .rep e, h => Expr.Comb.delayFree (e := e) h
  | .app f a, h => ⟨Expr.Comb.delayFree (e := f) h.1, Expr.Comb.delayFree (e := a) h.2⟩
  | .fold f z l, h => ⟨Expr.Comb.delayFree (e := f) h.1, Expr.Comb.delayFree (e := z) h.2.1, Expr.Comb.delayFree (e := l) h.2.2⟩
  | .declRef _, h | .delay _ _, h | .sync _ _ _, h | .mk _ _, h => h.elim

/-- **`lib_no_construction`**: a combinator constructs no Sem value. -/
theorem _root_.BDL.Expr.Comb.noConstruct : ∀ {e : Expr}, e.Comb → ∀ s, ¬ e.constructs s
  | .var _, _, _, h | .boolLit _, _, _, h | .natLit _, _, _, h | .prim _, _, _, h => h
  | .lam _ b, hc, s, h => Expr.Comb.noConstruct (e := b) hc s h
  | .rep e, hc, s, h => Expr.Comb.noConstruct (e := e) hc s h
  | .app f a, hc, s, h => h.elim (Expr.Comb.noConstruct (e := f) hc.1 s) (Expr.Comb.noConstruct (e := a) hc.2 s)
  | .fold f z l, hc, s, h =>
    h.elim (Expr.Comb.noConstruct (e := f) hc.1 s)
      (fun h => h.elim (Expr.Comb.noConstruct (e := z) hc.2.1 s) (Expr.Comb.noConstruct (e := l) hc.2.2 s))
  | .declRef _, h, _, _ | .delay _ _, h, _, _ | .sync _ _ _, h, _, _ | .mk _ _, h, _, _ => h.elim

/-- **`lib_typing_context_free`**: a combinator's typing is independent of
    the declaration environment and the grant; it depends on the concept
    environment only through the representation bindings an ordered
    concept's `rep` reads (which are write-once: `mono_concept`). -/
theorem _root_.BDL.HasType.comb_irrelevant {Θ : ConceptEnv} {Δ Δ' : DeclEnv} {G G' : Grant} {Γ : Ctx} {e : Expr} {τ : Ty}
    (hc : e.Comb) (h : HasType Θ Δ G Γ e τ) : HasType Θ Δ' G' Γ e τ := by
  induction h with
  | var h => exact .var h
  | boolLit => exact .boolLit
  | natLit => exact .natLit
  | lam _ ih => exact .lam (ih hc)
  | app _ _ ihf iha => exact .app (ihf hc.1) (iha hc.2)
  | fold _ _ _ ihf ihz ihl => exact .fold (ihf hc.1) (ihz hc.2.1) (ihl hc.2.2)
  | rep hΘ _ ih => exact .rep hΘ (ih hc)
  | prim => exact .prim
  | declRef _ | mk _ _ _ _ | delay _ _ _ _ _ | sync _ _ _ _ _ => exact hc.elim

/-- **`lib_eval_context_free`**: a combinator's value in a closure-free
    environment is the same in every design, at every tick, under every
    input. -/
theorem lib_eval_context_free {Δ Δ' : DeclEnv} {I I' : Input} {t t' : Nat} {ρ : List Value} {e : Expr} {v : Value}
    (hc : e.Comb) (hρ : ∀ w ∈ ρ, w.NoClo) (h : Ev Δ I t ρ e v) : Ev Δ' I' t' ρ e v :=
  (Ev.pure h hc.pure (fun w hw => Value.Pure.of_noClo (hρ w hw))).2 Δ' I' t'

/-- **`lib_clocked`**: a combinator is clocked in every domain. -/
theorem lib_clocked (Κ : ClockEnv) {e : Expr} (hc : e.Comb) (c : Option ClockId) : Clocked Κ c e :=
  Clock.clockedB_of_closed e hc.refFree hc.delayFree c

/-- **`lib_expansion`** (all four preservation results at once): inlining a
    combinator `L` at a use site `L a` preserves typing under any environment
    change that preserves the argument's typing, adds no construction, and
    keeps the domain judgment exactly that of the argument. -/
theorem lib_expansion {Θ : ConceptEnv} {Δ Δ' : DeclEnv} {G G' : Grant} {Γ : Ctx} {L a : Expr} {dom cod : Ty}
    (hc : L.Comb) (hL : HasType Θ Δ G Γ L (.arr dom cod)) (ha : HasType Θ Δ' G' Γ a dom) (Κ : ClockEnv) (c : Option ClockId) :
    HasType Θ Δ' G' Γ (.app L a) cod ∧
    (∀ s, (Expr.app L a).constructs s → a.constructs s) ∧
    (Clocked Κ c (.app L a) ↔ Clocked Κ c a) := by
  refine ⟨.app (hL.comb_irrelevant hc) ha, fun s h => h.elim (fun h => (hc.noConstruct s h).elim) id, ?_⟩
  have := lib_clocked Κ hc c
  simp only [Clocked, clockedB, Bool.and_eq_true] at this ⊢
  exact ⟨fun h => h.2, fun h => ⟨this, h⟩⟩

/-! ## Every library entry is a combinator -/

theorem ltAt_comb : ∀ {τ : Ty} (o : Ordered τ) {a b : Expr}, a.Comb → b.Comb → (ltAt o a b).Comb
  | _, .q _, _, _, ha, hb => by simp [ltAt, ltE, app2, Expr.Comb, ha, hb]
  | _, .sem _ _, _, _, ha, hb => by simp [ltAt, ltE, app2, Expr.Comb, ha, hb]

theorem lib_comb (τ σ : Ty) (h : τ.Data) (o : Ordered τ) (d : Dim) :
    (idF τ).Comb ∧ (constF τ σ).Comb ∧ (swapF τ σ).Comb ∧ (minF o).Comb ∧ (maxF o).Comb ∧
    (clampF o).Comb ∧ (inRangeF o).Comb ∧ (inIntervalF o).Comb ∧ (minByF τ).Comb ∧ (maxByF τ).Comb ∧
    (foldrF τ σ).Comb ∧ (anyF τ).Comb ∧
    (allF τ).Comb ∧ (containsF τ h).Comb ∧ (mapF τ σ).Comb ∧ (filterF τ).Comb ∧ (appendF τ).Comb ∧
    (sumF d).Comb ∧ (optElimF τ σ).Comb ∧ (mapOptF τ σ).Comb ∧ (getOrElseF τ).Comb ∧ (zipF τ σ).Comb := by
  have hlt : ∀ i j : Nat, (ltAt o (.var i) (.var j)).Comb := fun _ _ => ltAt_comb o trivial trivial
  simp [Expr.Comb, idF, constF, swapF, minF, maxF, clampF, inRangeF, inIntervalF, minByF, maxByF, foldrF, anyF,
    allF, containsF, mapF, filterF, appendF, sumF, optElimF, mapOptF, getOrElseF, zipF, iteE, eqE, orE, andE, notE,
    consE, nilE, pairE, fstE, sndE, someE, noneE, toListE, takeE, dropE, revE, litE, app2, app3, hlt]

/-! ## Typing at every instance -/

section Typing
variable {Θ : ConceptEnv} {Δ : DeclEnv} {G : Grant} {Γ : Ctx}

theorem idF_typed (τ : Ty) : HasType Θ Δ G Γ (idF τ) (.arr τ τ) := .lam (.var rfl)
theorem constF_typed (τ σ : Ty) : HasType Θ Δ G Γ (constF τ σ) (.arr τ (.arr σ τ)) := .lam (.lam (.var rfl))
theorem swapF_typed (a b : Ty) : HasType Θ Δ G Γ (swapF a b) (.arr (.prod a b) (.prod b a)) :=
  .lam (.app (.app .prim (.app .prim (.var rfl))) (.app .prim (.var rfl)))
/-- Ordered evidence is *well formed* against the concept environment: an
    ordered concept is represented by a quantity of the stated dimension. -/
def Ordered.WF (Θ : ConceptEnv) : {τ : Ty} → Ordered τ → Prop
  | _, .q _ => True
  | _, .sem s d => Θ s = some (.q d)

theorem ltAt_typed {τ : Ty} (o : Ordered τ) (ho : o.WF Θ) {a b : Expr}
    (ha : HasType Θ Δ G Γ a τ) (hb : HasType Θ Δ G Γ b τ) : HasType Θ Δ G Γ (ltAt o a b) .bool := by
  cases o with
  | q d => exact .app (.app .prim ha) hb
  | sem s d => exact .app (.app .prim (.rep ho ha)) (.rep ho hb)

theorem minF_typed {τ : Ty} (o : Ordered τ) (ho : o.WF Θ) : HasType Θ Δ G Γ (minF o) (.arr τ (.arr τ τ)) :=
  .lam (.lam (.app (.app (.app .prim (ltAt_typed o ho (.var rfl) (.var rfl))) (.var rfl)) (.var rfl)))
theorem maxF_typed {τ : Ty} (o : Ordered τ) (ho : o.WF Θ) : HasType Θ Δ G Γ (maxF o) (.arr τ (.arr τ τ)) :=
  .lam (.lam (.app (.app (.app .prim (ltAt_typed o ho (.var rfl) (.var rfl))) (.var rfl)) (.var rfl)))
theorem clampF_typed {τ : Ty} (o : Ordered τ) (ho : o.WF Θ) : HasType Θ Δ G Γ (clampF o) (.arr τ (.arr τ (.arr τ τ))) :=
  .lam (.lam (.lam (.app (.app (maxF_typed o ho) (.var rfl)) (.app (.app (minF_typed o ho) (.var rfl)) (.var rfl)))))
theorem inRangeF_typed {τ : Ty} (o : Ordered τ) (ho : o.WF Θ) : HasType Θ Δ G Γ (inRangeF o) (.arr τ (.arr τ (.arr τ .bool))) :=
  .lam (.lam (.lam (.app (.app .prim (.app .prim (ltAt_typed o ho (.var rfl) (.var rfl))))
    (.app .prim (ltAt_typed o ho (.var rfl) (.var rfl))))))
theorem inIntervalF_typed {τ : Ty} (o : Ordered τ) (ho : o.WF Θ) : HasType Θ Δ G Γ (inIntervalF o) (.arr (.prod τ τ) (.arr τ .bool)) :=
  .lam (.lam (.app (.app (.app (inRangeF_typed o ho) (.var rfl)) (.app .prim (.var rfl))) (.app .prim (.var rfl))))
theorem minByF_typed (τ : Ty) : HasType Θ Δ G Γ (minByF τ) (.arr (.arr τ (.arr τ .bool)) (.arr τ (.arr τ τ))) :=
  .lam (.lam (.lam (.app (.app (.app .prim (.app (.app (.var rfl) (.var rfl)) (.var rfl))) (.var rfl)) (.var rfl))))
theorem maxByF_typed (τ : Ty) : HasType Θ Δ G Γ (maxByF τ) (.arr (.arr τ (.arr τ .bool)) (.arr τ (.arr τ τ))) :=
  .lam (.lam (.lam (.app (.app (.app .prim (.app (.app (.var rfl) (.var rfl)) (.var rfl))) (.var rfl)) (.var rfl))))
theorem foldrF_typed (τ σ : Ty) : HasType Θ Δ G Γ (foldrF τ σ) (.arr (.arr τ (.arr σ σ)) (.arr σ (.arr (.list τ) σ))) :=
  .lam (.lam (.lam (.fold (.var rfl) (.var rfl) (.var rfl))))
theorem anyF_typed (τ : Ty) : HasType Θ Δ G Γ (anyF τ) (.arr (.arr τ .bool) (.arr (.list τ) .bool)) :=
  .lam (.lam (.fold (.lam (.lam (.app (.app .prim (.app (.var rfl) (.var rfl))) (.var rfl)))) .boolLit (.var rfl)))
theorem allF_typed (τ : Ty) : HasType Θ Δ G Γ (allF τ) (.arr (.arr τ .bool) (.arr (.list τ) .bool)) :=
  .lam (.lam (.fold (.lam (.lam (.app (.app .prim (.app (.var rfl) (.var rfl))) (.var rfl)))) .boolLit (.var rfl)))
theorem containsF_typed (τ : Ty) (h : τ.Data) : HasType Θ Δ G Γ (containsF τ h) (.arr τ (.arr (.list τ) .bool)) :=
  .lam (.lam (.fold (.lam (.lam (.app (.app .prim (.app (.app .prim (.var rfl)) (.var rfl))) (.var rfl))))
    .boolLit (.var rfl)))
theorem mapF_typed (τ σ : Ty) : HasType Θ Δ G Γ (mapF τ σ) (.arr (.arr τ σ) (.arr (.list τ) (.list σ))) :=
  .lam (.lam (.fold (.lam (.lam (.app (.app .prim (.app (.var rfl) (.var rfl))) (.var rfl)))) .prim (.var rfl)))
theorem filterF_typed (τ : Ty) : HasType Θ Δ G Γ (filterF τ) (.arr (.arr τ .bool) (.arr (.list τ) (.list τ))) :=
  .lam (.lam (.fold (.lam (.lam (.app (.app (.app .prim (.app (.var rfl) (.var rfl)))
    (.app (.app .prim (.var rfl)) (.var rfl))) (.var rfl)))) .prim (.var rfl)))
theorem appendF_typed (τ : Ty) : HasType Θ Δ G Γ (appendF τ) (.arr (.list τ) (.arr (.list τ) (.list τ))) :=
  .lam (.lam (.fold .prim (.var rfl) (.var rfl)))
theorem sumF_typed (d : Dim) : HasType Θ Δ G Γ (sumF d) (.arr (.list (.q d)) (.q d)) :=
  .lam (.fold .prim .prim (.var rfl))
theorem optElimF_typed (τ σ : Ty) : HasType Θ Δ G Γ (optElimF τ σ) (.arr σ (.arr (.arr τ σ) (.arr (.opt τ) σ))) :=
  .lam (.lam (.lam (.fold (.lam (.lam (.app (.var rfl) (.var rfl)))) (.var rfl) (.app .prim (.var rfl)))))
theorem mapOptF_typed (τ σ : Ty) : HasType Θ Δ G Γ (mapOptF τ σ) (.arr (.arr τ σ) (.arr (.opt τ) (.opt σ))) :=
  .lam (.lam (.fold (.lam (.lam (.app .prim (.app (.var rfl) (.var rfl))))) .prim (.app .prim (.var rfl))))
theorem getOrElseF_typed (τ : Ty) : HasType Θ Δ G Γ (getOrElseF τ) (.arr (.opt τ) (.arr τ τ)) := .prim
theorem zipF_typed (a b : Ty) : HasType Θ Δ G Γ (zipF a b) (.arr (.list a) (.arr (.list b) (.list (.prod a b)))) :=
  .lam (.lam (.app .prim (.app .prim
    (.fold
      (.lam (.lam (.app (.app .prim (.app (.app .prim .prim) (.app .prim (.var rfl))))
        (.fold .prim (.app .prim (.var rfl))
          (.fold (.lam (.lam (.app (.app .prim (.app (.app .prim (.var rfl)) (.var rfl))) (.var rfl))))
            .prim (.app (.app .prim .prim) (.app .prim (.var rfl))))))))
      (.app (.app .prim (.var rfl)) .prim)
      (.app .prim (.var rfl))))))

theorem listLit_typed (τ : Ty) : ∀ es : List Expr, (∀ e ∈ es, HasType Θ Δ G Γ e τ) → HasType Θ Δ G Γ (listLit τ es) (.list τ)
  | [], _ => .prim
  | e :: es, h => .app (.app .prim (h e List.mem_cons_self)) (listLit_typed τ es fun e' he' => h e' (List.mem_cons_of_mem _ he'))

theorem oneOfE_typed (τ : Ty) (h : τ.Data) {x : Expr} (hx : HasType Θ Δ G Γ x τ) {cs : List Expr}
    (hcs : ∀ e ∈ cs, HasType Θ Δ G Γ e τ) : HasType Θ Δ G Γ (oneOfE τ h x cs) .bool :=
  .app (.app (containsF_typed τ h) hx) (listLit_typed τ cs hcs)

/-- Records: a record of well-typed fields has the record type, and each
    projection has its field's type. -/
theorem recE_typed : ∀ fs : List (Ty × Expr), (∀ p ∈ fs, HasType Θ Δ G Γ p.2 p.1) →
    HasType Θ Δ G Γ (recE fs) (recTy (fs.map Prod.fst))
  | [], _ => .boolLit
  | [(τ, e)], h => h (τ, e) List.mem_cons_self
  | (τ, e) :: p :: rest, h => by
    show HasType Θ Δ G Γ (pairE τ (recTy ((p :: rest).map Prod.fst)) e (recE (p :: rest))) (.prod τ (recTy ((p :: rest).map Prod.fst)))
    exact .app (.app .prim (h (τ, e) List.mem_cons_self)) (recE_typed (p :: rest) fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem projE_typed : ∀ (fs : List Ty) (i : Nat) {e : Expr} {τ : Ty}, fs[i]? = some τ →
    HasType Θ Δ G Γ e (recTy fs) → HasType Θ Δ G Γ (projE fs i e) τ
  | [], _, _, _, h, _ => by simp at h
  | [τ'], i, e, τ, h, he => by
    cases i with
    | zero => simp at h; subst h; exact he
    | succ i => simp at h
  | τ' :: p :: rest, 0, e, τ, h, he => by
    simp at h; subst h
    exact .app .prim he
  | τ' :: p :: rest, i + 1, e, τ, h, he => by
    simp only [List.getElem?_cons_succ] at h
    exact projE_typed (p :: rest) i h (.app .prim he)

end Typing

/-! ## Evaluation: the library computes the intended functions -/

section Eval
variable {Δ : DeclEnv} {I : Input} {t : Nat} {ρ : List Value}

theorem ev_lt (d : Dim) {a b : Expr} {m n : Nat} (ha : Ev Δ I t ρ a (.nat m)) (hb : Ev Δ I t ρ b (.nat n)) :
    Ev Δ I t ρ (ltE d a b) (.bool (decide (m < n))) := by
  have := Ev.appPrim (Ev.appPrim (Ev.prim (p := .lt d)) ha) hb
  simpa [ltE, app2, applyPrim, Prim.arity, Prim.compute] using this

/-- The magnitude an ordered value compares by. -/
def Ordered.key : {τ : Ty} → Ordered τ → Value → Option Nat
  | _, .q _, .nat n => some n
  | _, .sem s _, .sem s' (.nat n) => if s = s' then some n else none
  | _, _, _ => none

theorem ev_ltAt {τ : Ty} (o : Ordered τ) {a b : Expr} {va vb : Value} {m n : Nat}
    (ha : Ev Δ I t ρ a va) (hb : Ev Δ I t ρ b vb) (hm : o.key va = some m) (hn : o.key vb = some n) :
    Ev Δ I t ρ (ltAt o a b) (.bool (decide (m < n))) := by
  cases o with
  | q d =>
    cases va with
    | nat m' =>
      cases vb with
      | nat n' =>
        simp only [Ordered.key, Option.some.injEq] at hm hn
        subst hm hn
        exact ev_lt d ha hb
      | _ => simp [Ordered.key] at hn
    | _ => simp [Ordered.key] at hm
  | sem s d =>
    rcases va with _ | _ | ⟨s₁, _ | m' | _ | _ | _ | _ | _ | _ | _⟩ | _ | _ | _ | _ | _ | _ <;> simp [Ordered.key] at hm
    rcases vb with _ | _ | ⟨s₂, _ | n' | _ | _ | _ | _ | _ | _ | _⟩ | _ | _ | _ | _ | _ | _ <;> simp [Ordered.key] at hn
    obtain ⟨rfl, rfl⟩ := hm
    obtain ⟨rfl, rfl⟩ := hn
    exact ev_lt d (.rep ha) (.rep hb)

theorem ev_eq (τ : Ty) (h : τ.Data) {a b : Expr} {va vb : Value} (ha : Ev Δ I t ρ a va) (hb : Ev Δ I t ρ b vb) :
    Ev Δ I t ρ (eqE τ h a b) (.bool (Value.beq va vb)) := by
  have := Ev.appPrim (Ev.appPrim (Ev.prim (p := .eq τ h)) ha) hb
  simpa [eqE, app2, applyPrim, Prim.arity, Prim.compute] using this

theorem ev_ite (τ : Ty) {c a b : Expr} {x : Bool} {va vb : Value} (hc : Ev Δ I t ρ c (.bool x)) (ha : Ev Δ I t ρ a va)
    (hb : Ev Δ I t ρ b vb) : Ev Δ I t ρ (iteE τ c a b) (if x then va else vb) := by
  have := Ev.appPrim (Ev.appPrim (Ev.appPrim (Ev.prim (p := .ite τ)) hc) ha) hb
  simpa [iteE, app3, applyPrim, Prim.arity, Prim.compute] using this

theorem ev_or {a b : Expr} {x y : Bool} (ha : Ev Δ I t ρ a (.bool x)) (hb : Ev Δ I t ρ b (.bool y)) :
    Ev Δ I t ρ (orE a b) (.bool (x || y)) := by
  have := Ev.appPrim (Ev.appPrim (Ev.prim (p := .or)) ha) hb
  simpa [orE, app2, applyPrim, Prim.arity, Prim.compute] using this

theorem ev_and {a b : Expr} {x y : Bool} (ha : Ev Δ I t ρ a (.bool x)) (hb : Ev Δ I t ρ b (.bool y)) :
    Ev Δ I t ρ (andE a b) (.bool (x && y)) := by
  have := Ev.appPrim (Ev.appPrim (Ev.prim (p := .and)) ha) hb
  simpa [andE, app2, applyPrim, Prim.arity, Prim.compute] using this

theorem ev_not {a : Expr} {x : Bool} (ha : Ev Δ I t ρ a (.bool x)) : Ev Δ I t ρ (notE a) (.bool (!x)) := by
  have := Ev.appPrim (Ev.prim (p := .not)) ha
  simpa [notE, applyPrim, Prim.arity, Prim.compute] using this

theorem ev_cons (τ : Ty) {x l : Expr} {vx : Value} {vs : List Value} (hx : Ev Δ I t ρ x vx) (hl : Ev Δ I t ρ l (.list vs)) :
    Ev Δ I t ρ (consE τ x l) (.list (vx :: vs)) := by
  have := Ev.appPrim (Ev.appPrim (Ev.prim (p := .cons τ)) hx) hl
  simpa [consE, app2, applyPrim, Prim.arity, Prim.compute] using this

theorem ev_nil (τ : Ty) : Ev Δ I t ρ (nilE τ) (.list []) := by
  have := Ev.prim (Δ := Δ) (I := I) (t := t) (ρ := ρ) (p := .nil τ)
  simpa [nilE, applyPrim, Prim.arity, Prim.compute] using this

theorem ev_pair (a b : Ty) {x y : Expr} {vx vy : Value} (hx : Ev Δ I t ρ x vx) (hy : Ev Δ I t ρ y vy) :
    Ev Δ I t ρ (pairE a b x y) (.pair vx vy) := by
  have := Ev.appPrim (Ev.appPrim (Ev.prim (p := .pair a b)) hx) hy
  simpa [pairE, app2, applyPrim, Prim.arity, Prim.compute] using this

theorem ev_fst (a b : Ty) {p : Expr} {vx vy : Value} (hp : Ev Δ I t ρ p (.pair vx vy)) : Ev Δ I t ρ (fstE a b p) vx := by
  have := Ev.appPrim (Ev.prim (p := .fst a b)) hp
  simpa [fstE, applyPrim, Prim.arity, Prim.compute] using this

theorem ev_snd (a b : Ty) {p : Expr} {vx vy : Value} (hp : Ev Δ I t ρ p (.pair vx vy)) : Ev Δ I t ρ (sndE a b p) vy := by
  have := Ev.appPrim (Ev.prim (p := .snd a b)) hp
  simpa [sndE, applyPrim, Prim.arity, Prim.compute] using this

theorem ev_some (τ : Ty) {x : Expr} {vx : Value} (hx : Ev Δ I t ρ x vx) : Ev Δ I t ρ (someE τ x) (.some vx) := by
  have := Ev.appPrim (Ev.prim (p := .some τ)) hx
  simpa [someE, applyPrim, Prim.arity, Prim.compute] using this

theorem ev_listLit (τ : Ty) : ∀ {es : List Expr} {vs : List Value}, (∀ i (h : i < es.length) (h' : i < vs.length), Ev Δ I t ρ es[i] vs[i]) →
    es.length = vs.length → Ev Δ I t ρ (listLit τ es) (.list vs)
  | [], [], _, _ => ev_nil τ
  | e :: es, v :: vs, h, hl => by
    refine ev_cons τ (h 0 (Nat.succ_pos _) (Nat.succ_pos _))
      (ev_listLit τ (fun i hi hi' => h (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hi')) ?_)
    exact Nat.succ.inj hl
  | [], _ :: _, _, hl => nomatch hl
  | _ :: _, [], _, hl => nomatch hl

/-- **`min_spec`**: `min a b` is the argument with the smaller magnitude —
    the value itself, identity and all. -/
theorem min_spec {τ : Ty} (o : Ordered τ) {a b : Expr} {va vb : Value} {m n : Nat}
    (ha : Ev Δ I t ρ a va) (hb : Ev Δ I t ρ b vb) (hm : o.key va = some m) (hn : o.key vb = some n) :
    Ev Δ I t ρ (app2 (minF o) a b) (if m < n then va else vb) := by
  refine .appClo (.appClo .lam ha .lam) hb ?_
  have := ev_ite (Δ := Δ) (I := I) (t := t) τ (ev_ltAt o (Ev.var (i := 1) (ρ := vb :: va :: ρ) rfl) (Ev.var (i := 0) rfl) hm hn)
    (Ev.var (i := 1) rfl) (Ev.var (i := 0) rfl)
  simpa using this

theorem max_spec {τ : Ty} (o : Ordered τ) {a b : Expr} {va vb : Value} {m n : Nat}
    (ha : Ev Δ I t ρ a va) (hb : Ev Δ I t ρ b vb) (hm : o.key va = some m) (hn : o.key vb = some n) :
    Ev Δ I t ρ (app2 (maxF o) a b) (if m < n then vb else va) := by
  refine .appClo (.appClo .lam ha .lam) hb ?_
  have := ev_ite (Δ := Δ) (I := I) (t := t) τ (ev_ltAt o (Ev.var (i := 1) (ρ := vb :: va :: ρ) rfl) (Ev.var (i := 0) rfl) hm hn)
    (Ev.var (i := 0) rfl) (Ev.var (i := 1) rfl)
  simpa using this

theorem key_ite {τ : Ty} (o : Ordered τ) {c : Prop} [Decidable c] {va vb : Value} {m n : Nat}
    (hm : o.key va = some m) (hn : o.key vb = some n) : o.key (if c then va else vb) = some (if c then m else n) := by
  by_cases hc : c <;> simp [hc, hm, hn]

theorem clamp_spec {τ : Ty} (o : Ordered τ) {x lo hi : Expr} {vx vlo vhi : Value} {kx klo khi : Nat}
    (hx : Ev Δ I t ρ x vx) (hlo : Ev Δ I t ρ lo vlo) (hhi : Ev Δ I t ρ hi vhi)
    (hkx : o.key vx = some kx) (hklo : o.key vlo = some klo) (hkhi : o.key vhi = some khi) :
    Ev Δ I t ρ (app3 (clampF o) x lo hi)
      (if klo < (if kx < khi then kx else khi) then (if kx < khi then vx else vhi) else vlo) := by
  refine .appClo (.appClo (.appClo .lam hx .lam) hlo .lam) hhi ?_
  exact max_spec o (Ev.var (i := 1) rfl) (min_spec o (Ev.var (i := 2) rfl) (Ev.var (i := 0) rfl) hkx hkhi) hklo
    (key_ite o hkx hkhi)

theorem inRange_spec {τ : Ty} (o : Ordered τ) {x lo hi : Expr} {vx vlo vhi : Value} {kx klo khi : Nat}
    (hx : Ev Δ I t ρ x vx) (hlo : Ev Δ I t ρ lo vlo) (hhi : Ev Δ I t ρ hi vhi)
    (hkx : o.key vx = some kx) (hklo : o.key vlo = some klo) (hkhi : o.key vhi = some khi) :
    Ev Δ I t ρ (app3 (inRangeF o) x lo hi) (.bool (!decide (kx < klo) && !decide (khi < kx))) := by
  refine .appClo (.appClo (.appClo .lam hx .lam) hlo .lam) hhi ?_
  exact ev_and (ev_not (ev_ltAt o (Ev.var (i := 2) (ρ := vhi :: vlo :: vx :: ρ) rfl) (Ev.var (i := 1) rfl) hkx hklo))
    (ev_not (ev_ltAt o (Ev.var (i := 0) (ρ := vhi :: vlo :: vx :: ρ) rfl) (Ev.var (i := 2) rfl) hkhi hkx))

/-- **`minBy_spec`**: the comparator form picks by the comparator's verdict. -/
theorem minBy_spec (τ : Ty) {cmp a b : Expr} {vc va vb : Value} {r : Bool}
    (hc : Ev Δ I t ρ cmp vc) (ha : Ev Δ I t ρ a va) (hb : Ev Δ I t ρ b vb)
    (hcmp : ∃ g, Apply Δ I t vc va g ∧ Apply Δ I t g vb (.bool r)) :
    Ev Δ I t ρ (app3 (minByF τ) cmp a b) (if r then va else vb) := by
  refine .appClo (.appClo (.appClo .lam hc .lam) ha .lam) hb ?_
  obtain ⟨g, hg, hr⟩ := hcmp
  exact ev_ite τ (Ev.app_of_apply (Ev.app_of_apply (Ev.var (i := 2) rfl) (Ev.var (i := 1) rfl) hg) (Ev.var (i := 0) rfl) hr)
    (Ev.var (i := 1) rfl) (Ev.var (i := 0) rfl)

/-- **`minBy_recovers_min`**: the comparator `λa b. a < b` at an ordered
    type makes `minBy` compute exactly `min` — the escape hatch loses
    nothing, so a designer-defined order needs no class. -/
theorem minBy_recovers_min {τ : Ty} (o : Ordered τ) {a b : Expr} {va vb : Value} {m n : Nat}
    (ha : Ev Δ I t ρ a va) (hb : Ev Δ I t ρ b vb) (hm : o.key va = some m) (hn : o.key vb = some n) :
    Ev Δ I t ρ (app3 (minByF τ) (.lam τ (.lam τ (ltAt o (.var 1) (.var 0)))) a b) (if m < n then va else vb) := by
  have := minBy_spec (Δ := Δ) (I := I) (t := t) (ρ := ρ) τ (r := decide (m < n))
    (cmp := .lam τ (.lam τ (ltAt o (.var 1) (.var 0)))) .lam ha hb
    ⟨.clo (va :: ρ) (ltAt o (.var 1) (.var 0)), Or.inl ⟨_, _, rfl, .lam⟩,
     Or.inl ⟨_, _, rfl, ev_ltAt o (Ev.var (i := 1) (ρ := vb :: va :: ρ) rfl) (Ev.var (i := 0) rfl) hm hn⟩⟩
  simpa using this

/-- **The recursor computes `List.foldr`** when the step closure implements
    `g` on the reachable accumulators. -/
theorem fold_foldr {g : Value → Value → Value} {Inv : Value → Prop} {vf vz : Value} (hz : Inv vz)
    (hinv : ∀ x r, Inv r → Inv (g x r)) :
    ∀ vs, (∀ x ∈ vs, ∀ r, Inv r → Ev Δ I t [r, x, vf] stepVarTerm (g x r)) →
      Inv (vs.foldr g vz) ∧ Ev Δ I t [.list vs, vz, vf] foldVarTerm (vs.foldr g vz)
  | [], _ => ⟨hz, .foldNil (.var rfl) (.var rfl) (.var rfl)⟩
  | x :: xs, himpl => by
    obtain ⟨hi, hr⟩ := fold_foldr hz hinv xs (fun y hy => himpl y (List.mem_cons_of_mem _ hy))
    exact ⟨hinv x _ hi, .foldCons (.var rfl) (.var rfl) (.var rfl) hr (himpl x List.mem_cons_self _ hi)⟩

theorem fold_spec {g : Value → Value → Value} {Inv : Value → Prop} {f z l : Expr} {vf vz : Value} {vs : List Value}
    (hf : Ev Δ I t ρ f vf) (hz : Ev Δ I t ρ z vz) (hl : Ev Δ I t ρ l (.list vs)) (hzi : Inv vz)
    (hinv : ∀ x r, Inv r → Inv (g x r))
    (himpl : ∀ x ∈ vs, ∀ r, Inv r → Ev Δ I t [r, x, vf] stepVarTerm (g x r)) :
    Ev Δ I t ρ (.fold f z l) (vs.foldr g vz) := by
  cases vs with
  | nil => exact .foldNil hf hz hl
  | cons x xs =>
    obtain ⟨hi, hr⟩ := fold_foldr hzi hinv xs (fun y hy => himpl y (List.mem_cons_of_mem _ hy))
    exact .foldCons hf hz hl hr (himpl x List.mem_cons_self _ hi)

/-- A predicate value `vp` implements `P` on `vs`. -/
def Implements (Δ : DeclEnv) (I : Input) (t : Nat) (vp : Value) (P : Value → Bool) (vs : List Value) : Prop :=
  ∀ x ∈ vs, Apply Δ I t vp x (.bool (P x))

theorem foldr_or (P : Value → Bool) : ∀ vs : List Value, vs.foldr (fun x acc => P x || acc) false = vs.any P
  | [] => rfl
  | x :: xs => by simp [List.foldr, foldr_or P xs]

theorem foldr_and (P : Value → Bool) : ∀ vs : List Value, vs.foldr (fun x acc => P x && acc) true = vs.all P
  | [] => rfl
  | x :: xs => by simp [List.foldr, foldr_and P xs]

/-- **`any_spec`**: `any p xs` is `List.any`. -/
theorem any_spec (τ : Ty) {p xs : Expr} {vp : Value} {vs : List Value} {P : Value → Bool}
    (hp : Ev Δ I t ρ p vp) (hxs : Ev Δ I t ρ xs (.list vs)) (hP : Implements Δ I t vp P vs) :
    Ev Δ I t ρ (app2 (anyF τ) p xs) (.bool (vs.any P)) := by
  refine .appClo (.appClo .lam hp .lam) hxs ?_
  rw [← foldr_or P vs]
  have := fold_spec (Δ := Δ) (I := I) (t := t) (ρ := .list vs :: vp :: ρ) (g := fun x acc => .bool (P x || (acc.toBool?.getD false)))
    (f := .lam τ (.lam .bool (orE (.app (.var 3) (.var 1)) (.var 0))))
    (Inv := fun r => ∃ b, r = .bool b) .lam .boolLit (Ev.var (i := 0) rfl) ⟨false, rfl⟩ (fun _ _ _ => ⟨_, rfl⟩) ?_
  · have e : ∀ vs' : List Value, vs'.foldr (fun x acc => Value.bool (P x || (acc.toBool?.getD false))) (.bool false)
        = .bool (vs'.foldr (fun x acc => P x || acc) false) := by
      intro vs'; induction vs' with
      | nil => rfl
      | cons y ys ih => simp only [List.foldr_cons, ih]; rfl
    rw [e] at this
    exact this
  · rintro x hx r ⟨b, rfl⟩
    refine .appClo (.appClo (Ev.var (i := 2) rfl) (Ev.var (i := 1) rfl) .lam) (Ev.var (i := 0) rfl) ?_
    have := ev_or (Δ := Δ) (I := I) (t := t) (ρ := .bool b :: x :: .list vs :: vp :: ρ) (a := .app (.var 3) (.var 1)) (b := .var 0)
      (Ev.app_of_apply (Ev.var (i := 3) rfl) (Ev.var (i := 1) rfl) (hP x hx)) (Ev.var (i := 0) rfl)
    simpa [Value.toBool?] using this

/-- **`all_spec`**: `all p xs` is `List.all`. -/
theorem all_spec (τ : Ty) {p xs : Expr} {vp : Value} {vs : List Value} {P : Value → Bool}
    (hp : Ev Δ I t ρ p vp) (hxs : Ev Δ I t ρ xs (.list vs)) (hP : Implements Δ I t vp P vs) :
    Ev Δ I t ρ (app2 (allF τ) p xs) (.bool (vs.all P)) := by
  refine .appClo (.appClo .lam hp .lam) hxs ?_
  rw [← foldr_and P vs]
  have := fold_spec (Δ := Δ) (I := I) (t := t) (ρ := .list vs :: vp :: ρ) (g := fun x acc => .bool (P x && (acc.toBool?.getD true)))
    (f := .lam τ (.lam .bool (andE (.app (.var 3) (.var 1)) (.var 0))))
    (Inv := fun r => ∃ b, r = .bool b) .lam .boolLit (Ev.var (i := 0) rfl) ⟨true, rfl⟩ (fun _ _ _ => ⟨_, rfl⟩) ?_
  · have e : ∀ vs' : List Value, vs'.foldr (fun x acc => Value.bool (P x && (acc.toBool?.getD true))) (.bool true)
        = .bool (vs'.foldr (fun x acc => P x && acc) true) := by
      intro vs'; induction vs' with
      | nil => rfl
      | cons y ys ih => simp only [List.foldr_cons, ih]; rfl
    rw [e] at this
    exact this
  · rintro x hx r ⟨b, rfl⟩
    refine .appClo (.appClo (Ev.var (i := 2) rfl) (Ev.var (i := 1) rfl) .lam) (Ev.var (i := 0) rfl) ?_
    have := ev_and (Δ := Δ) (I := I) (t := t) (ρ := .bool b :: x :: .list vs :: vp :: ρ) (a := .app (.var 3) (.var 1)) (b := .var 0)
      (Ev.app_of_apply (Ev.var (i := 3) rfl) (Ev.var (i := 1) rfl) (hP x hx)) (Ev.var (i := 0) rfl)
    simpa [Value.toBool?] using this

/-- **`contains_spec`**: `contains x xs` is `List.any (beq x)`. -/
theorem contains_spec (τ : Ty) (h : τ.Data) {x xs : Expr} {vx : Value} {vs : List Value}
    (hx : Ev Δ I t ρ x vx) (hxs : Ev Δ I t ρ xs (.list vs)) :
    Ev Δ I t ρ (app2 (containsF τ h) x xs) (.bool (vs.any (Value.beq vx))) := by
  refine .appClo (.appClo .lam hx .lam) hxs ?_
  rw [← foldr_or (Value.beq vx) vs]
  have := fold_spec (Δ := Δ) (I := I) (t := t) (ρ := .list vs :: vx :: ρ)
    (g := fun y acc => .bool (Value.beq vx y || (acc.toBool?.getD false)))
    (f := .lam τ (.lam .bool (orE (eqE τ h (.var 3) (.var 1)) (.var 0))))
    (Inv := fun r => ∃ b, r = .bool b) .lam .boolLit (Ev.var (i := 0) rfl) ⟨false, rfl⟩ (fun _ _ _ => ⟨_, rfl⟩) ?_
  · have e : ∀ vs' : List Value, vs'.foldr (fun y acc => Value.bool (Value.beq vx y || (acc.toBool?.getD false))) (.bool false)
        = .bool (vs'.foldr (fun y acc => Value.beq vx y || acc) false) := by
      intro vs'; induction vs' with
      | nil => rfl
      | cons y ys ih => simp only [List.foldr_cons, ih]; rfl
    rw [e] at this
    exact this
  · rintro y hy r ⟨b, rfl⟩
    refine .appClo (.appClo (Ev.var (i := 2) rfl) (Ev.var (i := 1) rfl) .lam) (Ev.var (i := 0) rfl) ?_
    have := ev_or (Δ := Δ) (I := I) (t := t) (ρ := .bool b :: y :: .list vs :: vx :: ρ) (b := .var 0)
      (ev_eq τ h (Ev.var (i := 3) rfl) (Ev.var (i := 1) rfl)) (Ev.var (i := 0) rfl)
    simpa [Value.toBool?] using this

/-- A function value `vf` implements `F` on `vs`. -/
def ImplementsF (Δ : DeclEnv) (I : Input) (t : Nat) (vf : Value) (F : Value → Value) (vs : List Value) : Prop :=
  ∀ x ∈ vs, Apply Δ I t vf x (F x)

/-- **`map_spec`**: `map f xs` is `List.map`. -/
theorem map_spec (τ σ : Ty) {f xs : Expr} {vf : Value} {vs : List Value} {F : Value → Value}
    (hf : Ev Δ I t ρ f vf) (hxs : Ev Δ I t ρ xs (.list vs)) (hF : ImplementsF Δ I t vf F vs) :
    Ev Δ I t ρ (app2 (mapF τ σ) f xs) (.list (vs.map F)) := by
  refine .appClo (.appClo .lam hf .lam) hxs ?_
  have := fold_spec (Δ := Δ) (I := I) (t := t) (ρ := .list vs :: vf :: ρ)
    (g := fun x acc => match acc with | Value.list ws => Value.list (F x :: ws) | _ => acc)
    (f := .lam τ (.lam (.list σ) (consE σ (.app (.var 3) (.var 1)) (.var 0))))
    (Inv := fun r => ∃ ws, r = Value.list ws) .lam (ev_nil σ) (Ev.var (i := 0) rfl) ⟨[], rfl⟩
    (fun _ r ⟨ws, hw⟩ => by subst hw; exact ⟨_, rfl⟩) ?_
  · have e : ∀ vs' : List Value, vs'.foldr (fun x acc => match acc with | Value.list ws => Value.list (F x :: ws) | _ => acc) (Value.list [])
        = Value.list (vs'.map F) := by
      intro vs'; induction vs' with
      | nil => rfl
      | cons y ys ih => simp only [List.foldr_cons, ih]; rfl
    rw [e] at this
    exact this
  · rintro x hx r ⟨ws, rfl⟩
    refine .appClo (.appClo (Ev.var (i := 2) rfl) (Ev.var (i := 1) rfl) .lam) (Ev.var (i := 0) rfl) ?_
    exact ev_cons σ (Ev.app_of_apply (Ev.var (i := 3) rfl) (Ev.var (i := 1) rfl) (hF x hx)) (Ev.var (i := 0) rfl)

/-- **`filter_spec`**: `filter p xs` is `List.filter`. -/
theorem filter_spec (τ : Ty) {p xs : Expr} {vp : Value} {vs : List Value} {P : Value → Bool}
    (hp : Ev Δ I t ρ p vp) (hxs : Ev Δ I t ρ xs (.list vs)) (hP : Implements Δ I t vp P vs) :
    Ev Δ I t ρ (app2 (filterF τ) p xs) (.list (vs.filter P)) := by
  refine .appClo (.appClo .lam hp .lam) hxs ?_
  have := fold_spec (Δ := Δ) (I := I) (t := t) (ρ := .list vs :: vp :: ρ)
    (g := fun x acc => match acc with | Value.list ws => if P x then Value.list (x :: ws) else Value.list ws | _ => acc)
    (f := .lam τ (.lam (.list τ) (iteE (.list τ) (.app (.var 3) (.var 1)) (consE τ (.var 1) (.var 0)) (.var 0))))
    (Inv := fun r => ∃ ws, r = Value.list ws) .lam (ev_nil τ) (Ev.var (i := 0) rfl) ⟨[], rfl⟩
    (fun x r ⟨ws, hw⟩ => by subst hw; cases P x <;> simp) ?_
  · have e : ∀ vs' : List Value, vs'.foldr (fun x acc => match acc with
        | Value.list ws => if P x then Value.list (x :: ws) else Value.list ws | _ => acc) (Value.list [])
        = Value.list (vs'.filter P) := by
      intro vs'; induction vs' with
      | nil => rfl
      | cons y ys ih =>
        simp only [List.foldr_cons, ih]
        cases hy : P y <;> simp [hy]
    rw [e] at this
    exact this
  · rintro x hx r ⟨ws, rfl⟩
    refine .appClo (.appClo (Ev.var (i := 2) rfl) (Ev.var (i := 1) rfl) .lam) (Ev.var (i := 0) rfl) ?_
    have := ev_ite (Δ := Δ) (I := I) (t := t) (ρ := .list ws :: x :: .list vs :: vp :: ρ) (.list τ)
      (Ev.app_of_apply (Ev.var (i := 3) rfl) (Ev.var (i := 1) rfl) (hP x hx))
      (ev_cons τ (Ev.var (i := 1) rfl) (Ev.var (i := 0) rfl)) (Ev.var (i := 0) rfl)
    cases hx' : P x <;> simp only [hx'] at this ⊢ <;> simpa using this

end Eval

/-! ## Finite quantification is a fold -/

/-- **`forall_in_list`**: `∀ x ∈ xs, P x` holds iff `all xs P` evaluates to
    `true` — for a finite list, the executable fold and the logical
    quantifier coincide. -/
theorem forall_in_list {Δ : DeclEnv} {I : Input} {t : Nat} {ρ : List Value} (τ : Ty) {p xs : Expr} {vp : Value}
    {vs : List Value} {P : Value → Bool} (hp : Ev Δ I t ρ p vp) (hxs : Ev Δ I t ρ xs (.list vs))
    (hP : Implements Δ I t vp P vs) :
    (∀ x ∈ vs, P x = true) ↔ Ev Δ I t ρ (app2 (allF τ) p xs) (.bool true) := by
  constructor
  · intro h
    have := all_spec τ hp hxs hP
    rwa [List.all_eq_true.mpr h] at this
  · intro h
    have := (all_spec τ hp hxs hP).det h
    simp only [Value.bool.injEq] at this
    exact List.all_eq_true.mp this

/-- **`exists_in_list`**: `∃ x ∈ xs, P x` iff `any xs P` evaluates to `true`. -/
theorem exists_in_list {Δ : DeclEnv} {I : Input} {t : Nat} {ρ : List Value} (τ : Ty) {p xs : Expr} {vp : Value}
    {vs : List Value} {P : Value → Bool} (hp : Ev Δ I t ρ p vp) (hxs : Ev Δ I t ρ xs (.list vs))
    (hP : Implements Δ I t vp P vs) :
    (∃ x ∈ vs, P x = true) ↔ Ev Δ I t ρ (app2 (anyF τ) p xs) (.bool true) := by
  constructor
  · intro h
    have := any_spec τ hp hxs hP
    rwa [List.any_eq_true.mpr h] at this
  · intro h
    have := (any_spec τ hp hxs hP).det h
    simp only [Value.bool.injEq] at this
    exact List.any_eq_true.mp this

end BDL.Stdlib
