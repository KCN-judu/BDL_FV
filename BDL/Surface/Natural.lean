import BDL.Surface.Generic
import BDL.Surface.Poly

/-!
# Natural — binder and range syntax as conservative desugaring (Phase 11)

Designer-natural forms

    all x in xs: p      any x in xs: p      map x in xs: f      filter x in xs: p
    x in lo .. hi       x ?? d

elaborate to the Phase-9 library applied to an ordinary lambda:

    all x in xs: p  ↦  allF τ (λx. p) xs        x in lo .. hi  ↦  inRangeF o x lo hi

A binder local *is* the kernel's lambda parameter: elaboration resolves a
name to its de Bruijn index in the binder stack (nearest binder wins),
and nothing else is added — no kernel type, expression, value,
evaluator rule, clock rule or capability.  Everything proved here is an
instance of a Phase-9/9c theorem about the elaborated term:

* scoping (`elab_local_nearest`, `elab_shadow`) and alpha-equivalence
  (`desugar_rename`): a consistent fresh renaming does not change the
  elaboration;
* typing (`binder_all_typed`, …, `range_typed`): the local has the
  collection's element type, the body's type is what the library expects,
  and nominal identity is untouched;
* evaluation (`binder_all_eval`, …): exactly `all_spec`, `any_spec`,
  `map_spec`, `filter_spec`, `inRange_spec`; `natural_forall`,
  `natural_exists` are `forall_in_list`/`exists_in_list`;
* clocks (`binder_clock`, `range_clock`): the elaborated term is clocked
  exactly when its operands are — the library is clocked everywhere;
* no construction (`desugar_constructs`): a binder introduces no `mk`.

`Range` is a surface node only; there is no interval value or type.
-/

namespace BDL.Natural
open BDL BDL.Reactive BDL.Clock BDL.Stdlib

abbrev Name := String

inductive BinderKind where
  | all
  | any
  | map (σ : Ty)      -- the body's result type, chosen by local inference
  | filter
  deriving DecidableEq, Repr

/-- Natural expressions.  Type annotations (`τ`, `σ`, the `Ordered`
    evidence) are what local type inference decides before elaboration;
    the model starts after that step. -/
inductive NatExpr where
  /-- An embedded kernel term with no free variables: a reference, a
      literal, a library function, a rule.  Closed, so it needs no shifting
      under binders. -/
  | core (e : Expr)
  /-- A binder local, by name. -/
  | local (x : Name)
  | app (f a : NatExpr)
  /-- `k x in xs: body`, with `xs : list τ`. -/
  | binder (k : BinderKind) (τ : Ty) (x : Name) (xs body : NatExpr)
  /-- `x in lo .. hi` at an ordered type. -/
  | range {τ : Ty} (o : Ordered τ) (x lo hi : NatExpr)
  /-- `x ?? d` at `opt τ`. -/
  | coalesce (τ : Ty) (x d : NatExpr)

/-- Position of the nearest binder of `x`. -/
def lookup : List Name → Name → Option Nat
  | [], _ => none
  | y :: Γ, x => if x = y then some 0 else (lookup Γ x).map (· + 1)

/-- The elaborated binder for a kind. -/
def binderTerm (k : BinderKind) (τ : Ty) (b' xs' : Expr) : Expr :=
  match k with
  | .all => app2 (allF τ) (.lam τ b') xs'
  | .any => app2 (anyF τ) (.lam τ b') xs'
  | .map σ => app2 (mapF τ σ) (.lam τ b') xs'
  | .filter => app2 (filterF τ) (.lam τ b') xs'

/-- Elaboration under a binder stack: one-way, into the existing terms. -/
def desugar (Γ : List Name) : NatExpr → Option Expr
  | .core e => some e
  | .local x => (lookup Γ x).map .var
  | .app f a => (desugar Γ f).bind fun f' => (desugar Γ a).bind fun a' => some (.app f' a')
  | .binder k τ x xs body =>
    (desugar Γ xs).bind fun xs' => (desugar (x :: Γ) body).bind fun b' => some (binderTerm k τ b' xs')
  | .range o x lo hi =>
    (desugar Γ x).bind fun x' => (desugar Γ lo).bind fun lo' => (desugar Γ hi).bind fun hi' =>
      some (app3 (inRangeF o) x' lo' hi')
  | .coalesce τ x d => (desugar Γ x).bind fun x' => (desugar Γ d).bind fun d' => some (app2 (getOrElseF τ) x' d')

/-! ## §1 Scoping -/

/-- A local resolves to the nearest binder: index 0 directly under it. -/
theorem elab_local_nearest (Γ : List Name) (x : Name) : desugar (x :: Γ) (.local x) = some (.var 0) := by
  simp [desugar, lookup]

/-- Shadowing: the inner binder wins; the outer occurrence is one further out. -/
theorem elab_shadow (Γ : List Name) (x : Name) :
    desugar (x :: x :: Γ) (.local x) = some (.var 0) ∧ desugar (x :: Γ) (.local x) = some (.var 0) ∧
    (∀ y, y ≠ x → desugar (y :: x :: Γ) (.local x) = some (.var 1)) := by
  refine ⟨by simp [desugar, lookup], by simp [desugar, lookup], fun y hy => ?_⟩
  simp [desugar, lookup, Ne.symm hy]

/-- A name bound by no binder is an error: there is no free surface variable. -/
theorem elab_unbound (x : Name) : desugar [] (.local x) = none := rfl

/-- A binder never binds an ambient reference: a `core` term is untouched. -/
theorem elab_core (Γ : List Name) (e : Expr) : desugar Γ (.core e) = some e := rfl

/-! ## §2 Alpha-equivalence: a fresh consistent renaming is invisible -/

/-- The names a natural expression mentions (locals and binders). -/
def NatExpr.names : NatExpr → List Name
  | .core _ => []
  | .local x => [x]
  | .app f a => f.names ++ a.names
  | .binder _ _ x xs body => x :: xs.names ++ body.names
  | .range _ x lo hi => x.names ++ lo.names ++ hi.names
  | .coalesce _ x d => x.names ++ d.names

/-- Rename every occurrence of `a` (binders and locals) to `b`. -/
def NatExpr.rename (a b : Name) : NatExpr → NatExpr
  | .core e => .core e
  | .local x => .local (if x = a then b else x)
  | .app f g => .app (f.rename a b) (g.rename a b)
  | .binder k τ x xs body => .binder k τ (if x = a then b else x) (xs.rename a b) (body.rename a b)
  | .range o x lo hi => .range o (x.rename a b) (lo.rename a b) (hi.rename a b)
  | .coalesce τ x d => .coalesce τ (x.rename a b) (d.rename a b)

def sw (a b : Name) (x : Name) : Name := if x = a then b else x

theorem sw_ne (a b : Name) {x y : Name} (hxy : x ≠ y) (hx : x ≠ b) (hy : y ≠ b) : sw a b x ≠ sw a b y := by
  unfold sw
  by_cases hxa : x = a
  · subst hxa
    have hya : y ≠ x := Ne.symm hxy
    simp [hya]; exact Ne.symm hy
  · by_cases hya : y = a
    · subst hya; simp [hxa]; exact hx
    · simp [hxa, hya]; exact hxy

theorem lookup_map_sw (a b : Name) : ∀ (Γ : List Name) (x : Name), b ∉ Γ → x ≠ b →
    lookup (Γ.map (sw a b)) (sw a b x) = lookup Γ x
  | [], _, _, _ => rfl
  | y :: Γ, x, hb, hx => by
    simp only [List.map_cons, lookup]
    have hyb : y ≠ b := fun h => hb (h ▸ List.mem_cons_self)
    have hb' : b ∉ Γ := fun h => hb (List.mem_cons_of_mem _ h)
    by_cases hxy : x = y
    · subst hxy; simp
    · have : sw a b x ≠ sw a b y := sw_ne a b hxy hx hyb
      simp [hxy, this, lookup_map_sw a b Γ x hb' hx]

/-- **`desugar_rename`**: renaming `a` to a name `b` that occurs nowhere in the
    expression nor in the binder stack does not change the elaboration —
    binder locals are positions, not names. -/
theorem desugar_rename (a b : Name) : ∀ (e : NatExpr) (Γ : List Name), b ∉ e.names → b ∉ Γ →
    desugar (Γ.map (sw a b)) (e.rename a b) = desugar Γ e
  | .core _, _, _, _ => rfl
  | .local x, Γ, he, hΓ => by
    simp only [NatExpr.rename, desugar]
    have hx : x ≠ b := fun h => he (h ▸ List.mem_cons_self)
    rw [show (if x = a then b else x) = sw a b x from rfl, lookup_map_sw a b Γ x hΓ hx]
  | .app f g, Γ, he, hΓ => by
    simp only [NatExpr.names, List.mem_append, not_or] at he
    simp only [NatExpr.rename, desugar, desugar_rename a b f Γ he.1 hΓ, desugar_rename a b g Γ he.2 hΓ]
  | .binder k τ x xs body, Γ, he, hΓ => by
    simp only [NatExpr.names, List.mem_cons, List.mem_append, not_or] at he
    have hΓ' : b ∉ (x :: Γ) := by simp only [List.mem_cons, not_or]; exact ⟨he.1.1, hΓ⟩
    have hbody := desugar_rename a b body (x :: Γ) he.2 hΓ'
    simp only [List.map_cons] at hbody
    simp only [NatExpr.rename, desugar, desugar_rename a b xs Γ he.1.2 hΓ]
    rw [show (if x = a then b else x) = sw a b x from rfl, hbody]
  | .range o x lo hi, Γ, he, hΓ => by
    simp only [NatExpr.names, List.mem_append, not_or] at he
    simp only [NatExpr.rename, desugar, desugar_rename a b x Γ he.1.1 hΓ, desugar_rename a b lo Γ he.1.2 hΓ,
      desugar_rename a b hi Γ he.2 hΓ]
  | .coalesce τ x d, Γ, he, hΓ => by
    simp only [NatExpr.names, List.mem_append, not_or] at he
    simp only [NatExpr.rename, desugar, desugar_rename a b x Γ he.1 hΓ, desugar_rename a b d Γ he.2 hΓ]

/-- At the top level (empty stack) a fresh renaming is exactly alpha-equivalence. -/
theorem alpha (a b : Name) (e : NatExpr) (hb : b ∉ e.names) : desugar [] (e.rename a b) = desugar [] e :=
  desugar_rename a b e [] hb (by simp)

/-! ## §3 No construction, no references of its own -/

/-- The elaborated term constructs a concept only if an embedded core term
    does: binders introduce no `mk`. -/
def NatExpr.CoresNoConstruct (s : SemanticId) : NatExpr → Prop
  | .core e => ¬ e.constructs s
  | .local _ => True
  | .app f a => f.CoresNoConstruct s ∧ a.CoresNoConstruct s
  | .binder _ _ _ xs body => xs.CoresNoConstruct s ∧ body.CoresNoConstruct s
  | .range _ x lo hi => x.CoresNoConstruct s ∧ lo.CoresNoConstruct s ∧ hi.CoresNoConstruct s
  | .coalesce _ x d => x.CoresNoConstruct s ∧ d.CoresNoConstruct s

theorem desugar_constructs (s : SemanticId) : ∀ (e : NatExpr) (Γ : List Name) {e' : Expr},
    desugar Γ e = some e' → e.CoresNoConstruct s → ¬ e'.constructs s
  | .core _, _, _, h, hc => by cases h; exact hc
  | .local x, Γ, _, h, _ => by
    simp only [desugar, Option.map_eq_some_iff] at h
    obtain ⟨i, _, rfl⟩ := h
    simp [Expr.constructs]
  | .app f a, Γ, _, h, hc => by
    simp only [desugar, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨f', hf, a', ha, rfl⟩ := h
    simp only [Expr.constructs, not_or]
    exact ⟨desugar_constructs s f Γ hf hc.1, desugar_constructs s a Γ ha hc.2⟩
  | .binder k τ x xs body, Γ, _, h, hc => by
    simp only [desugar, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨xs', hxs, b', hb, rfl⟩ := h
    have h1 := desugar_constructs s xs Γ hxs hc.1
    have h2 := desugar_constructs s body (x :: Γ) hb hc.2
    cases k <;> simp [binderTerm, app2, allF, anyF, mapF, filterF, Expr.constructs, orE, andE, consE, iteE, nilE, app3, h1, h2]
  | @NatExpr.range τ o x lo hi, Γ, _, h, hc => by
    simp only [desugar, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x', hx, lo', hlo, hi', hhi, rfl⟩ := h
    have h1 := desugar_constructs s x Γ hx hc.1
    have h2 := desugar_constructs s lo Γ hlo hc.2.1
    have h3 := desugar_constructs s hi Γ hhi hc.2.2
    have := (lib_comb τ τ (by cases o <;> trivial) o Dim.zero).2.2.2.2.2.2.1.noConstruct s
    simp only [app3, Expr.constructs, not_or]
    exact ⟨⟨⟨this, h1⟩, h2⟩, h3⟩
  | .coalesce τ x d, Γ, _, h, hc => by
    simp only [desugar, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x', hx, d', hd, rfl⟩ := h
    simp only [app2, getOrElseF, Expr.constructs, not_or]
    exact ⟨⟨id, desugar_constructs s x Γ hx hc.1⟩, desugar_constructs s d Γ hd hc.2⟩

/-! ## §4 Typing: the local has the element type; the body what the library expects -/

section Typing
variable {Θ : ConceptEnv} {Δ : DeclEnv} {G : Grant} {Γ : Ctx}

/-- `all x in xs: p` — with `xs : list τ` and `p : bool` under `x : τ`. -/
theorem binder_all_typed (τ : Ty) {xs' b' : Expr}
    (hxs : HasType Θ Δ G Γ xs' (.list τ)) (hb : HasType Θ Δ G (τ :: Γ) b' .bool) :
    HasType Θ Δ G Γ (app2 (allF τ) (.lam τ b') xs') .bool :=
  .app (.app (allF_typed τ) (.lam hb)) hxs

theorem binder_any_typed (τ : Ty) {xs' b' : Expr}
    (hxs : HasType Θ Δ G Γ xs' (.list τ)) (hb : HasType Θ Δ G (τ :: Γ) b' .bool) :
    HasType Θ Δ G Γ (app2 (anyF τ) (.lam τ b') xs') .bool :=
  .app (.app (anyF_typed τ) (.lam hb)) hxs

/-- `map x in xs: f` — `f : σ` under `x : τ` gives `list σ`. -/
theorem binder_map_typed (τ σ : Ty) {xs' b' : Expr}
    (hxs : HasType Θ Δ G Γ xs' (.list τ)) (hb : HasType Θ Δ G (τ :: Γ) b' σ) :
    HasType Θ Δ G Γ (app2 (mapF τ σ) (.lam τ b') xs') (.list σ) :=
  .app (.app (mapF_typed τ σ) (.lam hb)) hxs

theorem binder_filter_typed (τ : Ty) {xs' b' : Expr}
    (hxs : HasType Θ Δ G Γ xs' (.list τ)) (hb : HasType Θ Δ G (τ :: Γ) b' .bool) :
    HasType Θ Δ G Γ (app2 (filterF τ) (.lam τ b') xs') (.list τ) :=
  .app (.app (filterF_typed τ) (.lam hb)) hxs

/-- **The local's type is forced by the collection** (inversion): if the
    elaborated binder is typed at all, the collection is a `list τ` and the
    body is typed with the local at `τ` — nominal `τ` included. -/
theorem binder_local_type [DecidablePred G] (τ : Ty) {xs' b' : Expr} {ρ : Ty}
    (h : HasType Θ Δ G Γ (app2 (allF τ) (.lam τ b') xs') ρ) :
    HasType Θ Δ G Γ xs' (.list τ) ∧ HasType Θ Δ G (τ :: Γ) b' .bool := by
  cases h with
  | app hf hxs =>
    cases hf with
    | app hall hlam =>
      have e := (allF_typed (Θ := Θ) (Δ := Δ) (G := G) (Γ := Γ) τ).unique hall
      simp only [Ty.arr.injEq] at e
      obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := e
      cases hlam with
      | lam hb => exact ⟨hxs, hb⟩

/-- `x in lo .. hi`: `x`, `lo`, `hi` all at the ordered type — the bounds
    must be of the same (nominal) type as the value, never merely of the
    same dimension. -/
theorem range_typed {τ : Ty} (o : Ordered τ) (ho : o.WF Θ) {x' lo' hi' : Expr}
    (hx : HasType Θ Δ G Γ x' τ) (hlo : HasType Θ Δ G Γ lo' τ) (hhi : HasType Θ Δ G Γ hi' τ) :
    HasType Θ Δ G Γ (app3 (inRangeF o) x' lo' hi') .bool :=
  .app (.app (.app (inRangeF_typed o ho) hx) hlo) hhi

/-- Inversion: bounds of another type are rejected. -/
theorem range_bounds_forced [DecidablePred G] {τ : Ty} (o : Ordered τ) (ho : o.WF Θ) {x' lo' hi' : Expr} {ρ : Ty}
    (h : HasType Θ Δ G Γ (app3 (inRangeF o) x' lo' hi') ρ) :
    HasType Θ Δ G Γ x' τ ∧ HasType Θ Δ G Γ lo' τ ∧ HasType Θ Δ G Γ hi' τ := by
  cases h with
  | app h3 hhi =>
    cases h3 with
    | app h2 hlo =>
      cases h2 with
      | app hf hx =>
        have e := (inRangeF_typed (Θ := Θ) (Δ := Δ) (G := G) (Γ := Γ) o ho).unique hf
        simp only [Ty.arr.injEq] at e
        obtain ⟨rfl, rfl, rfl, rfl⟩ := e
        exact ⟨hx, hlo, hhi⟩

theorem coalesce_typed (τ : Ty) {x' d' : Expr}
    (hx : HasType Θ Δ G Γ x' (.opt τ)) (hd : HasType Θ Δ G Γ d' τ) :
    HasType Θ Δ G Γ (app2 (getOrElseF τ) x' d') τ :=
  .app (.app (getOrElseF_typed τ) hx) hd

end Typing

/-! ## §5 Evaluation: exactly the library specifications -/

section Eval
variable {Δ : DeclEnv} {I : Input} {t : Nat} {ρ : List Value}

/-- The body evaluated with the local bound to each element implements `P`. -/
def BodyImplements (Δ : DeclEnv) (I : Input) (t : Nat) (ρ : List Value) (b' : Expr) (P : Value → Bool)
    (vs : List Value) : Prop :=
  ∀ x ∈ vs, Ev Δ I t (x :: ρ) b' (.bool (P x))

theorem bodyImplements_closure {b' : Expr} {P : Value → Bool} {vs : List Value}
    (h : BodyImplements Δ I t ρ b' P vs) : Implements Δ I t (.clo ρ b') P vs :=
  fun x hx => Or.inl ⟨ρ, b', rfl, h x hx⟩

/-- **`all x in xs: p` is `List.all`** (`all_spec`). -/
theorem binder_all_eval (τ : Ty) {xs' b' : Expr} {vs : List Value} {P : Value → Bool}
    (hxs : Ev Δ I t ρ xs' (.list vs)) (hb : BodyImplements Δ I t ρ b' P vs) :
    Ev Δ I t ρ (app2 (allF τ) (.lam τ b') xs') (.bool (vs.all P)) :=
  all_spec τ .lam hxs (bodyImplements_closure hb)

/-- **`any x in xs: p` is `List.any`** (`any_spec`). -/
theorem binder_any_eval (τ : Ty) {xs' b' : Expr} {vs : List Value} {P : Value → Bool}
    (hxs : Ev Δ I t ρ xs' (.list vs)) (hb : BodyImplements Δ I t ρ b' P vs) :
    Ev Δ I t ρ (app2 (anyF τ) (.lam τ b') xs') (.bool (vs.any P)) :=
  any_spec τ .lam hxs (bodyImplements_closure hb)

/-- **`filter x in xs: p` is `List.filter`** (`filter_spec`). -/
theorem binder_filter_eval (τ : Ty) {xs' b' : Expr} {vs : List Value} {P : Value → Bool}
    (hxs : Ev Δ I t ρ xs' (.list vs)) (hb : BodyImplements Δ I t ρ b' P vs) :
    Ev Δ I t ρ (app2 (filterF τ) (.lam τ b') xs') (.list (vs.filter P)) :=
  filter_spec τ .lam hxs (bodyImplements_closure hb)

/-- **`map x in xs: f` is `List.map`** (`map_spec`). -/
theorem binder_map_eval (τ σ : Ty) {xs' b' : Expr} {vs : List Value} {F : Value → Value}
    (hxs : Ev Δ I t ρ xs' (.list vs)) (hb : ∀ x ∈ vs, Ev Δ I t (x :: ρ) b' (F x)) :
    Ev Δ I t ρ (app2 (mapF τ σ) (.lam τ b') xs') (.list (vs.map F)) :=
  map_spec τ σ .lam hxs (fun x hx => Or.inl ⟨ρ, b', rfl, hb x hx⟩)

/-- **Finite universal meaning** of `all x in xs: p` (`forall_in_list`). -/
theorem natural_forall (τ : Ty) {xs' b' : Expr} {vs : List Value} {P : Value → Bool}
    (hxs : Ev Δ I t ρ xs' (.list vs)) (hb : BodyImplements Δ I t ρ b' P vs) :
    (∀ x ∈ vs, P x = true) ↔ Ev Δ I t ρ (app2 (allF τ) (.lam τ b') xs') (.bool true) :=
  forall_in_list τ .lam hxs (bodyImplements_closure hb)

/-- **Finite existential meaning** of `any x in xs: p` (`exists_in_list`). -/
theorem natural_exists (τ : Ty) {xs' b' : Expr} {vs : List Value} {P : Value → Bool}
    (hxs : Ev Δ I t ρ xs' (.list vs)) (hb : BodyImplements Δ I t ρ b' P vs) :
    (∃ x ∈ vs, P x = true) ↔ Ev Δ I t ρ (app2 (anyF τ) (.lam τ b') xs') (.bool true) :=
  exists_in_list τ .lam hxs (bodyImplements_closure hb)

/-- **`x in lo .. hi` is `lo ≤ x ∧ x ≤ hi`** on the compared magnitudes
    (`inRange_spec`), and nothing else. -/
theorem range_eval {τ : Ty} (o : Ordered τ) {x' lo' hi' : Expr} {vx vlo vhi : Value} {kx klo khi : Nat}
    (hx : Ev Δ I t ρ x' vx) (hlo : Ev Δ I t ρ lo' vlo) (hhi : Ev Δ I t ρ hi' vhi)
    (hkx : o.key vx = some kx) (hklo : o.key vlo = some klo) (hkhi : o.key vhi = some khi) :
    Ev Δ I t ρ (app3 (inRangeF o) x' lo' hi') (.bool (decide (klo ≤ kx ∧ kx ≤ khi))) := by
  have := inRange_spec o hx hlo hhi hkx hklo hkhi
  have e : (!decide (kx < klo) && !decide (khi < kx)) = decide (klo ≤ kx ∧ kx ≤ khi) := by
    by_cases h1 : kx < klo
    · rw [decide_eq_true h1]
      have : ¬ (klo ≤ kx ∧ kx ≤ khi) := fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h1 h.1)
      rw [decide_eq_false this]; rfl
    · rw [decide_eq_false h1]
      by_cases h2 : khi < kx
      · rw [decide_eq_true h2]
        have : ¬ (klo ≤ kx ∧ kx ≤ khi) := fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h2 h.2)
        rw [decide_eq_false this]; rfl
      · rw [decide_eq_false h2]
        have : klo ≤ kx ∧ kx ≤ khi := ⟨Nat.le_of_not_lt h1, Nat.le_of_not_lt h2⟩
        rw [decide_eq_true this]; rfl
  rwa [e] at this

end Eval

/-! ## §6 Clocks: nothing new -/

open BDL.Clock in
/-- **`binder_clock`**: the elaborated binder is clocked exactly when the
    collection and the body are — the library combinator is clocked in
    every domain (`lib_clocked`), and a lambda is clocked as its body. -/
theorem allF_comb (τ : Ty) : (allF τ).Comb := by simp [Expr.Comb, allF, app2, andE]
theorem anyF_comb (τ : Ty) : (anyF τ).Comb := by simp [Expr.Comb, anyF, app2, orE]
theorem mapF_comb (τ σ : Ty) : (mapF τ σ).Comb := by simp [Expr.Comb, mapF, app2, consE, nilE]
theorem filterF_comb (τ : Ty) : (filterF τ).Comb := by simp [Expr.Comb, filterF, app2, app3, iteE, consE, nilE]

theorem binder_clock (Κ : ClockEnv) (c : Option ClockId) (k : BinderKind) (τ : Ty) (xs' b' : Expr) :
    Clocked Κ c (binderTerm k τ b' xs') ↔ Clocked Κ c b' ∧ Clocked Κ c xs' := by
  have hall := lib_clocked Κ (allF_comb τ) c
  have hany := lib_clocked Κ (anyF_comb τ) c
  have hfil := lib_clocked Κ (filterF_comb τ) c
  cases k with
  | map σ =>
    have hmap := lib_clocked Κ (mapF_comb τ σ) c
    simp only [Clocked, clockedB, app2, binderTerm, Bool.and_eq_true] at hmap ⊢
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hmap, h.1⟩, h.2⟩⟩
  | all =>
    simp only [Clocked, clockedB, app2, binderTerm, Bool.and_eq_true] at hall ⊢
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hall, h.1⟩, h.2⟩⟩
  | any =>
    simp only [Clocked, clockedB, app2, binderTerm, Bool.and_eq_true] at hany ⊢
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hany, h.1⟩, h.2⟩⟩
  | filter =>
    simp only [Clocked, clockedB, app2, binderTerm, Bool.and_eq_true] at hfil ⊢
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hfil, h.1⟩, h.2⟩⟩

open BDL.Clock in
theorem range_clock (Κ : ClockEnv) (c : Option ClockId) {τ : Ty} (o : Ordered τ) (x' lo' hi' : Expr) :
    Clocked Κ c (app3 (inRangeF o) x' lo' hi') ↔ Clocked Κ c x' ∧ Clocked Κ c lo' ∧ Clocked Κ c hi' := by
  have h := lib_clocked Κ (lib_comb τ τ (by cases o <;> trivial) o Dim.zero).2.2.2.2.2.2.1 c
  simp only [Clocked, clockedB, app3, Bool.and_eq_true] at h ⊢
  exact ⟨fun h => ⟨h.1.1.2, h.1.2, h.2⟩, fun h' => ⟨⟨⟨h, h'.1⟩, h'.2.1⟩, h'.2.2⟩⟩

end BDL.Natural
