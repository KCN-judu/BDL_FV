/-!
# Base — object language

A tiny simply typed language, extended (Phase 1) with references to design
declarations by *identity*: `Expr.declRef d`.  Nothing about a declaration's
interface or realization lives in the syntax; a reference is a name, resolved
against a `DeclEnv` (see `Decl.lean`) at typing time.
-/

namespace BDL

/-- Stable identity of a **concept** (Phase 2) — the *type* level of the
    ladder representation → concept → Sem block → value (FVD-0164):
    a concept is a type, a template; a declaration of type `sem C` is a
    **Sem block**, one instance of it holding one value per tick.  Distinct
    from `DeclId`: conflating a concept with a declaration admits category
    errors (see `Experiments.SemanticTypeAlternatives`, Model C).  Display
    names are surface data and are not part of identity.  (Before Phase 22
    this was `SemanticId`; theorem names keep their historical spelling,
    "concept identity" reading "concept identity".) -/
structure ConceptId where
  n : Nat
  deriving DecidableEq, Repr

/-- Nominal identity of a clock domain (Phase 5).  Distinct from any rate:
    two domains at equal rates with no phase relationship are distinct. -/
structure ClockId where
  n : Nat
  deriving DecidableEq, Repr

/-- Physical dimension as an exponent vector over base dimensions
    (Phase 3; Phase 10 adds mass and temperature for the unit and
    formula-composer cases).  Enough to test the abstraction; not an SI
    catalogue — the base set is not a kernel decision, the group structure
    is. -/
structure Dim where
  length : Int
  time   : Int
  angle  : Int
  mass   : Int := 0
  temp   : Int := 0
  deriving DecidableEq, Repr

namespace Dim
def zero : Dim := ⟨0, 0, 0, 0, 0⟩
def add (a b : Dim) : Dim :=
  ⟨a.length + b.length, a.time + b.time, a.angle + b.angle, a.mass + b.mass, a.temp + b.temp⟩
def sub (a b : Dim) : Dim :=
  ⟨a.length - b.length, a.time - b.time, a.angle - b.angle, a.mass - b.mass, a.temp - b.temp⟩
def Length : Dim := ⟨1, 0, 0, 0, 0⟩
def Time   : Dim := ⟨0, 1, 0, 0, 0⟩
def Angle  : Dim := ⟨0, 0, 1, 0, 0⟩
def Mass   : Dim := ⟨0, 0, 0, 1, 0⟩
def Temp   : Dim := ⟨0, 0, 0, 0, 1⟩

/-! Dimensions form an abelian group under `add` with inverse `sub zero`:
    the algebra the Formula Composer solves one-hole equations in. -/
theorem add_comm (a b : Dim) : a.add b = b.add a := by
  simp [Dim.add, Int.add_comm]
theorem add_assoc (a b c : Dim) : (a.add b).add c = a.add (b.add c) := by
  simp [Dim.add, Int.add_assoc]
theorem add_zero (a : Dim) : a.add zero = a := by simp [Dim.add, zero]
theorem zero_add (a : Dim) : zero.add a = a := by simp [Dim.add, zero]
theorem sub_self (a : Dim) : a.sub a = zero := by simp [Dim.sub, zero]
theorem add_sub_cancel (a b : Dim) : (a.add b).sub b = a := by simp [Dim.add, Dim.sub]
theorem sub_add_cancel (a b : Dim) : (a.sub b).add b = a := by simp [Dim.add, Dim.sub]
theorem add_sub_cancel_left (a b : Dim) : (a.add b).sub a = b := by
  simp only [Dim.add, Dim.sub]
  have h : ∀ x y : Int, x + y - x = y := fun x y => by omega
  simp [h]
end Dim

inductive Ty where
  | bool
  | nat
  | arr (dom cod : Ty)
  /-- Phase 2: the nominal type of the **Sem values** of concept `s` — read
      `sem s` as "a Sem of `s`".  Two distinct concepts are distinct types
      regardless of any eventual representation.  Sem values are observed
      with `Expr.rep` and constructed with `Expr.mk` — the latter only inside
      the realization of a declaration whose signature announces the type
      (`Ty.grant`). -/
  | sem (s : ConceptId)
  /-- Phase 3: a physical quantity of dimension `d`.  The representation type
      of physical concepts.  `nat` remains for counts. -/
  | q (d : Dim)
  /-- Phase 4: optional value.  `opt τ` streams are the single-domain model
      of events (at most one occurrence per tick). -/
  | opt (τ : Ty)
  /-- Phase 9a: ordinary list data.  The cross-domain *window* of source
      occurrences is a `list τ` at the destination; `Event` is still not a
      type, and buffering is surface elaboration over `delay`/`sync`. -/
  | list (τ : Ty)
  /-- Phase 9b: a product — value-level composition only.  A pair is data
      when both components are; it is never a component interface, an
      output bundle, or a system boundary. -/
  | prod (a b : Ty)
  deriving DecidableEq, Repr

/-- A type mentioning no concept. -/
def Ty.SemFree : Ty → Prop
  | .sem _ => False
  | .arr a b => a.SemFree ∧ b.SemFree
  | .opt τ => τ.SemFree
  | .list τ => τ.SemFree
  | .prod a b => a.SemFree ∧ b.SemFree
  | _ => True

instance : ∀ τ : Ty, Decidable τ.SemFree
  | .bool => inferInstanceAs (Decidable True)
  | .nat => inferInstanceAs (Decidable True)
  | .q _ => inferInstanceAs (Decidable True)
  | .sem _ => inferInstanceAs (Decidable False)
  | .opt τ => instDecidableSemFree τ
  | .list τ => instDecidableSemFree τ
  | .arr a b =>
    have := instDecidableSemFree a
    have := instDecidableSemFree b
    inferInstanceAs (Decidable (a.SemFree ∧ b.SemFree))
  | .prod a b =>
    have := instDecidableSemFree a
    have := instDecidableSemFree b
    inferInstanceAs (Decidable (a.SemFree ∧ b.SemFree))

/-- A *data* type: no function type inside.  Phase 4: only data may be
    delayed — temporal state stores values, not behaviour. -/
def Ty.Data : Ty → Prop
  | .arr _ _ => False
  | .opt τ => τ.Data
  | .list τ => τ.Data
  | .prod a b => a.Data ∧ b.Data
  | _ => True

instance : ∀ τ : Ty, Decidable τ.Data
  | .bool => inferInstanceAs (Decidable True)
  | .nat => inferInstanceAs (Decidable True)
  | .q _ => inferInstanceAs (Decidable True)
  | .sem _ => inferInstanceAs (Decidable True)
  | .opt τ => instDecidableData τ
  | .list τ => instDecidableData τ
  | .arr _ _ => inferInstanceAs (Decidable False)
  | .prod a b =>
    have := instDecidableData a
    have := instDecidableData b
    inferInstanceAs (Decidable (a.Data ∧ b.Data))

/-- **`list_data`** (Phase 9a): a list is data exactly when its elements
    are, so lists may be delayed and transported like any other data. -/
theorem Ty.list_data (τ : Ty) : (Ty.list τ).Data ↔ τ.Data := Iff.rfl
theorem Ty.list_semFree (τ : Ty) : (Ty.list τ).SemFree ↔ τ.SemFree := Iff.rfl

/-- **`prod_data`** (Phase 9b): a pair is data exactly when both components
    are — so paired state may be delayed and transported. -/
theorem Ty.prod_data (a b : Ty) : (Ty.prod a b).Data ↔ a.Data ∧ b.Data := Iff.rfl
theorem Ty.prod_semFree (a b : Ty) : (Ty.prod a b).SemFree ↔ a.SemFree ∧ b.SemFree := Iff.rfl

/-- Registered pure operators (the paper's `p(e₁,…,eₙ)`).  Dimension algebra
    lives entirely in their types; typing an application is ordinary STLC. -/
inductive Prim where
  -- Phase 3: dimensioned arithmetic
  | lit (d : Dim) (n : Nat)
  | add (d : Dim)
  | sub (d : Dim)
  | mul (d₁ d₂ : Dim)
  | div (d₁ d₂ : Dim)
  -- Phase 4: comparisons, booleans, conditionals, options (plain STLC data).
  -- Phase 9c (capability audit): `lt` is a *quantity* comparison only —
  -- ordering is a property of dimensioned magnitudes, not of data in
  -- general; an ordered concept compares through its representation at
  -- elaboration (`Stdlib.Ordered`).  `eq` is structural equality on every
  -- *data* type (Phase 9b); the proof field makes `eq` at a function type
  -- unwritable — the kernel's only capability evidence.
  | lt (d : Dim)
  | eq (τ : Ty) (h : τ.Data)
  | not
  | and
  | or
  | ite (τ : Ty)
  | none (τ : Ty)
  | some (τ : Ty)
  | isSome (τ : Ty)
  | getD (τ : Ty)
  -- Phase 9a: list data — constructors and a first-order eliminator set.
  -- No `fold`: primitives never apply closures, so a general eliminator
  -- would need a new evaluation rule; the buffer needs none of it.
  | nil (τ : Ty)
  | cons (τ : Ty)
  | length (τ : Ty)
  | take (τ : Ty)
  | reverse (τ : Ty)
  | head (τ : Ty)
  -- Phase 9b: products — construction and the two projections.
  | pair (a b : Ty)
  | fst (a b : Ty)
  | snd (a b : Ty)
  -- Phase 9b: `drop` (dual of `take`) and `toList` — an option is a list of
  -- length at most one, so `fold` eliminates options too.
  | drop (τ : Ty)
  | toList (τ : Ty)
  deriving DecidableEq, Repr

def Prim.ty : Prim → Ty
  | .lit d _ => .q d
  | .add d => .arr (.q d) (.arr (.q d) (.q d))
  | .sub d => .arr (.q d) (.arr (.q d) (.q d))
  | .mul d₁ d₂ => .arr (.q d₁) (.arr (.q d₂) (.q (d₁.add d₂)))
  | .div d₁ d₂ => .arr (.q d₁) (.arr (.q d₂) (.q (d₁.sub d₂)))
  | .lt d => .arr (.q d) (.arr (.q d) .bool)
  | .eq τ _ => .arr τ (.arr τ .bool)
  | .not => .arr .bool .bool
  | .and => .arr .bool (.arr .bool .bool)
  | .or => .arr .bool (.arr .bool .bool)
  | .ite τ => .arr .bool (.arr τ (.arr τ τ))
  | .none τ => .opt τ
  | .some τ => .arr τ (.opt τ)
  | .isSome τ => .arr (.opt τ) .bool
  | .getD τ => .arr (.opt τ) (.arr τ τ)
  | .nil τ => .list τ
  | .cons τ => .arr τ (.arr (.list τ) (.list τ))
  | .length τ => .arr (.list τ) (.q Dim.zero)
  | .take τ => .arr (.q Dim.zero) (.arr (.list τ) (.list τ))
  | .reverse τ => .arr (.list τ) (.list τ)
  | .head τ => .arr (.list τ) (.opt τ)
  | .pair a b => .arr a (.arr b (.prod a b))
  | .fst a b => .arr (.prod a b) a
  | .snd a b => .arr (.prod a b) b
  | .drop τ => .arr (.q Dim.zero) (.arr (.list τ) (.list τ))
  | .toList τ => .arr (.opt τ) (.list τ)

/-- Stable identity of a design declaration — an ordinary declaration name,
    not a novel abstraction (Phase 1 report §1.5,
    `docs/reports/phase-01-cross-declaration-references.md`).  A wrapper rather
    than a bare `Nat` so ids cannot be confused with de Bruijn indices or numerals.
    Display names are a surface concern and are not modelled. -/
structure DeclId where
  n : Nat
  deriving DecidableEq, Repr

inductive Expr where
  | var (i : Nat)                 -- de Bruijn index
  | boolLit (b : Bool)
  | natLit (n : Nat)
  | lam (dom : Ty) (body : Expr)  -- binder annotated with its domain
  | app (f a : Expr)
  | declRef (d : DeclId)          -- Phase 1: reference to a declaration by id
  | rep (e : Expr)                -- Phase 3: observe a Sem value's representation
  | mk (s : ConceptId) (e : Expr) -- Phase 3: construct a Sem value (granted only)
  | prim (p : Prim)               -- Phase 3: registered operator
  | delay (init e : Expr)         -- Phase 4: the value of `e` one tick ago; `init` at tick 0
  /-- Phase 5: cross-domain transport.  The value of `e` (evaluated in domain
      `src`) at the last activation of `src` strictly before now; `init` if
      there was none.  `delay init e` is `sync own init e`. -/
  | sync (src : ClockId) (init e : Expr)
  /-- Phase 9b: the list recursor, `fold f z [x₁, …, xₙ] = f x₁ (… (f xₙ z))`.
      The one term former that applies a function value in the course of
      evaluation; registered operators never do.  Every generic collection
      operation (`map`, `any`, `all`, `contains`, `filter`) is a definition
      over it (`Surface/Stdlib.lean`). -/
  | fold (f z l : Expr)
  deriving DecidableEq, Repr

/-- Typing context: the type of de Bruijn index `i` is `Γ[i]?`. -/
abbrev Ctx := List Ty

/-- The declarations a term refers to (with multiplicity; order irrelevant). -/
def Expr.refs : Expr → List DeclId
  | .var _ | .boolLit _ | .natLit _ | .prim _ => []
  | .lam _ b => b.refs
  | .app f a => f.refs ++ a.refs
  | .declRef d => [d]
  | .rep e => e.refs
  | .mk _ e => e.refs
  | .delay i e => i.refs ++ e.refs
  | .sync _ i e => i.refs ++ e.refs
  | .fold f z l => f.refs ++ z.refs ++ l.refs

/-- The declarations a term refers to *instantaneously*: those not under a
    `delay`.  (The initial value of a delay is read at tick 0, so it is
    instantaneous; the delayed operand is read one tick late.) -/
def Expr.instRefs : Expr → List DeclId
  | .var _ | .boolLit _ | .natLit _ | .prim _ => []
  | .lam _ b => b.instRefs
  | .app f a => f.instRefs ++ a.instRefs
  | .declRef d => [d]
  | .rep e => e.instRefs
  | .mk _ e => e.instRefs
  | .delay i _ => i.instRefs
  | .sync _ i _ => i.instRefs   -- a transport reads strictly earlier: never instantaneous
  | .fold f z l => f.instRefs ++ z.instRefs ++ l.instRefs

/-- Does the term contain a `delay`?  The timeless fragment is delay-free. -/
def Expr.DelayFree : Expr → Prop
  | .lam _ b => b.DelayFree
  | .app f a => f.DelayFree ∧ a.DelayFree
  | .rep e => e.DelayFree
  | .mk _ e => e.DelayFree
  | .delay _ _ => False
  | .sync _ _ _ => False
  | .fold f z l => f.DelayFree ∧ z.DelayFree ∧ l.DelayFree
  | _ => True

instance : ∀ e : Expr, Decidable e.DelayFree
  | .var _ | .boolLit _ | .natLit _ | .prim _ | .declRef _ => inferInstanceAs (Decidable True)
  | .lam _ b => instDecidableDelayFree b
  | .app f a =>
    have := instDecidableDelayFree f
    have := instDecidableDelayFree a
    inferInstanceAs (Decidable (f.DelayFree ∧ a.DelayFree))
  | .rep e => instDecidableDelayFree e
  | .mk _ e => instDecidableDelayFree e
  | .delay _ _ => inferInstanceAs (Decidable False)
  | .sync _ _ _ => inferInstanceAs (Decidable False)
  | .fold f z l =>
    have := instDecidableDelayFree f
    have := instDecidableDelayFree z
    have := instDecidableDelayFree l
    inferInstanceAs (Decidable (f.DelayFree ∧ z.DelayFree ∧ l.DelayFree))

theorem Expr.instRefs_of_delayFree : ∀ {e : Expr}, e.DelayFree → e.instRefs = e.refs
  | .var _, _ | .boolLit _, _ | .natLit _, _ | .prim _, _ | .declRef _, _ => rfl
  | .lam _ b, h => Expr.instRefs_of_delayFree (e := b) h
  | .app f a, h => by simp [Expr.instRefs, Expr.refs, Expr.instRefs_of_delayFree h.1, Expr.instRefs_of_delayFree h.2]
  | .rep e, h => Expr.instRefs_of_delayFree (e := e) h
  | .mk _ e, h => Expr.instRefs_of_delayFree (e := e) h
  | .delay _ _, h => h.elim
  | .sync _ _ _, h => h.elim
  | .fold f z l, h => by
    simp [Expr.instRefs, Expr.refs, Expr.instRefs_of_delayFree h.1, Expr.instRefs_of_delayFree h.2.1,
      Expr.instRefs_of_delayFree h.2.2]

/-- A term that refers to no declaration: an ordinary program whose typing is
    independent of any environment. -/
def Expr.RefFree (e : Expr) : Prop := e.refs = []

instance (e : Expr) : Decidable e.RefFree := inferInstanceAs (Decidable (e.refs = []))

theorem Expr.RefFree.app_left {f a : Expr} (h : (Expr.app f a).RefFree) : f.RefFree :=
  (List.append_eq_nil_iff.mp h).1

theorem Expr.RefFree.app_right {f a : Expr} (h : (Expr.app f a).RefFree) : a.RefFree :=
  (List.append_eq_nil_iff.mp h).2

end BDL
