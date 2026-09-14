/-!
# Base — object language

A tiny simply typed language, extended (Phase 1) with references to design
declarations by *identity*: `Expr.declRef d`.  Nothing about a declaration's
interface or realization lives in the syntax; a reference is a name, resolved
against a `DeclEnv` (see `Decl.lean`) at typing time.
-/

namespace BDL

/-- Stable identity of a semantic concept (Phase 2).  Distinct from `DeclId`:
    a concept is a *type*, a declaration is a *value*; conflating them admits
    category errors (see `Experiments.SemanticTypeAlternatives`, Model C).
    Display names are surface data and are not part of identity. -/
structure SemanticId where
  n : Nat
  deriving DecidableEq, Repr

/-- Physical dimension as an exponent vector over three base dimensions
    (Phase 3).  Enough to test the abstraction; not an SI catalogue. -/
structure Dim where
  length : Int
  time   : Int
  angle  : Int
  deriving DecidableEq, Repr

namespace Dim
def zero : Dim := ⟨0, 0, 0⟩
def add (a b : Dim) : Dim := ⟨a.length + b.length, a.time + b.time, a.angle + b.angle⟩
def sub (a b : Dim) : Dim := ⟨a.length - b.length, a.time - b.time, a.angle - b.angle⟩
def Length : Dim := ⟨1, 0, 0⟩
def Time   : Dim := ⟨0, 1, 0⟩
def Angle  : Dim := ⟨0, 0, 1⟩
end Dim

inductive Ty where
  | bool
  | nat
  | arr (dom cod : Ty)
  /-- Phase 2: a nominal semantic type.  Two distinct ids are distinct types
      regardless of any eventual representation.  Values of semantic type
      are observed with `Expr.rep` and constructed with `Expr.mk` — the latter
      only inside the realization of a declaration whose signature announces
      the type (`Ty.grant`). -/
  | sem (s : SemanticId)
  /-- Phase 3: a physical quantity of dimension `d`.  The representation type
      of physical concepts.  `nat` remains for counts. -/
  | q (d : Dim)
  deriving DecidableEq, Repr

/-- A type mentioning no semantic concept. -/
def Ty.SemFree : Ty → Prop
  | .sem _ => False
  | .arr a b => a.SemFree ∧ b.SemFree
  | _ => True

instance : ∀ τ : Ty, Decidable τ.SemFree
  | .bool => inferInstanceAs (Decidable True)
  | .nat => inferInstanceAs (Decidable True)
  | .q _ => inferInstanceAs (Decidable True)
  | .sem _ => inferInstanceAs (Decidable False)
  | .arr a b =>
    have := instDecidableSemFree a
    have := instDecidableSemFree b
    inferInstanceAs (Decidable (a.SemFree ∧ b.SemFree))

/-- Registered pure operators (the paper's `p(e₁,…,eₙ)`).  Dimension algebra
    lives entirely in their types; typing an application is ordinary STLC. -/
inductive Prim where
  | lit (d : Dim) (n : Nat)
  | add (d : Dim)
  | mul (d₁ d₂ : Dim)
  | div (d₁ d₂ : Dim)
  deriving DecidableEq, Repr

def Prim.ty : Prim → Ty
  | .lit d _ => .q d
  | .add d => .arr (.q d) (.arr (.q d) (.q d))
  | .mul d₁ d₂ => .arr (.q d₁) (.arr (.q d₂) (.q (d₁.add d₂)))
  | .div d₁ d₂ => .arr (.q d₁) (.arr (.q d₂) (.q (d₁.sub d₂)))

/-- Stable identity of a design declaration — an ordinary declaration name,
    not a novel abstraction (Phase 1, REPORT §1.5).  A wrapper rather than a
    bare `Nat` so ids cannot be confused with de Bruijn indices or numerals.
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
  | rep (e : Expr)                -- Phase 3: observe a semantic value's representation
  | mk (s : SemanticId) (e : Expr) -- Phase 3: construct a semantic value (granted only)
  | prim (p : Prim)               -- Phase 3: registered operator
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

/-- A term that refers to no declaration: an ordinary program whose typing is
    independent of any environment. -/
def Expr.RefFree (e : Expr) : Prop := e.refs = []

instance (e : Expr) : Decidable e.RefFree := inferInstanceAs (Decidable (e.refs = []))

theorem Expr.RefFree.app_left {f a : Expr} (h : (Expr.app f a).RefFree) : f.RefFree :=
  (List.append_eq_nil_iff.mp h).1

theorem Expr.RefFree.app_right {f a : Expr} (h : (Expr.app f a).RefFree) : a.RefFree :=
  (List.append_eq_nil_iff.mp h).2

end BDL
