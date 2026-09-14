/-!
# Base — object language

A tiny simply typed language, extended (Phase 1) with references to design
holes by *identity*: `Expr.holeRef h`.  Nothing about a hole's specification
or realization lives in the syntax; a reference is a name, resolved against a
`HoleEnv` (see `Hole.lean`) at typing time.
-/

namespace BDL

inductive Ty where
  | bool
  | nat
  | arr (dom cod : Ty)
  deriving DecidableEq, Repr

/-- Persistent identity of a design hole.  A wrapper rather than a bare `Nat`
    so ids cannot be confused with de Bruijn indices or numerals. -/
structure HoleId where
  n : Nat
  deriving DecidableEq, Repr

inductive Expr where
  | var (i : Nat)                 -- de Bruijn index
  | boolLit (b : Bool)
  | natLit (n : Nat)
  | lam (dom : Ty) (body : Expr)  -- binder annotated with its domain
  | app (f a : Expr)
  | holeRef (h : HoleId)          -- Phase 1: reference to a design entity by id
  deriving DecidableEq, Repr

/-- Typing context: the type of de Bruijn index `i` is `Γ[i]?`. -/
abbrev Ctx := List Ty

/-- The hole identifiers a term refers to (with multiplicity; order irrelevant). -/
def Expr.refs : Expr → List HoleId
  | .var _ | .boolLit _ | .natLit _ => []
  | .lam _ b => b.refs
  | .app f a => f.refs ++ a.refs
  | .holeRef h => [h]

/-- A term that mentions no hole: an ordinary closed-over-the-environment program. -/
def Expr.HoleFree (e : Expr) : Prop := e.refs = []

instance (e : Expr) : Decidable e.HoleFree := inferInstanceAs (Decidable (e.refs = []))

theorem Expr.HoleFree.app_left {f a : Expr} (h : (Expr.app f a).HoleFree) : f.HoleFree :=
  (List.append_eq_nil_iff.mp h).1

theorem Expr.HoleFree.app_right {f a : Expr} (h : (Expr.app f a).HoleFree) : a.HoleFree :=
  (List.append_eq_nil_iff.mp h).2

end BDL
