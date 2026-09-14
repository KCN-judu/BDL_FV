/-!
# Base — object language

A tiny simply typed language, extended (Phase 1) with references to design
declarations by *identity*: `Expr.declRef d`.  Nothing about a declaration's
interface or realization lives in the syntax; a reference is a name, resolved
against a `DeclEnv` (see `Decl.lean`) at typing time.
-/

namespace BDL

inductive Ty where
  | bool
  | nat
  | arr (dom cod : Ty)
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

/-- Typing context: the type of de Bruijn index `i` is `Γ[i]?`. -/
abbrev Ctx := List Ty

/-- The declarations a term refers to (with multiplicity; order irrelevant). -/
def Expr.refs : Expr → List DeclId
  | .var _ | .boolLit _ | .natLit _ => []
  | .lam _ b => b.refs
  | .app f a => f.refs ++ a.refs
  | .declRef d => [d]

/-- A term that refers to no declaration: an ordinary program whose typing is
    independent of any environment. -/
def Expr.RefFree (e : Expr) : Prop := e.refs = []

instance (e : Expr) : Decidable e.RefFree := inferInstanceAs (Decidable (e.refs = []))

theorem Expr.RefFree.app_left {f a : Expr} (h : (Expr.app f a).RefFree) : f.RefFree :=
  (List.append_eq_nil_iff.mp h).1

theorem Expr.RefFree.app_right {f a : Expr} (h : (Expr.app f a).RefFree) : a.RefFree :=
  (List.append_eq_nil_iff.mp h).2

end BDL
