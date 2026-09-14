import PersistentHole.Spec

/-!
# Hole — persistent design holes

A design hole is a record with three *independent* components:

* `id`          — its persistent identity (a mere name);
* `spec`        — its current commitment (which grows over time);
* `realization` — an optional concrete term (which is supplied at most once).

Identity is a separate field precisely so that the refinement relation can
be *required* to preserve it (`HoleRefines` in `Refinement.lean`) rather than
merely be assumed to.  Note that a hole is not a syntactic position: nothing
in `DesignHole` mentions where (if anywhere) it occurs in a term.
-/

namespace PersistentHole

/-- Persistent identity of a design hole.  A wrapper rather than a bare
    `Nat` so that ids cannot be confused with de Bruijn indices or numerals. -/
structure HoleId where
  n : Nat
  deriving DecidableEq, Repr

structure DesignHole where
  id          : HoleId
  spec        : Spec
  realization : Option Expr
  deriving DecidableEq, Repr

/-- A freshly declared, unresolved hole. -/
def DesignHole.unresolved (id : HoleId) (S : Spec) : DesignHole :=
  ⟨id, S, none⟩

def DesignHole.IsRealized (h : DesignHole) : Prop := h.realization.isSome

/-- Well-formedness.  Every `Spec` is trivially valid in this model (there is
    no consistency condition on obligations), so an unresolved hole is always
    well formed; a realized hole is well formed when its term satisfies its
    *current* specification. -/
def WellFormedHole (ev : Evidence) (Γ : Ctx) (h : DesignHole) : Prop :=
  ∀ e, h.realization = some e → Satisfies ev Γ e h.spec

theorem WellFormedHole.unresolved (ev : Evidence) (Γ : Ctx) (id : HoleId) (S : Spec) :
    WellFormedHole ev Γ (.unresolved id S) :=
  fun _ h => nomatch h

theorem WellFormedHole.realized {ev : Evidence} {Γ : Ctx} {id : HoleId} {S : Spec} {e : Expr}
    (hs : Satisfies ev Γ e S) : WellFormedHole ev Γ ⟨id, S, some e⟩ :=
  fun _ h => Option.some.inj h ▸ hs

instance (ev : Evidence) [∀ e p, Decidable (ev e p)] (Γ : Ctx) (h : DesignHole) :
    Decidable (WellFormedHole ev Γ h) :=
  match hr : h.realization with
  | none => isTrue fun _ h' => by rw [hr] at h'; exact nomatch h'
  | some e =>
    if hs : Satisfies ev Γ e h.spec then
      isTrue fun _ h' => by rw [hr] at h'; exact Option.some.inj h' ▸ hs
    else
      isFalse fun wf => hs (wf e hr)

end PersistentHole
