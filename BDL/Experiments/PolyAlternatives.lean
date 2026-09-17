import BDL.Surface.Generic

/-!
# Phase 9b — polymorphism alternatives: what the kernel needs, and what it does not

The candidates of the brief (§3):

* **A** monomorphic STLC kernel — what BDL has, unchanged;
* **B** ad-hoc duplication per type — what the kernel *sees* after
  elaboration (`instances_are_monomorphic`);
* **C** rank-1 parametric polymorphism — realized as type-indexed families
  instantiated by matching (`Poly.lean`, `Stdlib.lean`): no type variable
  reaches the kernel;
* **D** explicit System F — a toy here, to measure what would be added:
  `Λ`/`[τ]` in terms and `∀` in types, and the rank the standard encodings
  need;
* **E** higher rank — rejected: every candidate use has rank ≥ 2 and a
  rank-1 replacement (`applyBoth_rank`, `applyBoth_replacement`).

Two encodings usually offered as reasons *not* to add products to a
kernel are measured: Church pairs need rank 2 to be first-class
(`church_fst_rank`) and are arrows, hence not data — they cannot be
delayed (`arrow_not_delayable`).  So paired *state* needs `prod` in the
kernel, which is why Phase 9b added it.
-/

namespace BDL.Experiments.Poly
open BDL BDL.Reactive BDL.Stdlib BDL.Poly

/-! ## §1 Model B is what Model C elaborates to -/

def Brightness : SemanticId := ⟨40⟩
def Opacity : SemanticId := ⟨41⟩
def Mode : SemanticId := ⟨42⟩

/-- Brightness and Opacity are ordered concepts; Mode is not.  All three are
    represented by `q 0`. -/
def O : OrdDecl := fun s => s = Brightness ∨ s = Opacity
def Θ : ConceptEnv := fun s => if s = Brightness ∨ s = Opacity ∨ s = Mode then some (.q Dim.zero) else none

/-- Three uses of `min` are three monomorphic kernel terms.  The scheme
    `∀α:Ord. α → α → α` exists only in the elaborator. -/
theorem instances_are_monomorphic :
    minF (.q Dim.Length) ≠ minF (.sem Brightness Dim.zero) ∧
    minF (.sem Brightness Dim.zero) ≠ minF (.sem Opacity Dim.zero) ∧
    (∀ Δ G Γ, HasType Θ Δ G Γ (minF (.sem Brightness Dim.zero))
      (.arr (.sem Brightness) (.arr (.sem Brightness) (.sem Brightness)))) := by
  refine ⟨by decide, by decide, fun _ _ _ => minF_typed _ (by simp [Ordered.WF, Θ, Brightness])⟩

/-- Use-site inference is matching: from the argument type the elaborator
    recovers the instance, uniquely; then the capability is checked. -/
def minScheme : Scheme := ⟨.arr (.tvar 0) (.arr (.tvar 0) (.tvar 0)), [(0, .ord)]⟩
def containsScheme : Scheme := ⟨.arr (.tvar 0) (.arr (.list (.tvar 0)) .bool), [(0, .eq)]⟩

theorem min_instantiation :
    (minScheme.instantiate O Θ (.arr (.sem Brightness) (.arr (.sem Brightness) (.sem Brightness)))).map (·.ty 0)
      = some (.sem Brightness) ∧
    -- Mode is data and has equality, but no order: `min` at Mode is rejected
    minScheme.instantiate O Θ (.arr (.sem Mode) (.arr (.sem Mode) (.sem Mode))) = none ∧
    (containsScheme.instantiate O Θ (.arr (.sem Mode) (.arr (.list (.sem Mode)) .bool))).map (·.ty 0) = some (.sem Mode) ∧
    -- a function-typed instance fails every capability
    minScheme.instantiate O Θ (.arr (.arr .bool .bool) (.arr (.arr .bool .bool) (.arr .bool .bool))) = none ∧
    -- a mixed use has no instance at all
    minScheme.instantiate O Θ (.arr (.sem Brightness) (.arr (.sem Opacity) (.sem Brightness))) = none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Dimension variables match the same way. -/
def sumScheme : Scheme := ⟨.arr (.list (.q (.dvar 0))) (.q (.dvar 0)), []⟩

theorem sum_instantiation :
    (sumScheme.instantiate O Θ (.arr (.list (.q Dim.Length)) (.q Dim.Length))).map (·.dim 0) = some Dim.Length ∧
    sumScheme.instantiate O Θ (.arr (.list (.q Dim.Length)) (.q Dim.Time)) = none := ⟨rfl, rfl⟩

/-! ## §2 A toy System F, to measure Model D -/

inductive FTy where
  | base
  | tvar (n : Nat)
  | arr (a b : FTy)
  | all (body : FTy)      -- ∀. body, de Bruijn
  deriving DecidableEq, Repr

/-- Rank: how deep a `∀` sits to the left of arrows (∀-free types have
    rank 0; a ∀ in argument position raises the rank by one). -/
def FTy.rank : FTy → Nat
  | .base | .tvar _ => 0
  | .arr a b => max (if a.rank = 0 then 0 else a.rank + 1) b.rank
  | .all body => max 1 body.rank

/-- Prenex (rank ≤ 1) types are the ones a scheme expresses. -/
def FTy.Prenex (τ : FTy) : Prop := τ.rank ≤ 1

/-- Church pair: `∀γ. (A → B → γ) → γ` (with `A`, `B` closed and `γ = tvar 0`). -/
def churchPair (A B : FTy) : FTy := .all (.arr (.arr A (.arr B (.tvar 0))) (.tvar 0))

/-- Its type has rank 1 — the *value* is prenex — but consuming it as an
    argument (`fst : Pair A B → A`) has rank 2. -/
theorem church_fst_rank (A B : FTy) (hA : A.rank = 0) (hB : B.rank = 0) :
    (churchPair A B).rank = 1 ∧ (FTy.arr (churchPair A B) A).rank = 2 := by
  simp [churchPair, FTy.rank, hA, hB]

/-- In the prenex fragment a Church pair must be instantiated at one
    result type before it is passed; `fst` needs `γ = A`, `snd` needs
    `γ = B`, and those are different monomorphic types when `A ≠ B`. -/
def churchInst (A B γ : FTy) : FTy := .arr (.arr A (.arr B γ)) γ

theorem church_pair_prenex_one_projection (A B : FTy) (h : A ≠ B) : churchInst A B A ≠ churchInst A B B := by
  intro e; simp [churchInst] at e; exact h e

/-- Existentials as `∀γ. (∀α. τ → γ) → γ` are rank 2 as well. -/
def existential (τ : FTy) : FTy := .all (.arr (.all (.arr τ (.tvar 0))) (.tvar 0))
theorem existential_rank (τ : FTy) (hτ : τ.rank = 0) : (existential τ).rank = 2 := by
  simp [existential, FTy.rank, hτ]

/-- The candidate higher-rank use: a function taking a polymorphic
    function.  Rank 2. -/
def applyBothTy (A B : FTy) : FTy := .arr (.all (.arr (.tvar 0) (.tvar 0))) (.arr (.arr A B) (.arr A B))
theorem applyBoth_rank (A B : FTy) (hA : A.rank = 0) (hB : B.rank = 0) : (applyBothTy A B).rank = 2 := by
  simp [applyBothTy, FTy.rank, hA, hB]

/-- Its rank-1 replacement in BDL: instantiate the generic function twice
    and pair the results — an ordinary well-typed kernel term. -/
theorem applyBoth_replacement {Θ : ConceptEnv} {Δ : DeclEnv} {G : Grant} {Γ : Ctx} (A B : Ty) (g : Ty → Expr)
    (hg : ∀ τ, HasType Θ Δ G Γ (g τ) (.arr τ τ)) {p : Expr} (hp : HasType Θ Δ G Γ p (.prod A B)) :
    HasType Θ Δ G Γ (pairE A B (.app (g A) (fstE A B p)) (.app (g B) (sndE A B p))) (.prod A B) :=
  .app (.app .prim (.app (hg A) (.app .prim hp))) (.app (hg B) (.app .prim hp))

/-! ## §3 Function encodings are not data -/

/-- **`arrow_not_delayable`**: no term of function type can be delayed or
    transported — so any function encoding of pairs (or options, or lists)
    cannot be state.  Products must be data, hence kernel. -/
theorem arrow_not_delayable {Θ : ConceptEnv} {Δ : DeclEnv} {G : Grant} (a b : Ty) (i e : Expr) :
    ¬ HasType Θ Δ G [] (.delay i e) (.arr a b) ∧ ∀ c, ¬ HasType Θ Δ G [] (.sync c i e) (.arr a b) := by
  refine ⟨fun h => ?_, fun c h => ?_⟩
  · cases h with | delay hd _ _ => exact hd
  · cases h with | sync hd _ _ => exact hd

/-- Paired state *is* delayable: `prod` of data is data. -/
theorem pair_state_delayable {Θ : ConceptEnv} {Δ : DeclEnv} {G : Grant} {a b : Ty} (ha : a.Data) (hb : b.Data)
    {i e : Expr} (hi : HasType Θ Δ G [] i (.prod a b)) (he : HasType Θ Δ G [] e (.prod a b)) :
    HasType Θ Δ G [] (.delay i e) (.prod a b) :=
  .delay ⟨ha, hb⟩ hi he

/-! ## §4 Constrained polymorphism: the closed vocabulary suffices

Model D (dictionary passing) collapses to ordinary function arguments: a
designer's custom order is an explicit comparator (`minByF`,
`minBy_recovers_min` in `Stdlib`), no class needed.  `eq` on a function
type is not writable at all; `lt` exists only on quantities. -/
theorem no_eq_on_functions : ¬ (Ty.arr .bool .bool).Data := fun h => h

end BDL.Experiments.Poly
