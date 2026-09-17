import BDL.Core.Clock

/-!
# ListData — ordinary list data in the kernel (Phase 9a)

`Ty.list τ`, the values `Value.list`, and six registered operators
(`nil`, `cons`, `length`, `take`, `reverse`, `head`) were added to
`Base.lean` and `Reactive.lean`.  Nothing else changed: typing is the
ordinary application of `Prim.ty`; evaluation is `applyPrim`; the domain
judgment has no list rule; and every earlier theorem (`Ev.det`,
`reactive_total`, `MEv.det`, `multi_domain_total`, provenance, erasure)
holds unchanged because each is generic over primitives and data types.

This module records the list-specific corollaries by name.
-/

namespace BDL
open BDL.Reactive BDL.Clock

/-! ## A — lists are data -/

/-- Lists may be delayed and transported exactly when their elements may. -/
theorem list_data (τ : Ty) : (Ty.list τ).Data ↔ τ.Data := Ty.list_data τ

theorem list_semFree (τ : Ty) : (Ty.list τ).SemFree ↔ τ.SemFree := Ty.list_semFree τ

/-! ## B — value typing of the constructors and the eliminators -/

/-- `nil` inhabits `list τ`. -/
theorem list_nil_red {Θ : ConceptEnv} {A : App} (τ : Ty) : Red Θ A (.list τ) (Value.list []) :=
  ⟨[], rfl, fun _ h => by simp at h⟩

/-- `cons` of related values is related. -/
theorem list_cons_red {Θ : ConceptEnv} {A : App} {τ : Ty} {x : Value} {xs : List Value}
    (hx : Red Θ A τ x) (hxs : Red Θ A (.list τ) (Value.list xs)) : Red Θ A (.list τ) (Value.list (x :: xs)) := by
  obtain ⟨vs, hvs, hall⟩ := hxs
  have : vs = xs := (Value.list.inj hvs).symm
  subst this
  refine ⟨x :: vs, rfl, fun w hw => ?_⟩
  rcases List.mem_cons.mp hw with rfl | hw
  · exact hx
  · exact hall w hw

/-- Every list operator inhabits its type (the `Red_prim` cases). -/
theorem list_prims_red {Θ : ConceptEnv} {A : App} (hA : A.HasPrim) (τ : Ty) :
    Red Θ A (Prim.nil τ).ty (applyPrim (.nil τ) []) ∧ Red Θ A (Prim.cons τ).ty (applyPrim (.cons τ) []) ∧
    Red Θ A (Prim.length τ).ty (applyPrim (.length τ) []) ∧ Red Θ A (Prim.take τ).ty (applyPrim (.take τ) []) ∧
    Red Θ A (Prim.reverse τ).ty (applyPrim (.reverse τ) []) ∧ Red Θ A (Prim.head τ).ty (applyPrim (.head τ) []) :=
  ⟨Red_prim hA _, Red_prim hA _, Red_prim hA _, Red_prim hA _, Red_prim hA _, Red_prim hA _⟩

/-- The operators compute as expected on list values. -/
theorem list_compute (τ : Ty) (x : Value) (xs : List Value) (k : Nat) :
    Prim.compute (.nil τ) [] = .list [] ∧
    Prim.compute (.cons τ) [x, .list xs] = .list (x :: xs) ∧
    Prim.compute (.length τ) [.list xs] = .nat xs.length ∧
    Prim.compute (.take τ) [.nat k, .list xs] = .list (xs.take k) ∧
    Prim.compute (.reverse τ) [.list xs] = .list xs.reverse ∧
    Prim.compute (.head τ) [.list []] = .none ∧ Prim.compute (.head τ) [.list (x :: xs)] = .some x :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## C, D, E — determinism and totality are inherited -/

/-- **`list_eval_deterministic`**: `Ev.det` is unconditional and generic in
    values, so it covers lists. -/
theorem list_eval_deterministic {Δ : DeclEnv} {I : Input} {t : Nat} {ρ : List Value} {e : Expr} {v₁ v₂ : Value}
    (h₁ : Ev Δ I t ρ e v₁) (h₂ : Ev Δ I t ρ e v₂) : v₁ = v₂ := h₁.det h₂

theorem list_meval_deterministic {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat} {ρ : List Value}
    {e : Expr} {v₁ v₂ : Value} (h₁ : MEv S Δ I c t ρ e v₁) (h₂ : MEv S Δ I c t ρ e v₂) : v₁ = v₂ := h₁.det h₂

/-- **`reactive_total_with_lists`**: totality at a list type, an instance of
    `reactive_total` — the value is a list of related elements. -/
theorem reactive_total_with_lists {Θ : ConceptEnv} (hΘ : Θ.WF) {Δ : DeclEnv} (hc : Causal Δ) {I : Input}
    {ev : Evidence} (g : GlobalWF ev Θ Δ)
    (hI : ∀ d τ t, Δ.tyView d = some τ → Δ.realizationOf d = none → Red Θ (Apply Δ I t) τ (I d t))
    {d : DeclId} {τ : Ty} (htv : Δ.tyView d = some (.list τ)) (t : Nat) :
    ∃ vs, Ev Δ I t [] (.declRef d) (.list vs) ∧ ∀ w ∈ vs, Red Θ (Apply Δ I t) τ w := by
  obtain ⟨v, hv, hr⟩ := reactive_total hΘ hc g hI htv t
  obtain ⟨vs, rfl, hvs⟩ := hr
  exact ⟨vs, hv, hvs⟩

/-- **`multi_domain_total_with_lists`**: the multi-domain instance. -/
theorem multi_domain_total_with_lists {S : Sched} {Θ : ConceptEnv} (hΘ : Θ.WF) {Δ : DeclEnv} (hc : Causal Δ)
    {I : Input} {ev : Evidence} (g : GlobalWF ev Θ Δ)
    (hI : ∀ d τ c t, Δ.tyView d = some τ → Δ.realizationOf d = none → Red Θ (MApply S Δ I c t) τ (I d t))
    {d : DeclId} {τ : Ty} (htv : Δ.tyView d = some (.list τ)) (c : ClockId) (t : Nat) :
    ∃ vs, MEv S Δ I c t [] (.declRef d) (.list vs) ∧ ∀ w ∈ vs, Red Θ (MApply S Δ I c t) τ w := by
  obtain ⟨v, hv, hr⟩ := multi_domain_total hΘ hc g hI htv c t
  obtain ⟨vs, rfl, hvs⟩ := hr
  exact ⟨vs, hv, hvs⟩

/-! ## F — no new clock rule -/

/-- **`list_clock_conservative`**: wrapping a reference in a list constructor
    does not change whether it may be read in a domain.  The domain judgment
    has no rule for lists; `cons` and `nil` are clocked like any primitive. -/
theorem list_clock_conservative (Κ : ClockEnv) (c : Option ClockId) (τ : Ty) (d : DeclId) :
    Clocked Κ c (.app (.app (.prim (.cons τ)) (.declRef d)) (.prim (.nil τ))) ↔ Clocked Κ c (.declRef d) := by
  unfold Clocked
  cases c <;> simp [clockedB]

/-- In particular a direct cross-domain read stays rejected when listed. -/
theorem list_direct_wire_rejected (Κ : ClockEnv) {c c' : ClockId} (hne : c ≠ c') {d : DeclId} (τ : Ty)
    (hK : Κ d = some c') :
    ¬ Clocked Κ (some c) (.app (.app (.prim (.cons τ)) (.declRef d)) (.prim (.nil τ))) := by
  rw [list_clock_conservative]
  unfold Clocked
  simp [clockedB, hK, hne.symm]

end BDL
