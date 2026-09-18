import BDL.Surface.Units

/-!
# Composer — typed holes and local bidirectional dimension inference (Phase 10)

The formal basis a structured Formula Composer needs, and nothing more:

* a **partial expression** with typed holes (`PExpr`) — arithmetic over
  known operands of known dimension; it is not executed;
* **bottom-up** dimension checking of the known parts (`check`);
* **top-down** propagation of an expected dimension into holes (`solve`),
  by the local rules of each operator in the `Dim` group:
  `add/sub`: both sides get the result; `mul`: the other side gets
  `r − d`; `div`: numerator `r + d`, denominator `d − r`;
* **candidate units** for a hole from its solved dimension (`candidates`),
  sound and complete relative to the registry.

`solve` is deterministic, local and one-pass: an operand with no known
side (two holes under one `mul`) is reported unsolved (`none`), not
searched for.  There is no unification and no symbolic algebra beyond the
group laws of `Dim`.  Soundness and completeness are proved for the whole
fragment: filling the holes as solved makes the expression check at the
expected dimension, and any filling that checks agrees with the solution.
-/

namespace BDL.Composer
open BDL BDL.Units

/-- Partial expressions: holes, known operands (a literal, a reference or a
    known equation result, by dimension), and the four operators. -/
inductive PExpr where
  | hole (id : Nat)
  | known (d : Dim)
  | add (a b : PExpr)
  | sub (a b : PExpr)
  | mul (a b : PExpr)
  | div (a b : PExpr)
  deriving DecidableEq, Repr

/-- Bottom-up: the dimension of a hole-free expression. -/
def check : PExpr → Option Dim
  | .hole _ => none
  | .known d => some d
  | .add a b | .sub a b =>
    match check a, check b with
    | some d₁, some d₂ => if d₁ = d₂ then some d₁ else none
    | _, _ => none
  | .mul a b =>
    match check a, check b with
    | some d₁, some d₂ => some (d₁.add d₂)
    | _, _ => none
  | .div a b =>
    match check a, check b with
    | some d₁, some d₂ => some (d₁.sub d₂)
    | _, _ => none

/-- Fill every hole with a known operand. -/
def fill (σ : Nat → Dim) : PExpr → PExpr
  | .hole i => .known (σ i)
  | .known d => .known d
  | .add a b => .add (fill σ a) (fill σ b)
  | .sub a b => .sub (fill σ a) (fill σ b)
  | .mul a b => .mul (fill σ a) (fill σ b)
  | .div a b => .div (fill σ a) (fill σ b)

/-- Top-down: the dimensions the holes must have for the expression to
    have dimension `r`.  `none` = inconsistent known part, or not locally
    determined. -/
def solve : PExpr → Dim → Option (List (Nat × Dim))
  | .hole i, r => some [(i, r)]
  | .known d, r => if d = r then some [] else none
  | .add a b, r | .sub a b, r =>
    match solve a r, solve b r with
    | some c₁, some c₂ => some (c₁ ++ c₂)
    | _, _ => none
  | .mul a b, r =>
    match check a, check b with
    | some d₁, _ => solve b (r.sub d₁)
    | none, some d₂ => solve a (r.sub d₂)
    | none, none => none
  | .div a b, r =>
    match check a, check b with
    | some d₁, _ => solve b (d₁.sub r)
    | none, some d₂ => solve a (r.add d₂)
    | none, none => none

/-- `σ` respects the constraints. -/
def Agrees (σ : Nat → Dim) (cs : List (Nat × Dim)) : Prop := ∀ p ∈ cs, σ p.1 = p.2

theorem Dim.add_sub_cancel' (a b : Dim) : a.add (b.sub a) = b := by
  rw [Dim.add_comm]; exact Dim.sub_add_cancel b a
theorem Dim.sub_sub_cancel (a b : Dim) : a.sub (a.sub b) = b := by
  cases a; cases b; simp only [Dim.sub, Dim.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega
theorem Dim.eq_sub_of_add_eq {a b r : Dim} (h : a.add b = r) : b = r.sub a := by
  rw [← h, Dim.add_sub_cancel_left]
theorem Dim.eq_sub_of_add_eq' {a b r : Dim} (h : a.add b = r) : a = r.sub b := by
  rw [← h, Dim.add_sub_cancel]
theorem Dim.eq_of_sub_eq {a b r : Dim} (h : a.sub b = r) : b = a.sub r := by
  rw [← h, Dim.sub_sub_cancel]
theorem Dim.eq_of_sub_eq' {a b r : Dim} (h : a.sub b = r) : a = r.add b := by
  rw [← h, Dim.sub_add_cancel]

/-- A known part keeps its dimension under any filling. -/
theorem check_fill (σ : Nat → Dim) : ∀ {e : PExpr} {d : Dim}, check e = some d → check (fill σ e) = some d
  | .hole _, _, h => by simp [check] at h
  | .known _, _, h => h
  | .add a b, d, h => by
    simp only [check] at h
    split at h
    · rename_i d₁ d₂ h₁ h₂
      simp only [check, fill, check_fill σ h₁, check_fill σ h₂]
      exact h
    · exact nomatch h
  | .sub a b, d, h => by
    simp only [check] at h
    split at h
    · rename_i d₁ d₂ h₁ h₂
      simp only [check, fill, check_fill σ h₁, check_fill σ h₂]
      exact h
    · exact nomatch h
  | .mul a b, d, h => by
    simp only [check] at h
    split at h
    · rename_i d₁ d₂ h₁ h₂
      simp only [check, fill, check_fill σ h₁, check_fill σ h₂]
      exact h
    · exact nomatch h
  | .div a b, d, h => by
    simp only [check] at h
    split at h
    · rename_i d₁ d₂ h₁ h₂
      simp only [check, fill, check_fill σ h₁, check_fill σ h₂]
      exact h
    · exact nomatch h

theorem Agrees.append_left {σ : Nat → Dim} {c₁ c₂ : List (Nat × Dim)} (h : Agrees σ (c₁ ++ c₂)) : Agrees σ c₁ :=
  fun p hp => h p (List.mem_append_left _ hp)
theorem Agrees.append_right {σ : Nat → Dim} {c₁ c₂ : List (Nat × Dim)} (h : Agrees σ (c₁ ++ c₂)) : Agrees σ c₂ :=
  fun p hp => h p (List.mem_append_right _ hp)

/-- **Soundness of local inference.**  If `solve e r` succeeds and the
    holes are filled as it says, the completed expression has dimension `r`. -/
theorem solve_sound : ∀ (e : PExpr) (r : Dim) {cs : List (Nat × Dim)} {σ : Nat → Dim},
    solve e r = some cs → Agrees σ cs → check (fill σ e) = some r
  | .hole i, r, cs, σ, h, hσ => by
    simp only [solve, Option.some.injEq] at h
    subst h
    simp [fill, check, hσ (i, r) List.mem_cons_self]
  | .known d, r, cs, σ, h, _ => by
    simp only [solve] at h
    split at h
    · rename_i hd; subst hd; rfl
    · exact nomatch h
  | .add a b, r, cs, σ, h, hσ => by
    simp only [solve] at h
    split at h
    · rename_i c₁ c₂ h₁ h₂
      cases h
      have ha := solve_sound a r h₁ hσ.append_left
      have hb := solve_sound b r h₂ hσ.append_right
      simp [check, fill, ha, hb]
    · exact nomatch h
  | .sub a b, r, cs, σ, h, hσ => by
    simp only [solve] at h
    split at h
    · rename_i c₁ c₂ h₁ h₂
      cases h
      have ha := solve_sound a r h₁ hσ.append_left
      have hb := solve_sound b r h₂ hσ.append_right
      simp [check, fill, ha, hb]
    · exact nomatch h
  | .mul a b, r, cs, σ, h, hσ => by
    simp only [solve] at h
    split at h
    · rename_i d₁ h₁
      have hb := solve_sound b (r.sub d₁) h hσ
      simp [check, fill, check_fill σ h₁, hb, Dim.add_sub_cancel']
    · rename_i d₂ _ h₂
      have ha := solve_sound a (r.sub d₂) h hσ
      simp [check, fill, check_fill σ h₂, ha, Dim.sub_add_cancel]
    · exact nomatch h
  | .div a b, r, cs, σ, h, hσ => by
    simp only [solve] at h
    split at h
    · rename_i d₁ h₁
      have hb := solve_sound b (d₁.sub r) h hσ
      simp [check, fill, check_fill σ h₁, hb, Dim.sub_sub_cancel]
    · rename_i d₂ _ h₂
      have ha := solve_sound a (r.add d₂) h hσ
      simp [check, fill, check_fill σ h₂, ha, Dim.add_sub_cancel]
    · exact nomatch h

/-- **Completeness (uniqueness) of local inference.**  Whenever `solve`
    succeeds, every filling that makes the expression check at `r` assigns
    the holes exactly as solved: a one-hole equation in the `Dim` group has
    one solution. -/
theorem solve_complete : ∀ (e : PExpr) (r : Dim) {cs : List (Nat × Dim)} {σ : Nat → Dim},
    solve e r = some cs → check (fill σ e) = some r → Agrees σ cs
  | .hole i, r, cs, σ, h, hc => by
    simp only [solve, Option.some.injEq] at h
    subst h
    simp only [fill, check, Option.some.injEq] at hc
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact hc
  | .known _, _, cs, σ, h, _ => by
    simp only [solve] at h
    split at h
    · cases h; intro p hp; simp at hp
    · exact nomatch h
  | .add a b, r, cs, σ, h, hc => by
    simp only [solve] at h
    split at h
    · rename_i c₁ c₂ h₁ h₂
      cases h
      simp only [fill, check] at hc
      split at hc
      · rename_i d₁ d₂ ha hb
        split at hc
        · rename_i hd
          subst hd
          cases hc
          intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact solve_complete a _ h₁ ha p hp
          · exact solve_complete b _ h₂ hb p hp
        · exact nomatch hc
      · exact nomatch hc
    · exact nomatch h
  | .sub a b, r, cs, σ, h, hc => by
    simp only [solve] at h
    split at h
    · rename_i c₁ c₂ h₁ h₂
      cases h
      simp only [fill, check] at hc
      split at hc
      · rename_i d₁ d₂ ha hb
        split at hc
        · rename_i hd
          subst hd
          cases hc
          intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact solve_complete a _ h₁ ha p hp
          · exact solve_complete b _ h₂ hb p hp
        · exact nomatch hc
      · exact nomatch hc
    · exact nomatch h
  | .mul a b, r, cs, σ, h, hc => by
    simp only [solve] at h
    split at h
    · rename_i d₁ h₁
      simp only [fill, check] at hc
      split at hc
      · rename_i d₁' d₂' ha hb
        rw [check_fill σ h₁] at ha
        cases ha
        cases hc
        exact solve_complete b _ h (by rw [hb, Dim.add_sub_cancel_left])
      · exact nomatch hc
    · rename_i d₂ _ h₂
      simp only [fill, check] at hc
      split at hc
      · rename_i d₁' d₂' ha hb
        rw [check_fill σ h₂] at hb
        cases hb
        cases hc
        exact solve_complete a _ h (by rw [ha, Dim.add_sub_cancel])
      · exact nomatch hc
    · exact nomatch h
  | .div a b, r, cs, σ, h, hc => by
    simp only [solve] at h
    split at h
    · rename_i d₁ h₁
      simp only [fill, check] at hc
      split at hc
      · rename_i d₁' d₂' ha hb
        rw [check_fill σ h₁] at ha
        cases ha
        cases hc
        exact solve_complete b _ h (by rw [hb, Dim.sub_sub_cancel])
      · exact nomatch hc
    · rename_i d₂ _ h₂
      simp only [fill, check] at hc
      split at hc
      · rename_i d₁' d₂' ha hb
        rw [check_fill σ h₂] at hb
        cases hb
        cases hc
        exact solve_complete a _ h (by rw [ha, Dim.sub_add_cancel])
      · exact nomatch hc
    · exact nomatch h

/-! ## Candidates for a hole -/

/-- The dimension solved for hole `i`, if determined. -/
def holeDim (e : PExpr) (r : Dim) (i : Nat) : Option Dim :=
  (solve e r).bind fun cs => (cs.find? (·.1 = i)).map (·.2)

/-- Candidate units for hole `i` of `e` at expected dimension `r`. -/
def candidates {K : Type} (reg : List (Unit K)) (e : PExpr) (r : Dim) (i : Nat) : List (Unit K) :=
  match holeDim e r i with
  | some d => unitsFor reg d
  | none => []

/-- **Candidate soundness**: every suggested unit has the hole's solved
    dimension, hence filling the hole with a literal in that unit yields an
    expression of the expected dimension (`solve_sound`). -/
theorem candidates_sound {K : Type} (reg : List (Unit K)) (e : PExpr) (r : Dim) (i : Nat) :
    ∀ u ∈ candidates reg e r i, holeDim e r i = some u.dim := by
  intro u hu
  unfold candidates at hu
  split at hu
  · rename_i d hd
    rw [hd, unitsFor_sound reg d u hu]
  · simp at hu

/-- **Candidate completeness** relative to the registry. -/
theorem candidates_complete {K : Type} (reg : List (Unit K)) (e : PExpr) (r : Dim) (i : Nat) (d : Dim)
    (hd : holeDim e r i = some d) : ∀ u ∈ reg, u.dim = d → u ∈ candidates reg e r i := by
  intro u hu hud
  unfold candidates
  rw [hd]
  exact unitsFor_complete reg d u hu hud

/-- Type-directed reference candidates: the declarations whose type is the
    quantity of the solved dimension. -/
def refCandidates (decls : List (DeclId × Ty)) (d : Dim) : List DeclId :=
  (decls.filter (·.2 = .q d)).map (·.1)

theorem refCandidates_sound (decls : List (DeclId × Ty)) (d : Dim) :
    ∀ x ∈ refCandidates decls d, ∃ p ∈ decls, p.1 = x ∧ p.2 = .q d := by
  intro x hx
  simp only [refCandidates, List.mem_map, List.mem_filter] at hx
  obtain ⟨p, ⟨hp, hty⟩, rfl⟩ := hx
  exact ⟨p, hp, rfl, of_decide_eq_true hty⟩

/-- What the editor may explain for a slot: its expected dimension and the
    candidate units — both derived, never authored. -/
structure Slot (K : Type) where
  expected : Dim
  units : List (Unit K)

def slot {K : Type} (reg : List (Unit K)) (e : PExpr) (r : Dim) (i : Nat) : Option (Slot K) :=
  (holeDim e r i).map fun d => ⟨d, unitsFor reg d⟩

theorem slot_sound {K : Type} (reg : List (Unit K)) (e : PExpr) (r : Dim) (i : Nat) {sl : Slot K}
    (h : slot reg e r i = some sl) : holeDim e r i = some sl.expected ∧ ∀ u ∈ sl.units, u.dim = sl.expected := by
  unfold slot at h
  cases hd : holeDim e r i with
  | none => rw [hd] at h; exact nomatch h
  | some d =>
    rw [hd] at h
    cases h
    exact ⟨rfl, unitsFor_sound reg d⟩

end BDL.Composer
