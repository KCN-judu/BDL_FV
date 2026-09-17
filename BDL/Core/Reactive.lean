import BDL.Core.Dependency

/-!
# Reactive — the single-domain reactive semantics (Phase 4)

Every declaration denotes a stream over one logical tick domain.  Unresolved
declarations are the *inputs* (`Input`); realized declarations are evaluated
at every tick from their bodies.  The single temporal primitive is

    delay init e        -- the value of `e` one tick ago; `init` at tick 0

`Ty` is unchanged: "signalness" lives in this judgment, not in the type.

Results

* `Ev.det`                       — evaluation is deterministic.
* `Ev.not_of_strictCyclic`       — a strict instantaneous cycle has no value.
* `fundamental`, `reactive_total`— causal + globally well formed + well-typed
                                    inputs ⇒ a value at every tick.
* `Ev.tag_provenance`, `temporal_state_preserves_semantic_identity`
                                 — state never manufactures a `SemanticId`.
* `unfolds_preserves_eval`       — on wiring designs, stepping the unfolded
                                    program equals stepping the references.
* `evalF` / `evalF_sound`        — an executable interpreter for examples.

Concrete designs, derived operators, and rejected alternatives live in
`Experiments/ReactiveAlternatives.lean`.
-/

namespace BDL.Reactive
open BDL

/-! ## §1 Values and evaluation -/

inductive Value where
  | bool (b : Bool)
  | nat (n : Nat)                 -- also every `q d`
  | sem (s : SemanticId) (v : Value)
  | none
  | some (v : Value)
  | clo (ρ : List Value) (body : Expr)
  | prim (p : Prim) (args : List Value)
  /-- Phase 9a: an ordinary list value (the cross-domain window). -/
  | list (vs : List Value)
  deriving Repr, Inhabited

/-- Projections used to state example results decidably (`Value` is a nested
    inductive, so `DecidableEq` is not derived). -/
def Value.toNat? : Value → Option Nat
  | .nat n => Option.some n
  | _ => Option.none

def Value.toBool? : Value → Option Bool
  | .bool b => Option.some b
  | _ => Option.none

def _root_.BDL.Prim.arity : Prim → Nat
  | .lit _ _ => 0 | .none _ => 0 | .nil _ => 0
  | .not | .isSome _ | .some _ | .length _ | .reverse _ | .head _ => 1
  | .add _ | .sub _ | .mul _ _ | .div _ _ | .lt _ | .eq _ | .and | .or | .getD _ | .cons _ | .take _ => 2
  | .ite _ => 3

/-- Saturated primitive evaluation.  Ill-shaped arguments (excluded by typing)
    default to `nat 0`. -/
def _root_.BDL.Prim.compute : Prim → List Value → Value
  | .lit _ n, _ => .nat n
  | .add _, [.nat a, .nat b] => .nat (a + b)
  | .sub _, [.nat a, .nat b] => .nat (a - b)
  | .mul _ _, [.nat a, .nat b] => .nat (a * b)
  | .div _ _, [.nat a, .nat b] => .nat (a / b)
  | .lt _, [.nat a, .nat b] => .bool (decide (a < b))
  | .eq _, [.nat a, .nat b] => .bool (decide (a = b))
  | .not, [.bool a] => .bool (!a)
  | .and, [.bool a, .bool b] => .bool (a && b)
  | .or, [.bool a, .bool b] => .bool (a || b)
  | .ite _, [.bool c, x, y] => if c then x else y
  | .none _, _ => .none
  | .some _, [x] => .some x
  | .isSome _, [.some _] => .bool true
  | .isSome _, [.none] => .bool false
  | .getD _, [.some x, _] => x
  | .getD _, [.none, d] => d
  | .nil _, _ => .list []
  | .cons _, [x, .list xs] => .list (x :: xs)
  | .length _, [.list xs] => .nat xs.length
  | .take _, [.nat k, .list xs] => .list (xs.take k)
  | .reverse _, [.list xs] => .list xs.reverse
  | .head _, [.list (x :: _)] => .some x
  | .head _, [.list []] => .none
  | _, _ => .nat 0

/-- Apply a primitive to one more argument: compute when saturated. -/
def applyPrim (p : Prim) (args : List Value) : Value :=
  if args.length = p.arity then p.compute args else .prim p args

/-- Input streams: a value for every (unresolved) declaration at every tick. -/
abbrev Input := DeclId → Nat → Value

/-- Big-step evaluation of `e` at tick `t` under environment `ρ`. -/
inductive Ev (Δ : DeclEnv) (I : Input) : Nat → List Value → Expr → Value → Prop where
  | var {t ρ i v} : ρ[i]? = some v → Ev Δ I t ρ (.var i) v
  | boolLit {t ρ b} : Ev Δ I t ρ (.boolLit b) (.bool b)
  | natLit {t ρ n} : Ev Δ I t ρ (.natLit n) (.nat n)
  | lam {t ρ dom body} : Ev Δ I t ρ (.lam dom body) (.clo ρ body)
  | appClo {t ρ f a ρ' body va v} :
      Ev Δ I t ρ f (.clo ρ' body) → Ev Δ I t ρ a va → Ev Δ I t (va :: ρ') body v →
      Ev Δ I t ρ (.app f a) v
  | appPrim {t ρ f a p args va} :
      Ev Δ I t ρ f (.prim p args) → Ev Δ I t ρ a va →
      Ev Δ I t ρ (.app f a) (applyPrim p (args ++ [va]))
  | refRealized {t ρ d b v} : Δ.realizationOf d = some b → Ev Δ I t [] b v → Ev Δ I t ρ (.declRef d) v
  | refInput {t ρ d} : Δ.realizationOf d = none → Ev Δ I t ρ (.declRef d) (I d t)
  | rep {t ρ e s w} : Ev Δ I t ρ e (.sem s w) → Ev Δ I t ρ (.rep e) w
  | mk {t ρ e s w} : Ev Δ I t ρ e w → Ev Δ I t ρ (.mk s e) (.sem s w)
  | prim {t ρ p} : Ev Δ I t ρ (.prim p) (applyPrim p [])
  | delayZero {ρ i e v} : Ev Δ I 0 ρ i v → Ev Δ I 0 ρ (.delay i e) v
  | delaySucc {t ρ i e v} : Ev Δ I t ρ e v → Ev Δ I (t + 1) ρ (.delay i e) v
  /-- In a single domain every clock is *the* clock, so a transport is a delay
      (this is what the Phase-5 embedding theorem makes precise). -/
  | syncZero {ρ c i e v} : Ev Δ I 0 ρ i v → Ev Δ I 0 ρ (.sync c i e) v
  | syncSucc {t ρ c i e v} : Ev Δ I t ρ e v → Ev Δ I (t + 1) ρ (.sync c i e) v

/-- **`reactive_step_deterministic`.**  Evaluation is a partial function:
    one tick, one environment, one term — at most one value.  No evaluation
    order is hidden anywhere (there are no side effects to order). -/
theorem Ev.det {Δ : DeclEnv} {I : Input} {t : Nat} {ρ : List Value} {e : Expr} {v₁ v₂ : Value}
    (h₁ : Ev Δ I t ρ e v₁) (h₂ : Ev Δ I t ρ e v₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | var h => cases h₂ with | var h' => rw [h] at h'; exact Option.some.inj h'
  | boolLit => cases h₂; rfl
  | natLit => cases h₂; rfl
  | lam => cases h₂; rfl
  | appClo _ _ _ ihf iha ihb =>
    cases h₂ with
    | appClo hf' ha' hb' =>
      cases ihf hf'; cases iha ha'; exact ihb hb'
    | appPrim hf' _ => cases ihf hf'
  | appPrim _ _ ihf iha =>
    cases h₂ with
    | appClo hf' _ _ => cases ihf hf'
    | appPrim hf' ha' => cases ihf hf'; cases iha ha'; rfl
  | refRealized hs _ ih =>
    cases h₂ with
    | refRealized hs' hb' => rw [hs] at hs'; cases hs'; exact ih hb'
    | refInput hn => rw [hs] at hn; exact nomatch hn
  | refInput hn =>
    cases h₂ with
    | refRealized hs' _ => rw [hn] at hs'; exact nomatch hs'
    | refInput _ => rfl
  | rep _ ih => cases h₂ with | rep h' => cases ih h'; rfl
  | mk _ ih => cases h₂ with | mk h' => cases ih h'; rfl
  | prim => cases h₂; rfl
  | delayZero _ ih => cases h₂ with | delayZero h' => exact ih h'
  | delaySucc _ ih => cases h₂ with | delaySucc h' => exact ih h'
  | syncZero _ ih => cases h₂ with | syncZero h' => exact ih h'
  | syncSucc _ ih => cases h₂ with | syncSucc h' => exact ih h'

/-! ### An executable interpreter, sound for `Ev`

Fuel-bounded; `some v` implies an `Ev` derivation.  Used to check the
examples of §5 by `decide`. -/

def evalF (Δ : DeclEnv) (I : Input) : Nat → Nat → List Value → Expr → Option Value
  | 0, _, _, _ => Option.none
  | fuel + 1, t, ρ, e =>
    match e with
    | .var i => ρ[i]?
    | .boolLit b => Option.some (.bool b)
    | .natLit n => Option.some (.nat n)
    | .lam _ body => Option.some (.clo ρ body)
    | .app f a =>
      (evalF Δ I fuel t ρ f).bind fun vf =>
      (evalF Δ I fuel t ρ a).bind fun va =>
      match vf with
      | .clo ρ' body => evalF Δ I fuel t (va :: ρ') body
      | .prim p args => Option.some (applyPrim p (args ++ [va]))
      | _ => Option.none
    | .declRef d =>
      match Δ.realizationOf d with
      | Option.some b => evalF Δ I fuel t [] b
      | Option.none => Option.some (I d t)
    | .rep e =>
      (evalF Δ I fuel t ρ e).bind fun ve =>
      match ve with
      | .sem _ w => Option.some w
      | _ => Option.none
    | .mk s e => (evalF Δ I fuel t ρ e).map (.sem s)
    | .prim p => Option.some (applyPrim p [])
    | .delay i e =>
      match t with
      | 0 => evalF Δ I fuel 0 ρ i
      | t' + 1 => evalF Δ I fuel t' ρ e
    | .sync _ i e =>
      match t with
      | 0 => evalF Δ I fuel 0 ρ i
      | t' + 1 => evalF Δ I fuel t' ρ e

theorem evalF_sound {Δ : DeclEnv} {I : Input} :
    ∀ {fuel t : Nat} {ρ : List Value} {e : Expr} {v : Value},
      evalF Δ I fuel t ρ e = Option.some v → Ev Δ I t ρ e v
  | 0, _, _, _, _, h => by simp [evalF] at h
  | fuel + 1, t, ρ, e, v, h => by
    cases e with
    | var i => exact .var h
    | boolLit b => exact (Option.some.inj h) ▸ Ev.boolLit
    | natLit n => exact (Option.some.inj h) ▸ Ev.natLit
    | lam dom body => exact (Option.some.inj h) ▸ Ev.lam
    | prim p => exact (Option.some.inj h) ▸ Ev.prim
    | app f a =>
      simp only [evalF, Option.bind_eq_some_iff] at h
      obtain ⟨vf, hf, va, ha, hm⟩ := h
      cases vf with
      | clo ρ' body => exact .appClo (evalF_sound hf) (evalF_sound ha) (evalF_sound hm)
      | prim p args =>
        simp only [Option.some.injEq] at hm
        subst hm
        exact .appPrim (evalF_sound hf) (evalF_sound ha)
      | bool _ | nat _ | sem _ _ | none | some _ | list _ => simp at hm
    | declRef d =>
      simp only [evalF] at h
      cases hr : Δ.realizationOf d with
      | none => rw [hr] at h; exact (Option.some.inj h) ▸ Ev.refInput hr
      | some b => rw [hr] at h; exact .refRealized hr (evalF_sound h)
    | rep e =>
      simp only [evalF, Option.bind_eq_some_iff] at h
      obtain ⟨ve, he, hm⟩ := h
      cases ve with
      | sem s w => simp only [Option.some.injEq] at hm; subst hm; exact .rep (evalF_sound he)
      | bool _ | nat _ | none | some _ | clo _ _ | prim _ _ | list _ => simp at hm
    | mk s e =>
      simp only [evalF, Option.map_eq_some_iff] at h
      obtain ⟨w, hw, rfl⟩ := h
      exact .mk (evalF_sound hw)
    | delay i e =>
      cases t with
      | zero => exact .delayZero (evalF_sound h)
      | succ t' => exact .delaySucc (evalF_sound h)
    | sync c i e =>
      cases t with
      | zero => exact .syncZero (evalF_sound h)
      | succ t' => exact .syncSucc (evalF_sound h)

/-- Decidable evaluation for concrete examples: `evalF … = some v` gives `Ev`. -/
theorem Ev.of_evalF {Δ : DeclEnv} {I : Input} {fuel t : Nat} {ρ : List Value} {e : Expr} {v : Value}
    (h : evalF Δ I fuel t ρ e = Option.some v) : Ev Δ I t ρ e v := evalF_sound h

/-- A dimensioned literal evaluates to its number. -/
theorem Ev.lit {Δ : DeclEnv} {I : Input} {t : Nat} {ρ : List Value} (d : Dim) (n : Nat) :
    Ev Δ I t ρ (.prim (.lit d n)) (.nat n) :=
  have h := @Ev.prim Δ I t ρ (.lit d n)
  by simpa [applyPrim, Prim.arity, Prim.compute] using h


/-! ## Strict cycles have no value -/

/-- References that are *necessarily* evaluated at the current tick when the
    term is: not under a lambda (a closure body waits for application) and not
    inside a `delay` at all (its operand is read at the previous tick, its
    initial value only at tick 0).  Strictly smaller than `instRefs`, which
    is the conservative set used by `Causal`. -/
def _root_.BDL.Expr.strictRefs : Expr → List DeclId
  | .app f a => f.strictRefs ++ a.strictRefs
  | .declRef d => [d]
  | .rep e => e.strictRefs
  | .mk _ e => e.strictRefs
  | _ => []

def strictDependsOn (Δ : DeclEnv) (a b : DeclId) : Bool :=
  match Δ.realizationOf a with
  | some e => decide (b ∈ e.strictRefs)
  | none => false

def StrictDependsOn (Δ : DeclEnv) (a b : DeclId) : Prop := strictDependsOn Δ a b = true

instance (Δ : DeclEnv) (a b : DeclId) : Decidable (StrictDependsOn Δ a b) :=
  inferInstanceAs (Decidable (strictDependsOn Δ a b = true))

theorem StrictDependsOn.iff {Δ : DeclEnv} {a b : DeclId} :
    StrictDependsOn Δ a b ↔ ∃ e, Δ.realizationOf a = some e ∧ b ∈ e.strictRefs := by
  unfold StrictDependsOn strictDependsOn
  cases h : Δ.realizationOf a with
  | none => simp
  | some e => simp

/-- Strict reachability (transitive closure of `StrictDependsOn`). -/
def StrictReaches (Δ : DeclEnv) (a b : DeclId) : Prop :=
  ∃ c, StrictDependsOn Δ a c ∧ Star (StrictDependsOn Δ) c b

theorem StrictReaches.star_left {Δ : DeclEnv} {a b c : DeclId}
    (h : Star (StrictDependsOn Δ) a b) (r : StrictReaches Δ b c) : StrictReaches Δ a c := by
  induction h with
  | refl _ => exact r
  | step hab _ ih =>
    obtain ⟨d, hd, hs⟩ := ih r
    exact ⟨_, hab, .step hd hs⟩

/-- Any term that evaluates refers *strictly* only to declarations that are
    not on a strict cycle. -/
theorem Ev.strictRefs_not_cyclic {Δ : DeclEnv} {I : Input} {t : Nat} {ρ : List Value} {e : Expr} {v : Value}
    (h : Ev Δ I t ρ e v) : ∀ x ∈ e.strictRefs, ¬ StrictReaches Δ x x := by
  induction h with
  | var _ | boolLit | natLit | prim | lam => intro x hx; simp [Expr.strictRefs] at hx
  | appClo _ _ _ ihf iha _ =>
    intro x hx
    simp only [Expr.strictRefs, List.mem_append] at hx
    exact hx.elim (ihf x) (iha x)
  | appPrim _ _ ihf iha =>
    intro x hx
    simp only [Expr.strictRefs, List.mem_append] at hx
    exact hx.elim (ihf x) (iha x)
  | refRealized hs _ ih =>
    intro x hx hr
    simp [Expr.strictRefs] at hx; subst hx
    obtain ⟨c, hc, hcx⟩ := hr
    obtain ⟨e₀, he₀, hcmem⟩ := StrictDependsOn.iff.mp hc
    rw [hs] at he₀; cases he₀
    exact ih c hcmem (StrictReaches.star_left hcx ⟨c, hc, .refl c⟩)
  | refInput hn =>
    intro x hx hr
    simp [Expr.strictRefs] at hx; subst hx
    obtain ⟨c, hc, _⟩ := hr
    obtain ⟨_, he, _⟩ := StrictDependsOn.iff.mp hc
    rw [hn] at he; exact nomatch he
  | rep _ ih => exact ih
  | mk _ ih => exact ih
  | delayZero _ _ => intro x hx; simp [Expr.strictRefs] at hx
  | delaySucc _ _ => intro x hx; simp [Expr.strictRefs] at hx
  | syncZero _ _ => intro x hx; simp [Expr.strictRefs] at hx
  | syncSucc _ _ => intro x hx; simp [Expr.strictRefs] at hx

/-- **`instantaneous_cycle_rejected`.**  A declaration on an instantaneous
    cycle has no value at any tick — not "some default", not "one of several":
    no derivation exists. -/
theorem Ev.not_of_strictCyclic {Δ : DeclEnv} {I : Input} {a : DeclId} (hc : StrictReaches Δ a a)
    (t : Nat) (ρ : List Value) : ¬ ∃ v, Ev Δ I t ρ (.declRef a) v := by
  rintro ⟨v, h⟩
  exact h.strictRefs_not_cyclic a (by simp [Expr.strictRefs]) hc

/-- Strict cycles are instantaneous cycles (so `Causal` rejects them too). -/
theorem StrictDependsOn.toInst {Δ : DeclEnv} {a b : DeclId} (h : StrictDependsOn Δ a b) : InstDependsOn Δ a b := by
  obtain ⟨e, he, hb⟩ := StrictDependsOn.iff.mp h
  exact InstDependsOn.iff.mpr ⟨e, he, sub hb⟩
where
  sub {e : Expr} {b : DeclId} : b ∈ e.strictRefs → b ∈ e.instRefs := by
    induction e with
    | var _ | boolLit _ | natLit _ | prim _ | declRef _ | lam _ _ _ | delay _ _ _ _ | sync _ _ _ _ _ =>
      intro h; simp [Expr.strictRefs, Expr.instRefs] at h ⊢; try exact h
    | app f a ihf iha =>
      intro h
      simp only [Expr.strictRefs, Expr.instRefs, List.mem_append] at h ⊢
      exact h.elim (fun h => .inl (ihf h)) (fun h => .inr (iha h))
    | rep e ih => exact ih
    | mk _ e ih => exact ih

/-! ## §3 Totality — causal designs have a value at every tick

Proved with a logical relation `Red` indexed by the tick.  The induction is
lexicographic on (tick, instantaneous rank, typing derivation): a delayed
operand is evaluated at the previous tick under any rank; an instantaneous
reference is evaluated at the same tick under a smaller rank. -/

/-- Application of a function value to an argument at tick `t`. -/
def Apply (Δ : DeclEnv) (I : Input) (t : Nat) (vf w v : Value) : Prop :=
  (∃ ρ' body, vf = .clo ρ' body ∧ Ev Δ I t (w :: ρ') body v) ∨
  (∃ p args, vf = .prim p args ∧ v = applyPrim p (args ++ [w]))

theorem Ev.app_of_apply {Δ : DeclEnv} {I : Input} {t : Nat} {ρ : List Value} {f a : Expr} {vf w v : Value}
    (hf : Ev Δ I t ρ f vf) (ha : Ev Δ I t ρ a w) (hap : Apply Δ I t vf w v) : Ev Δ I t ρ (.app f a) v := by
  rcases hap with ⟨ρ', body, rfl, hb⟩ | ⟨p, args, rfl, rfl⟩
  · exact .appClo hf ha hb
  · exact .appPrim hf ha

/-- An application relation at one evaluation point: how a function value
    applied to an argument yields a result.  `Red` is generic in it so that
    the single-domain (`Apply`) and multi-domain (Phase 5) semantics share
    one logical relation. -/
abbrev App := Value → Value → Value → Prop

/-- Logical relation at sem-free types. -/
def RedSF (A : App) : Ty → Value → Prop
  | .bool, v => ∃ b, v = .bool b
  | .nat, v => ∃ n, v = .nat n
  | .q _, v => ∃ n, v = .nat n
  | .opt τ, v => v = .none ∨ ∃ w, v = .some w ∧ RedSF A τ w
  | .list τ, v => ∃ vs, v = .list vs ∧ ∀ w ∈ vs, RedSF A τ w
  | .arr a b, v => ∀ w, RedSF A a w → ∃ v', A v w v' ∧ RedSF A b v'
  | .sem _, _ => False

/-- Logical relation.  A semantic value is a tagged representation value. -/
def Red (Θ : ConceptEnv) (A : App) : Ty → Value → Prop
  | .bool, v => ∃ b, v = .bool b
  | .nat, v => ∃ n, v = .nat n
  | .q _, v => ∃ n, v = .nat n
  | .opt τ, v => v = .none ∨ ∃ w, v = .some w ∧ Red Θ A τ w
  | .list τ, v => ∃ vs, v = .list vs ∧ ∀ w ∈ vs, Red Θ A τ w
  | .arr a b, v => ∀ w, Red Θ A a w → ∃ v', A v w v' ∧ Red Θ A b v'
  | .sem s, v => ∃ w, v = .sem s w ∧ ∀ R, Θ s = some R → RedSF A R w

theorem Red_semFree {Θ : ConceptEnv} {A : App} :
    ∀ {τ : Ty}, τ.SemFree → ∀ {v : Value}, (Red Θ A τ v ↔ RedSF A τ v)
  | .bool, _, _ => Iff.rfl
  | .nat, _, _ => Iff.rfl
  | .q _, _, _ => Iff.rfl
  | .sem _, h, _ => h.elim
  | .opt τ, h, v => by
    simp only [Red, RedSF]
    constructor
    · rintro (rfl | ⟨w, rfl, hw⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨w, rfl, (Red_semFree (τ := τ) h).mp hw⟩
    · rintro (rfl | ⟨w, rfl, hw⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨w, rfl, (Red_semFree (τ := τ) h).mpr hw⟩
  | .list τ, h, v => by
    simp only [Red, RedSF]
    constructor
    · rintro ⟨vs, rfl, hvs⟩
      exact ⟨vs, rfl, fun w hw => (Red_semFree (τ := τ) h).mp (hvs w hw)⟩
    · rintro ⟨vs, rfl, hvs⟩
      exact ⟨vs, rfl, fun w hw => (Red_semFree (τ := τ) h).mpr (hvs w hw)⟩
  | .arr a b, h, v => by
    simp only [Red, RedSF]
    constructor
    · intro hv w hw
      obtain ⟨v', hap, hv'⟩ := hv w ((Red_semFree h.1).mpr hw)
      exact ⟨v', hap, (Red_semFree h.2).mp hv'⟩
    · intro hv w hw
      obtain ⟨v', hap, hv'⟩ := hv w ((Red_semFree h.1).mp hw)
      exact ⟨v', hap, (Red_semFree h.2).mpr hv'⟩

/-- At data types the relation does not depend on the application relation
    (no closures): values can be moved between evaluation points. -/
theorem RedSF_data {A A' : App} :
    ∀ {τ : Ty}, τ.Data → ∀ {v : Value}, RedSF A τ v → RedSF A' τ v
  | .bool, _, _, h => h
  | .nat, _, _, h => h
  | .q _, _, _, h => h
  | .sem _, _, _, h => h.elim
  | .arr _ _, h, _, _ => h.elim
  | .opt τ, hd, v, h => by
    simp only [RedSF] at h ⊢
    rcases h with rfl | ⟨w, rfl, hw⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨w, rfl, RedSF_data (τ := τ) hd hw⟩
  | .list τ, hd, v, h => by
    simp only [RedSF] at h ⊢
    obtain ⟨vs, rfl, hvs⟩ := h
    exact ⟨vs, rfl, fun w hw => RedSF_data (τ := τ) hd (hvs w hw)⟩

theorem Red_data {Θ : ConceptEnv} (hΘ : Θ.WF) {A A' : App} :
    ∀ {τ : Ty}, τ.Data → ∀ {v : Value}, Red Θ A τ v → Red Θ A' τ v
  | .bool, _, _, h => h
  | .nat, _, _, h => h
  | .q _, _, _, h => h
  | .arr _ _, h, _, _ => h.elim
  | .sem s, _, v, h => by
    obtain ⟨w, rfl, hw⟩ := h
    exact ⟨w, rfl, fun R hR => RedSF_data (hΘ s R hR).2 (hw R hR)⟩
  | .opt τ, hd, v, h => by
    simp only [Red] at h ⊢
    rcases h with rfl | ⟨w, rfl, hw⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨w, rfl, Red_data (τ := τ) hΘ hd hw⟩
  | .list τ, hd, v, h => by
    simp only [Red] at h ⊢
    obtain ⟨vs, rfl, hvs⟩ := h
    exact ⟨vs, rfl, fun w hw => Red_data (τ := τ) hΘ hd (hvs w hw)⟩

/-- Environments related pointwise. -/
def RedEnv (Θ : ConceptEnv) (A : App) (Γ : Ctx) (ρ : List Value) : Prop :=
  ∀ (i : Nat) (τ : Ty), Γ[i]? = some τ → ∃ v, ρ[i]? = some v ∧ Red Θ A τ v

theorem RedEnv.nil {Θ : ConceptEnv} {A : App} (ρ : List Value) : RedEnv Θ A [] ρ :=
  fun _ _ h => absurd h (by simp)

theorem RedEnv.cons {Θ : ConceptEnv} {A : App} {Γ : Ctx} {ρ : List Value}
    {τ : Ty} {w : Value} (hw : Red Θ A τ w) (hρ : RedEnv Θ A Γ ρ) :
    RedEnv Θ A (τ :: Γ) (w :: ρ) := by
  intro i τ' h
  cases i with
  | zero => rw [List.getElem?_cons_zero] at h; exact ⟨w, rfl, (Option.some.inj h) ▸ hw⟩
  | succ i => rw [List.getElem?_cons_succ] at h; exact hρ i τ' h

/-- An application relation that at least applies primitives. -/
def App.HasPrim (A : App) : Prop := ∀ p args w, A (.prim p args) w (applyPrim p (args ++ [w]))

theorem Apply.hasPrim (Δ : DeclEnv) (I : Input) (t : Nat) : App.HasPrim (Apply Δ I t) :=
  fun p args _ => Or.inr ⟨p, args, rfl, rfl⟩

/-- Every registered operator inhabits its type. -/
theorem Red_prim {Θ : ConceptEnv} {A : App} (hA : A.HasPrim) (p : Prim) :
    Red Θ A p.ty (applyPrim p []) := by
  cases p with
  | lit d n => exact ⟨n, by simp [applyPrim, Prim.arity, Prim.compute]⟩
  | add d | sub d | mul _ _ | div _ _ =>
    simp only [Prim.ty, Red, applyPrim, Prim.arity]
    rintro _ ⟨a, rfl⟩
    refine ⟨_, hA _ _ _, ?_⟩
    simp only [applyPrim, Prim.arity]
    rintro _ ⟨b, rfl⟩
    refine ⟨_, hA _ _ _, ?_⟩
    simp [applyPrim, Prim.arity, Prim.compute]
  | lt d | eq d =>
    simp only [Prim.ty, Red, applyPrim, Prim.arity]
    rintro _ ⟨a, rfl⟩
    refine ⟨_, hA _ _ _, ?_⟩
    simp only [applyPrim, Prim.arity]
    rintro _ ⟨b, rfl⟩
    refine ⟨_, hA _ _ _, ?_⟩
    simp [applyPrim, Prim.arity, Prim.compute]
  | not =>
    simp only [Prim.ty, Red, applyPrim, Prim.arity]
    rintro _ ⟨a, rfl⟩
    refine ⟨_, hA _ _ _, ?_⟩
    simp [applyPrim, Prim.arity, Prim.compute]
  | and | or =>
    simp only [Prim.ty, Red, applyPrim, Prim.arity]
    rintro _ ⟨a, rfl⟩
    refine ⟨_, hA _ _ _, ?_⟩
    simp only [applyPrim, Prim.arity]
    rintro _ ⟨b, rfl⟩
    refine ⟨_, hA _ _ _, ?_⟩
    simp [applyPrim, Prim.arity, Prim.compute]
  | ite τ =>
    simp only [Prim.ty, Red, applyPrim, Prim.arity]
    rintro _ ⟨c, rfl⟩
    refine ⟨_, hA _ _ _, ?_⟩
    simp only [applyPrim, Prim.arity]
    intro x hx
    refine ⟨_, hA _ _ _, ?_⟩
    simp only [applyPrim, Prim.arity]
    intro y hy
    refine ⟨_, hA _ _ _, ?_⟩
    simp only [applyPrim, Prim.arity, List.length_cons, List.length_nil, Prim.compute,
      List.nil_append, List.cons_append]
    cases c <;> simpa
  | none τ => simp [Prim.ty, Red, applyPrim, Prim.arity, Prim.compute]
  | some τ =>
    simp only [Prim.ty, Red, applyPrim, Prim.arity]
    intro x hx
    exact ⟨_, hA _ _ _, Or.inr ⟨x, by simp [applyPrim, Prim.arity, Prim.compute], hx⟩⟩
  | isSome τ =>
    simp only [Prim.ty, Red, applyPrim, Prim.arity]
    intro o ho
    refine ⟨_, hA _ _ _, ?_⟩
    rcases ho with rfl | ⟨w, rfl, _⟩ <;> simp [applyPrim, Prim.arity, Prim.compute]
  | getD τ =>
    simp only [Prim.ty, Red, applyPrim, Prim.arity]
    intro o ho
    refine ⟨_, hA _ _ _, ?_⟩
    simp only [applyPrim, Prim.arity]
    intro d hd
    refine ⟨_, hA _ _ _, ?_⟩
    rcases ho with rfl | ⟨w, rfl, hw⟩
    · simpa [applyPrim, Prim.arity, Prim.compute] using hd
    · simpa [applyPrim, Prim.arity, Prim.compute] using hw
  | nil τ => exact ⟨[], by simp [applyPrim, Prim.arity, Prim.compute], fun _ h => by simp at h⟩
  | cons τ =>
    simp only [Prim.ty, Red, applyPrim, Prim.arity]
    intro x hx
    refine ⟨_, hA _ _ _, ?_⟩
    simp only [applyPrim, Prim.arity]
    rintro _ ⟨vs, rfl, hvs⟩
    refine ⟨_, hA _ _ _, ?_⟩
    refine ⟨x :: vs, by simp [applyPrim, Prim.arity, Prim.compute], ?_⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hx
    · exact hvs w hw
  | length τ =>
    simp only [Prim.ty, Red, applyPrim, Prim.arity]
    rintro _ ⟨vs, rfl, -⟩
    exact ⟨_, hA _ _ _, vs.length, by simp [applyPrim, Prim.arity, Prim.compute]⟩
  | take τ =>
    simp only [Prim.ty, Red, applyPrim, Prim.arity]
    rintro _ ⟨k, rfl⟩
    refine ⟨_, hA _ _ _, ?_⟩
    simp only [applyPrim, Prim.arity]
    rintro _ ⟨vs, rfl, hvs⟩
    refine ⟨_, hA _ _ _, vs.take k, by simp [applyPrim, Prim.arity, Prim.compute], ?_⟩
    intro w hw
    exact hvs w (List.mem_of_mem_take hw)
  | reverse τ =>
    simp only [Prim.ty, Red, applyPrim, Prim.arity]
    rintro _ ⟨vs, rfl, hvs⟩
    refine ⟨_, hA _ _ _, vs.reverse, by simp [applyPrim, Prim.arity, Prim.compute], ?_⟩
    intro w hw
    exact hvs w (List.mem_reverse.mp hw)
  | head τ =>
    simp only [Prim.ty, Red, applyPrim, Prim.arity]
    rintro _ ⟨vs, rfl, hvs⟩
    refine ⟨_, hA _ _ _, ?_⟩
    cases vs with
    | nil => exact Or.inl (by simp [applyPrim, Prim.arity, Prim.compute])
    | cons x xs => exact Or.inr ⟨x, by simp [applyPrim, Prim.arity, Prim.compute], hvs x (List.mem_cons_self)⟩

/-- **Fundamental theorem.**  In a causal, globally well-formed design with
    well-typed inputs, every well-typed term whose instantaneous references
    have rank below `r` evaluates at every tick to a related value. -/
theorem fundamental {Θ : ConceptEnv} (hΘ : Θ.WF) {Δ : DeclEnv} {I : Input}
    {rank : DeclId → Nat} {R : Nat} (hR : ∀ d, rank d < R)
    (hc : ∀ a b, InstDependsOn Δ a b → rank b < rank a)
    {ev : Evidence} (g : GlobalWF ev Θ Δ)
    (hI : ∀ d τ t, Δ.tyView d = some τ → Δ.realizationOf d = none → Red Θ (Apply Δ I t) τ (I d t)) :
    ∀ t r {G : Grant} {Γ : Ctx} {e : Expr} {τ : Ty}, HasType Θ Δ G Γ e τ →
      ∀ ρ, (∀ x ∈ e.instRefs, rank x < r) → RedEnv Θ (Apply Δ I t) Γ ρ →
      ∃ v, Ev Δ I t ρ e v ∧ Red Θ (Apply Δ I t) τ v := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t iht =>
  intro r
  induction r using Nat.strongRecOn with
  | ind r ihr =>
  intro G Γ e τ h
  induction h with
  | var h =>
    intro ρ _ hρ
    obtain ⟨v, hv, hr⟩ := hρ _ _ h
    exact ⟨v, .var hv, hr⟩
  | boolLit => intro ρ _ _; exact ⟨_, .boolLit, ⟨_, rfl⟩⟩
  | natLit => intro ρ _ _; exact ⟨_, .natLit, ⟨_, rfl⟩⟩
  | lam _ ih =>
    intro ρ hb hρ
    refine ⟨_, .lam, ?_⟩
    intro w hw
    obtain ⟨v, hv, hr⟩ := ih (w :: ρ) hb (hρ.cons hw)
    exact ⟨v, Or.inl ⟨_, _, rfl, hv⟩, hr⟩
  | app _ _ ihf iha =>
    intro ρ hb hρ
    obtain ⟨vf, hvf, hrf⟩ := ihf ρ (fun x hx => hb x (by simp [Expr.instRefs, hx])) hρ
    obtain ⟨va, hva, hra⟩ := iha ρ (fun x hx => hb x (by simp [Expr.instRefs, hx])) hρ
    obtain ⟨v, hap, hr⟩ := hrf va hra
    exact ⟨v, Ev.app_of_apply hvf hva hap, hr⟩
  | @declRef _ d τ htv =>
    intro ρ hb _
    have hd : rank d < r := hb d (by simp [Expr.instRefs])
    cases hre : Δ.realizationOf d with
    | none => exact ⟨_, .refInput hre, hI d τ t htv hre⟩
    | some b =>
      -- the body is typed under its own grant at top level
      have hbody : HasType Θ Δ (Grant.of τ) [] b τ := by
        simp only [DeclEnv.realizationOf, DeclEnv.tyView, Option.bind_eq_some_iff,
          Option.map_eq_some_iff] at hre htv
        obtain ⟨dh, hh, hb'⟩ := hre
        obtain ⟨dh', hh', hty⟩ := htv
        rw [hh] at hh'; cases hh'
        subst hty
        exact ((g.wellFormed hh) _ hb').1
      have hbb : ∀ x ∈ b.instRefs, rank x < rank d :=
        fun x hx => hc d x (InstDependsOn.iff.mpr ⟨b, hre, hx⟩)
      obtain ⟨v, hv, hr⟩ := ihr (rank d) hd hbody [] hbb (RedEnv.nil [])
      exact ⟨v, .refRealized hre hv, hr⟩
  | @rep _ _ s R' hΘs _ ih =>
    intro ρ hb hρ
    obtain ⟨v, hv, hr⟩ := ih ρ hb hρ
    obtain ⟨w, rfl, hw⟩ := hr
    exact ⟨w, .rep hv, (Red_semFree (hΘ s R' hΘs).1).mpr (hw R' hΘs)⟩
  | @mk _ _ s R' _ hΘs _ ih =>
    intro ρ hb hρ
    obtain ⟨w, hw, hr⟩ := ih ρ hb hρ
    refine ⟨_, .mk hw, w, rfl, ?_⟩
    intro R'' hR''
    rw [hΘs] at hR''; cases hR''
    exact (Red_semFree (hΘ s R' hΘs).1).mp hr
  | prim => intro ρ _ _; exact ⟨_, .prim, Red_prim (Apply.hasPrim Δ I t) _⟩
  | @delay i e τ hdata hi he ihi _ =>
    intro ρ hb hρ
    cases t with
    | zero =>
      obtain ⟨v, hv, hr⟩ := ihi ρ hb hρ
      exact ⟨v, .delayZero hv, hr⟩
    | succ t' =>
      obtain ⟨v, hv, hr⟩ := iht t' (Nat.lt_succ_self _) R he ρ (fun x _ => hR x) (RedEnv.nil ρ)
      exact ⟨v, .delaySucc hv, Red_data hΘ hdata hr⟩
  | @sync c i e τ hdata hi he ihi _ =>
    intro ρ hb hρ
    cases t with
    | zero =>
      obtain ⟨v, hv, hr⟩ := ihi ρ hb hρ
      exact ⟨v, .syncZero hv, hr⟩
    | succ t' =>
      obtain ⟨v, hv, hr⟩ := iht t' (Nat.lt_succ_self _) R he ρ (fun x _ => hR x) (RedEnv.nil ρ)
      exact ⟨v, .syncSucc hv, Red_data hΘ hdata hr⟩

/-- **`reactive_total`.**  Every declaration of a causal, globally
    well-formed design has a value at every tick, related to its type. -/
theorem reactive_total {Θ : ConceptEnv} (hΘ : Θ.WF) {Δ : DeclEnv} (hc : Causal Δ) {I : Input}
    {ev : Evidence} (g : GlobalWF ev Θ Δ)
    (hI : ∀ d τ t, Δ.tyView d = some τ → Δ.realizationOf d = none → Red Θ (Apply Δ I t) τ (I d t))
    {d : DeclId} {τ : Ty} (htv : Δ.tyView d = some τ) (t : Nat) :
    ∃ v, Ev Δ I t [] (.declRef d) v ∧ Red Θ (Apply Δ I t) τ v := by
  obtain ⟨rank, R, hR, hr⟩ := hc
  have h : HasType Θ Δ Grant.none [] (.declRef d) τ := .declRef htv
  exact fundamental hΘ hR hr g hI t R h [] (fun x hx => by simp [Expr.instRefs] at hx; subst hx; exact hR _)
    (RedEnv.nil [])

/-- Semantic soundness: *the* value of a well-typed term (unique by
    `Ev.det`) is related to its type. -/
theorem Ev.red {Θ : ConceptEnv} (hΘ : Θ.WF) {Δ : DeclEnv} (hc : Causal Δ) {I : Input}
    {ev : Evidence} (g : GlobalWF ev Θ Δ)
    (hI : ∀ d τ t, Δ.tyView d = some τ → Δ.realizationOf d = none → Red Θ (Apply Δ I t) τ (I d t))
    {G : Grant} {e : Expr} {τ : Ty} (h : HasType Θ Δ G [] e τ) {t : Nat} {v : Value}
    (hv : Ev Δ I t [] e v) : Red Θ (Apply Δ I t) τ v := by
  obtain ⟨rank, R, hR, hr⟩ := hc
  obtain ⟨v', hv', hr'⟩ := fundamental hΘ hR hr g hI t R h [] (fun x _ => hR x) (RedEnv.nil [])
  exact (hv.det hv') ▸ hr'

/-! ## §4 Semantic isolation over time

A value is *tainted* by `s` if a `sem s` tag occurs inside it — including
inside closure environments, and counting a closure body that *could*
construct `s` when applied. -/

inductive Value.Taints (s : SemanticId) : Value → Prop where
  | semHere (v : Value) : Value.Taints s (.sem s v)
  | semInner {s' : SemanticId} {v : Value} : Value.Taints s v → Value.Taints s (.sem s' v)
  | someInner {v : Value} : Value.Taints s v → Value.Taints s (.some v)
  | cloEnv {ρ : List Value} {body : Expr} {v : Value} : v ∈ ρ → Value.Taints s v → Value.Taints s (.clo ρ body)
  | cloBody {ρ : List Value} {body : Expr} : body.constructs s → Value.Taints s (.clo ρ body)
  | primArg {p : Prim} {args : List Value} {v : Value} : v ∈ args → Value.Taints s v → Value.Taints s (.prim p args)
  | listElem {vs : List Value} {v : Value} : v ∈ vs → Value.Taints s v → Value.Taints s (.list vs)

/-- A saturated primitive either returns one of its arguments or a fresh
    untagged value: it never introduces a tag. -/
theorem Prim.compute_taints {s : SemanticId} (p : Prim) (args : List Value)
    (h : (p.compute args).Taints s) : ∃ v ∈ args, v.Taints s := by
  unfold Prim.compute at h
  split at h <;> first
    | (refine ⟨_, ?_, h⟩; simp; done)
    | (refine ⟨_, ?_, Value.Taints.someInner h⟩; simp; done)
    | (cases h; done)
    | (cases h with | someInner h' => (refine ⟨_, ?_, h'⟩; simp; done))
    | (rename_i c x y; cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;> (refine ⟨_, ?_, h⟩; simp; done))
    -- Phase 9a: list results are built from list arguments
    | (cases h with | listElem hm _ => (simp at hm; done))
    | (cases h with | listElem hm h' =>
        (rcases List.mem_cons.mp hm with rfl | hm'
         · (refine ⟨_, ?_, h'⟩; simp; done)
         · (refine ⟨_, ?_, Value.Taints.listElem hm' h'⟩; simp; done)))
    | (cases h with | listElem hm h' => (refine ⟨_, ?_, Value.Taints.listElem (List.mem_of_mem_take hm) h'⟩; simp; done))
    | (cases h with | listElem hm h' => (refine ⟨_, ?_, Value.Taints.listElem (List.mem_reverse.mp hm) h'⟩; simp; done))
    | (cases h with | someInner h' => (rename_i x xs; refine ⟨.list (x :: xs), ?_, Value.Taints.listElem List.mem_cons_self h'⟩; simp; done))

theorem applyPrim_taints {s : SemanticId} (p : Prim) (args : List Value)
    (h : (applyPrim p args).Taints s) : ∃ v ∈ args, v.Taints s := by
  unfold applyPrim at h
  split at h
  · exact Prim.compute_taints p args h
  · cases h with | primArg hm ht => exact ⟨_, hm, ht⟩

/-- **Tag provenance.**  If no realization constructs `s`, no input value
    carries `s`, the term itself does not construct `s`, and the environment
    is clean, then the result is clean.  In particular `delay` — the only
    stateful construct — never manufactures a tag: state preserves semantic
    values, it cannot re-label them. -/
theorem Ev.tag_provenance {Δ : DeclEnv} {I : Input} (s : SemanticId)
    (hΔ : ∀ d b, Δ.realizationOf d = some b → ¬ b.constructs s)
    (hI : ∀ d t, ¬ (I d t).Taints s) :
    ∀ {t : Nat} {ρ : List Value} {e : Expr} {v : Value}, Ev Δ I t ρ e v →
      ¬ e.constructs s → (∀ w ∈ ρ, ¬ w.Taints s) → ¬ v.Taints s := by
  intro t ρ e v h
  induction h with
  | var hv => intro _ hρ; exact hρ _ (List.mem_of_getElem? hv)
  | boolLit | natLit => intro _ _ ht; cases ht
  | lam =>
    intro he hρ ht
    cases ht with
    | cloEnv hw ht => exact hρ _ hw ht
    | cloBody hb => exact he hb
  | appClo _ _ _ ihf iha ihb =>
    intro he hρ
    have hf := ihf (fun h => he (Or.inl h)) hρ
    have ha := iha (fun h => he (Or.inr h)) hρ
    refine ihb (fun hb => hf (.cloBody hb)) ?_
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact ha
    · exact fun ht => hf (.cloEnv hw' ht)
  | appPrim _ _ ihf iha =>
    intro he hρ ht
    have hf := ihf (fun h => he (Or.inl h)) hρ
    have ha := iha (fun h => he (Or.inr h)) hρ
    obtain ⟨w, hw, hwt⟩ := applyPrim_taints _ _ ht
    rcases List.mem_append.mp hw with hw' | hw'
    · exact hf (.primArg hw' hwt)
    · simp at hw'; subst hw'; exact ha hwt
  | refRealized hs _ ih => intro _ _; exact ih (hΔ _ _ hs) (fun _ h => by simp at h)
  | refInput _ => intro _ _; exact hI _ _
  | rep _ ih =>
    intro he hρ ht
    exact ih he hρ (.semInner ht)
  | mk _ ih =>
    intro he hρ ht
    cases ht with
    | semHere _ => exact he (Or.inl rfl)
    | semInner ht => exact ih (fun h => he (Or.inr h)) hρ ht
  | prim =>
    intro _ _ ht
    obtain ⟨w, hw, _⟩ := applyPrim_taints _ _ ht
    simp at hw
  | delayZero _ ih => intro he hρ; exact ih (fun h => he (Or.inl h)) hρ
  | delaySucc _ ih => intro he hρ; exact ih (fun h => he (Or.inr h)) hρ
  | syncZero _ ih => intro he hρ; exact ih (fun h => he (Or.inl h)) hρ
  | syncSucc _ ih => intro he hρ; exact ih (fun h => he (Or.inr h)) hρ

/-- **`temporal_state_preserves_semantic_identity`.**  Combined with the
    Phase-3 grant discipline: if no declaration's *signature* announces
    `sem s` and no input carries `s`, then no value at any tick carries `s`
    — with delays, closures and primitives all present. -/
theorem temporal_state_preserves_semantic_identity {Θ : ConceptEnv} {Δ : DeclEnv} {I : Input}
    {ev : Evidence} (g : GlobalWF ev Θ Δ) (s : SemanticId)
    (hsig : ∀ d dh, Δ d = some dh → s ∉ dh.interface.expectedType.grant)
    (hI : ∀ d t, ¬ (I d t).Taints s)
    {t : Nat} {d : DeclId} {v : Value} (h : Ev Δ I t [] (.declRef d) v) : ¬ v.Taints s := by
  refine Ev.tag_provenance s ?_ hI h (by simp [Expr.constructs]) (fun _ h => by simp at h)
  intro d' b hb
  simp only [DeclEnv.realizationOf, Option.bind_eq_some_iff] at hb
  obtain ⟨dh, hdh, hre⟩ := hb
  have ht := ((g.wellFormed hdh) b hre).1
  intro hc
  exact hsig d' dh hdh (ht.constructs_granted s hc)

/-- A decidable causality check for finite designs. -/
def causalCheck (l : List DesignDecl) (rank : DeclId → Nat) : Bool :=
  l.all fun dh =>
    match dh.realization with
    | some e => e.instRefs.all fun b => decide (rank b < rank dh.id)
    | none => true

theorem Causal.ofList {l : List DesignDecl} (rank : DeclId → Nat) (R : Nat) (hR : ∀ d, rank d < R)
    (h : causalCheck l rank = true) : Causal (.ofList l) := by
  refine ⟨rank, R, hR, ?_⟩
  intro a b hab
  obtain ⟨e, he, hb⟩ := InstDependsOn.iff.mp hab
  simp only [DeclEnv.realizationOf, Option.bind_eq_some_iff] at he
  obtain ⟨dh, hdh, hre⟩ := he
  obtain ⟨hmem, hid⟩ := DeclEnv.ofList_some hdh
  subst hid
  have := (List.all_eq_true.mp h) dh hmem
  rw [hre] at this
  exact of_decide_eq_true ((List.all_eq_true.mp this) b hb)

/-! ## Wiring designs: unfolding preserves stepping -/

def _root_.BDL.Expr.Wiring : Expr → Prop
  | .var _ | .lam _ _ => False
  | .app f a => f.Wiring ∧ a.Wiring
  | .rep e => e.Wiring
  | .mk _ e => e.Wiring
  | .delay i e => i.Wiring ∧ e.Wiring
  | .sync _ i e => i.Wiring ∧ e.Wiring
  | _ => True

def DeclEnvWiring (Δ : DeclEnv) : Prop := ∀ d b, Δ.realizationOf d = some b → b.Wiring

inductive Value.HasClo : Value → Prop where
  | clo (ρ : List Value) (body : Expr) : Value.HasClo (.clo ρ body)
  | semInner {s : SemanticId} {v : Value} : Value.HasClo v → Value.HasClo (.sem s v)
  | someInner {v : Value} : Value.HasClo v → Value.HasClo (.some v)
  | primArg {p : Prim} {args : List Value} {v : Value} : v ∈ args → Value.HasClo v → Value.HasClo (.prim p args)
  | listElem {vs : List Value} {v : Value} : v ∈ vs → Value.HasClo v → Value.HasClo (.list vs)

abbrev Value.NoClo (v : Value) : Prop := ¬ v.HasClo

theorem Prim.compute_noClo (p : Prim) (args : List Value) (h : ∀ v ∈ args, v.NoClo) : (p.compute args).NoClo := by
  intro hc
  unfold Prim.compute at hc
  split at hc <;> first
    | (refine h _ ?_ hc; simp; done)
    | (refine h _ ?_ (Value.HasClo.someInner hc); simp; done)
    | (cases hc; done)
    | (cases hc with | someInner hc' => (refine h _ ?_ hc'; simp; done))
    | (rename_i c x y; cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at hc <;> (refine h _ ?_ hc; simp; done))
    -- Phase 9a: list results are built from list arguments
    | (cases hc with | listElem hm _ => (simp at hm; done))
    | (cases hc with | listElem hm hc' =>
        (rcases List.mem_cons.mp hm with rfl | hm'
         · (refine h _ ?_ hc'; simp; done)
         · (refine h _ ?_ (Value.HasClo.listElem hm' hc'); simp; done)))
    | (cases hc with | listElem hm hc' => (refine h _ ?_ (Value.HasClo.listElem (List.mem_of_mem_take hm) hc'); simp; done))
    | (cases hc with | listElem hm hc' => (refine h _ ?_ (Value.HasClo.listElem (List.mem_reverse.mp hm) hc'); simp; done))
    | (cases hc with | someInner hc' => (rename_i x xs; refine h (.list (x :: xs)) ?_ (Value.HasClo.listElem List.mem_cons_self hc'); simp; done))

theorem applyPrim_noClo (p : Prim) (args : List Value) (h : ∀ v ∈ args, v.NoClo) : (applyPrim p args).NoClo := by
  unfold applyPrim; split
  · exact Prim.compute_noClo p args h
  · intro hc; cases hc with | primArg hm hc' => exact h _ hm hc'

/-- Wiring designs never produce closures. -/
theorem Ev.noClo {Δ : DeclEnv} (hΔ : DeclEnvWiring Δ) {I : Input} (hI : ∀ d t, (I d t).NoClo) :
    ∀ {t : Nat} {ρ : List Value} {e : Expr} {v : Value}, Ev Δ I t ρ e v → e.Wiring → v.NoClo := by
  intro t ρ e v h
  induction h with
  | var _ => intro hw; exact hw.elim
  | boolLit | natLit => intro _ hc; cases hc
  | lam => intro hw; exact hw.elim
  | appClo _ _ _ ihf _ _ => intro hw; exact (ihf hw.1 (.clo _ _)).elim
  | appPrim _ _ ihf iha =>
    intro hw
    have hf := ihf hw.1
    have ha := iha hw.2
    refine applyPrim_noClo _ _ ?_
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact fun hc => hf (.primArg hv hc)
    · simp at hv; subst hv; exact ha
  | refRealized hs _ ih => intro _; exact ih (hΔ _ _ hs)
  | refInput _ => intro _; exact hI _ _
  | rep _ ih => intro hw hc; exact ih hw (.semInner hc)
  | mk _ ih => intro hw hc; cases hc with | semInner hc' => exact ih hw hc'
  | prim => intro _; exact applyPrim_noClo _ _ (fun _ h => by simp at h)
  | delayZero _ ih => intro hw; exact ih hw.1
  | delaySucc _ ih => intro hw; exact ih hw.2
  | syncZero _ ih => intro hw; exact ih hw.1
  | syncSucc _ ih => intro hw; exact ih hw.2

/-- The environment is irrelevant for wiring terms. -/
theorem Ev.env_irrelevant {Δ : DeclEnv} (hΔ : DeclEnvWiring Δ) {I : Input} (hI : ∀ d t, (I d t).NoClo) :
    ∀ {t : Nat} {ρ : List Value} {e : Expr} {v : Value}, Ev Δ I t ρ e v → e.Wiring →
      ∀ ρ', Ev Δ I t ρ' e v := by
  intro t ρ e v h
  induction h with
  | var _ => intro hw; exact hw.elim
  | boolLit => intro _ _; exact .boolLit
  | natLit => intro _ _; exact .natLit
  | lam => intro hw; exact hw.elim
  | appClo hf _ _ _ _ _ => intro hw; exact ((Ev.noClo hΔ hI hf hw.1) (.clo _ _)).elim
  | appPrim _ _ ihf iha => intro hw ρ'; exact .appPrim (ihf hw.1 ρ') (iha hw.2 ρ')
  | refRealized hs hb _ => intro _ _; exact .refRealized hs hb
  | refInput hn => intro _ _; exact .refInput hn
  | rep _ ih => intro hw ρ'; exact .rep (ih hw ρ')
  | mk _ ih => intro hw ρ'; exact .mk (ih hw ρ')
  | prim => intro _ _; exact .prim
  | delayZero _ ih => intro hw ρ'; exact .delayZero (ih hw.1 ρ')
  | delaySucc _ ih => intro hw ρ'; exact .delaySucc (ih hw.2 ρ')
  | syncZero _ ih => intro hw ρ'; exact .syncZero (ih hw.1 ρ')
  | syncSucc _ ih => intro hw ρ'; exact .syncSucc (ih hw.2 ρ')

theorem unfolds_wiring {Δ : DeclEnv} (hΔ : DeclEnvWiring Δ) {e e' : Expr} (h : Unfolds Δ e e') (hw : e.Wiring) : e'.Wiring := by
  induction h with
  | var _ | boolLit _ | natLit _ | prim _ => exact hw
  | lam _ _ => exact hw.elim
  | app _ _ ihf iha => exact ⟨ihf hw.1, iha hw.2⟩
  | refStuck _ => trivial
  | refRealized hs _ ih => exact ih (hΔ _ _ hs)
  | rep _ ih => exact ih hw
  | mk _ ih => exact ih hw
  | delay _ _ ihi ihe => exact ⟨ihi hw.1, ihe hw.2⟩
  | sync _ _ ihi ihe => exact ⟨ihi hw.1, ihe hw.2⟩

/-- **Unfolding preserves stepping** on wiring designs: the value of a term
    at any tick is the value of its unfolding.  So `Unfolds` (Phase 1) is a
    correct *optimization* wherever it exists; `Ev` is the semantics. -/
theorem unfolds_preserves_eval {Δ : DeclEnv} (hΔ : DeclEnvWiring Δ) {I : Input} (hI : ∀ d t, (I d t).NoClo)
    {e e' : Expr} (hu : Unfolds Δ e e') (hw : e.Wiring) :
    ∀ (t : Nat) (ρ : List Value) (v : Value), Ev Δ I t ρ e v → Ev Δ I t ρ e' v := by
  induction hu with
  | var _ | boolLit _ | natLit _ | prim _ | refStuck _ => intro _ _ _ h; exact h
  | lam _ _ => exact hw.elim
  | app _ _ ihf iha =>
    intro t ρ v h
    cases h with
    | appClo hf _ _ => exact ((Ev.noClo hΔ hI hf hw.1) (.clo _ _)).elim
    | appPrim hf ha => exact .appPrim (ihf hw.1 _ _ _ hf) (iha hw.2 _ _ _ ha)
  | @refRealized d b b' hs hu' ih =>
    intro t ρ v h
    cases h with
    | refRealized hs' hb =>
      rw [hs] at hs'; cases hs'
      exact Ev.env_irrelevant hΔ hI (ih (hΔ _ _ hs) _ _ _ hb) (unfolds_wiring hΔ hu' (hΔ _ _ hs)) ρ
    | refInput hn => rw [hs] at hn; exact nomatch hn
  | rep _ ih => intro t ρ v h; cases h with | rep h' => exact .rep (ih hw _ _ _ h')
  | mk _ ih => intro t ρ v h; cases h with | mk h' => exact .mk (ih hw _ _ _ h')
  | delay _ _ ihi ihe =>
    intro t ρ v h
    cases h with
    | delayZero h' => exact .delayZero (ihi hw.1 _ _ _ h')
    | delaySucc h' => exact .delaySucc (ihe hw.2 _ _ _ h')
  | sync _ _ ihi ihe =>
    intro t ρ v h
    cases h with
    | syncZero h' => exact .syncZero (ihi hw.1 _ _ _ h')
    | syncSucc h' => exact .syncSucc (ihe hw.2 _ _ _ h')

/-- `rep (delay i x)` and `delay (rep i) (rep x)` evaluate identically:
    representation access commutes with delay (both are typed `q Angle`). -/
theorem rep_delay_commute {Δ : DeclEnv} {I : Input} (t : Nat) (ρ : List Value) (i x : Expr) (w : Value) :
    Ev Δ I t ρ (.rep (.delay i x)) w ↔ Ev Δ I t ρ (.delay (.rep i) (.rep x)) w := by
  constructor
  · intro h
    cases h with
    | rep h' =>
      cases h' with
      | delayZero hi => exact .delayZero (.rep hi)
      | delaySucc hx => exact .delaySucc (.rep hx)
  · intro h
    cases h with
    | delayZero hi => cases hi with | rep hi' => exact .rep (.delayZero hi')
    | delaySucc hx => cases hx with | rep hx' => exact .rep (.delaySucc hx')


end BDL.Reactive
