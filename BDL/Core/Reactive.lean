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
  /-- Phase 9b: a pair. -/
  | pair (a b : Value)
  deriving Repr, Inhabited

/-! ### Structural equality and order on data values (Phase 9b)

The closed capability vocabulary is {`Data`}: every data value admits a
decidable structural equality and a lexicographic order — booleans
`false < true`, numbers, `none < some`, pairs and lists lexicographically,
semantic values by their representations (typing already forbids comparing
two concepts).  Closures compare `false`; typing never asks. -/

mutual
def Value.beq : Value → Value → Bool
  | .bool a, .bool b => a == b
  | .nat a, .nat b => a == b
  | .sem s v, .sem s' w => s == s' && Value.beq v w
  | .none, .none => true
  | .some v, .some w => Value.beq v w
  | .pair a b, .pair c d => Value.beq a c && Value.beq b d
  | .list vs, .list ws => Value.beqList vs ws
  | _, _ => false
def Value.beqList : List Value → List Value → Bool
  | [], [] => true
  | v :: vs, w :: ws => Value.beq v w && Value.beqList vs ws
  | _, _ => false
end

mutual
def Value.blt : Value → Value → Bool
  | .bool a, .bool b => !a && b
  | .nat a, .nat b => decide (a < b)
  | .sem s v, .sem s' w => s == s' && Value.blt v w
  | .none, .some _ => true
  | .some v, .some w => Value.blt v w
  | .pair a b, .pair c d => Value.blt a c || (Value.beq a c && Value.blt b d)
  | .list vs, .list ws => Value.bltList vs ws
  | _, _ => false
def Value.bltList : List Value → List Value → Bool
  | [], _ :: _ => true
  | v :: vs, w :: ws => Value.blt v w || (Value.beq v w && Value.bltList vs ws)
  | _, _ => false
end

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
  | .not | .isSome _ | .some _ | .length _ | .reverse _ | .head _ | .fst _ _ | .snd _ _ | .toList _ => 1
  | .add _ | .sub _ | .mul _ _ | .div _ _ | .lt _ _ | .eq _ _ | .and | .or | .getD _ | .cons _ | .take _ | .pair _ _
  | .drop _ => 2
  | .ite _ => 3

/-- Saturated primitive evaluation.  Ill-shaped arguments (excluded by typing)
    default to `nat 0`. -/
def _root_.BDL.Prim.compute : Prim → List Value → Value
  | .lit _ n, _ => .nat n
  | .add _, [.nat a, .nat b] => .nat (a + b)
  | .sub _, [.nat a, .nat b] => .nat (a - b)
  | .mul _ _, [.nat a, .nat b] => .nat (a * b)
  | .div _ _, [.nat a, .nat b] => .nat (a / b)
  | .lt _ _, [a, b] => .bool (Value.blt a b)
  | .eq _ _, [a, b] => .bool (Value.beq a b)
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
  | .pair _ _, [a, b] => .pair a b
  | .fst _ _, [.pair a _] => a
  | .snd _ _, [.pair _ b] => b
  | .drop _, [.nat k, .list xs] => .list (xs.drop k)
  | .toList _, [.some x] => .list [x]
  | .toList _, [.none] => .list []
  | _, _ => .nat 0

/-- Apply a primitive to one more argument: compute when saturated. -/
def applyPrim (p : Prim) (args : List Value) : Value :=
  if args.length = p.arity then p.compute args else .prim p args

/-- Input streams: a value for every (unresolved) declaration at every tick. -/
abbrev Input := DeclId → Nat → Value

/-- `fold f z l` over the environment `[l, z, f]` (Phase 9b). -/
def _root_.BDL.foldVarTerm : Expr := .fold (.var 2) (.var 1) (.var 0)
/-- `f x r` over the environment `[r, x, f]` (Phase 9b). -/
def _root_.BDL.stepVarTerm : Expr := .app (.app (.var 2) (.var 1)) (.var 0)

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
  /-- Phase 9b: the list recursor on the empty list is `z`. -/
  | foldNil {t ρ f z l vf vz} :
      Ev Δ I t ρ f vf → Ev Δ I t ρ z vz → Ev Δ I t ρ l (.list []) → Ev Δ I t ρ (.fold f z l) vz
  /-- On `x :: xs`: recurse on `xs` (the three values passed through the
      environment, `foldVarTerm`), then apply `f x r` (`stepVarTerm`).  The
      recursion is syntactic unrolling through the environment, so `Ev`
      stays an ordinary inductive relation. -/
  | foldCons {t ρ f z l vf vz x xs r v} :
      Ev Δ I t ρ f vf → Ev Δ I t ρ z vz → Ev Δ I t ρ l (.list (x :: xs)) →
      Ev Δ I t [.list xs, vz, vf] foldVarTerm r → Ev Δ I t [r, x, vf] stepVarTerm v →
      Ev Δ I t ρ (.fold f z l) v

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
  | foldNil _ _ _ _ ihz ihl =>
    cases h₂ with
    | foldNil _ hz' _ => exact ihz hz'
    | foldCons _ _ hl' _ _ => cases ihl hl'
  | foldCons _ _ _ _ _ ihf ihz ihl ihr ihv =>
    cases h₂ with
    | foldNil _ _ hl' => cases ihl hl'
    | foldCons hf' hz' hl' hr' hv' =>
      cases ihf hf'; cases ihz hz'; cases ihl hl'; cases ihr hr'; exact ihv hv'

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
    | .fold f z l =>
      (evalF Δ I fuel t ρ f).bind fun vf =>
      (evalF Δ I fuel t ρ z).bind fun vz =>
      (evalF Δ I fuel t ρ l).bind fun vl =>
      match vl with
      | .list [] => Option.some vz
      | .list (x :: xs) =>
        (evalF Δ I fuel t [.list xs, vz, vf] foldVarTerm).bind fun r =>
        evalF Δ I fuel t [r, x, vf] stepVarTerm
      | _ => Option.none

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
      | bool _ | nat _ | sem _ _ | none | some _ | list _ | pair _ _ => simp at hm
    | declRef d =>
      simp only [evalF] at h
      cases hr : Δ.realizationOf d with
      | none => rw [hr] at h; exact (Option.some.inj h) ▸ Ev.refInput hr
      | some b => rw [hr] at h; exact .refRealized hr (evalF_sound h)
    | fold f z l =>
      simp only [evalF, Option.bind_eq_some_iff] at h
      obtain ⟨vf, hf, vz, hz, vl, hl, hm⟩ := h
      cases vl with
      | list vs =>
        cases vs with
        | nil =>
          simp only [Option.some.injEq] at hm
          subst hm
          exact .foldNil (evalF_sound hf) (evalF_sound hz) (evalF_sound hl)
        | cons x xs =>
          simp only [Option.bind_eq_some_iff] at hm
          obtain ⟨r, hr, hv⟩ := hm
          exact .foldCons (evalF_sound hf) (evalF_sound hz) (evalF_sound hl) (evalF_sound hr) (evalF_sound hv)
      | bool _ | nat _ | sem _ _ | none | some _ | clo _ _ | prim _ _ | pair _ _ => simp at hm
    | rep e =>
      simp only [evalF, Option.bind_eq_some_iff] at h
      obtain ⟨ve, he, hm⟩ := h
      cases ve with
      | sem s w => simp only [Option.some.injEq] at hm; subst hm; exact .rep (evalF_sound he)
      | bool _ | nat _ | none | some _ | clo _ _ | prim _ _ | list _ | pair _ _ => simp at hm
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
  | .fold f z l => f.strictRefs ++ z.strictRefs ++ l.strictRefs
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
  | foldNil _ _ _ ihf ihz ihl =>
    intro x hx
    simp only [Expr.strictRefs, List.mem_append] at hx
    exact hx.elim (fun h => h.elim (ihf x) (ihz x)) (ihl x)
  | foldCons _ _ _ _ _ ihf ihz ihl _ _ =>
    intro x hx
    simp only [Expr.strictRefs, List.mem_append] at hx
    exact hx.elim (fun h => h.elim (ihf x) (ihz x)) (ihl x)

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
    | fold f z l ihf ihz ihl =>
      intro h
      simp only [Expr.strictRefs, Expr.instRefs, List.mem_append] at h ⊢
      rcases h with (h | h) | h
      · exact .inl (.inl (ihf h))
      · exact .inl (.inr (ihz h))
      · exact .inr (ihl h)

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
  | .prod a b, v => ∃ x y, v = .pair x y ∧ RedSF A a x ∧ RedSF A b y
  | .arr a b, v => ∀ w, RedSF A a w → ∃ v', A v w v' ∧ RedSF A b v'
  | .sem _, _ => False

/-- Logical relation.  A semantic value is a tagged representation value. -/
def Red (Θ : ConceptEnv) (A : App) : Ty → Value → Prop
  | .bool, v => ∃ b, v = .bool b
  | .nat, v => ∃ n, v = .nat n
  | .q _, v => ∃ n, v = .nat n
  | .opt τ, v => v = .none ∨ ∃ w, v = .some w ∧ Red Θ A τ w
  | .list τ, v => ∃ vs, v = .list vs ∧ ∀ w ∈ vs, Red Θ A τ w
  | .prod a b, v => ∃ x y, v = .pair x y ∧ Red Θ A a x ∧ Red Θ A b y
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
  | .prod a b, h, v => by
    simp only [Red, RedSF]
    constructor
    · rintro ⟨x, y, rfl, hx, hy⟩
      exact ⟨x, y, rfl, (Red_semFree h.1).mp hx, (Red_semFree h.2).mp hy⟩
    · rintro ⟨x, y, rfl, hx, hy⟩
      exact ⟨x, y, rfl, (Red_semFree h.1).mpr hx, (Red_semFree h.2).mpr hy⟩
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
  | .prod a b, hd, v, h => by
    simp only [RedSF] at h ⊢
    obtain ⟨x, y, rfl, hx, hy⟩ := h
    exact ⟨x, y, rfl, RedSF_data (τ := a) hd.1 hx, RedSF_data (τ := b) hd.2 hy⟩

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
  | .prod a b, hd, v, h => by
    simp only [Red] at h ⊢
    obtain ⟨x, y, rfl, hx, hy⟩ := h
    exact ⟨x, y, rfl, Red_data (τ := a) hΘ hd.1 hx, Red_data (τ := b) hΘ hd.2 hy⟩

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
  | lt τ _ | eq τ _ =>
    simp only [Prim.ty, Red, applyPrim, Prim.arity]
    intro a _
    refine ⟨_, hA _ _ _, ?_⟩
    simp only [applyPrim, Prim.arity]
    intro b _
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
  | pair a b =>
    simp only [Prim.ty, Red, applyPrim, Prim.arity]
    intro x hx
    refine ⟨_, hA _ _ _, ?_⟩
    simp only [applyPrim, Prim.arity]
    intro y hy
    refine ⟨_, hA _ _ _, x, y, by simp [applyPrim, Prim.arity, Prim.compute], hx, hy⟩
  | fst a b =>
    simp only [Prim.ty, Red, applyPrim, Prim.arity]
    rintro _ ⟨x, y, rfl, hx, hy⟩
    exact ⟨_, hA _ _ _, by simpa [applyPrim, Prim.arity, Prim.compute] using hx⟩
  | snd a b =>
    simp only [Prim.ty, Red, applyPrim, Prim.arity]
    rintro _ ⟨x, y, rfl, hx, hy⟩
    exact ⟨_, hA _ _ _, by simpa [applyPrim, Prim.arity, Prim.compute] using hy⟩
  | drop τ =>
    simp only [Prim.ty, Red, applyPrim, Prim.arity]
    rintro _ ⟨k, rfl⟩
    refine ⟨_, hA _ _ _, ?_⟩
    simp only [applyPrim, Prim.arity]
    rintro _ ⟨vs, rfl, hvs⟩
    refine ⟨_, hA _ _ _, vs.drop k, by simp [applyPrim, Prim.arity, Prim.compute], ?_⟩
    intro w hw
    exact hvs w (List.mem_of_mem_drop hw)
  | toList τ =>
    simp only [Prim.ty, Red, applyPrim, Prim.arity]
    intro o ho
    refine ⟨_, hA _ _ _, ?_⟩
    rcases ho with rfl | ⟨w, rfl, hw⟩
    · exact ⟨[], by simp [applyPrim, Prim.arity, Prim.compute], fun _ h => by simp at h⟩
    · refine ⟨[w], by simp [applyPrim, Prim.arity, Prim.compute], ?_⟩
      intro x hx; simp at hx; subst hx; exact hw

/-- **`fold_total`** (Phase 9b): the recursor applied through the
    environment to related values yields a related value, by induction on
    the list. -/
theorem fold_total {Θ : ConceptEnv} {Δ : DeclEnv} {I : Input} {t : Nat} {τ σ : Ty} {vf vz : Value}
    (hf : Red Θ (Apply Δ I t) (.arr τ (.arr σ σ)) vf) (hz : Red Θ (Apply Δ I t) σ vz) :
    ∀ vs, (∀ w ∈ vs, Red Θ (Apply Δ I t) τ w) →
      ∃ r, Ev Δ I t [.list vs, vz, vf] foldVarTerm r ∧ Red Θ (Apply Δ I t) σ r
  | [], _ => ⟨vz, .foldNil (.var rfl) (.var rfl) (.var rfl), hz⟩
  | x :: xs, hvs => by
    obtain ⟨r, hr, hrr⟩ := fold_total hf hz xs (fun w hw => hvs w (List.mem_cons_of_mem x hw))
    obtain ⟨g, hg, hrg⟩ := hf x (hvs x List.mem_cons_self)
    obtain ⟨v, hv, hrv⟩ := hrg r hrr
    refine ⟨v, .foldCons (.var rfl) (.var rfl) (.var rfl) hr ?_, hrv⟩
    exact Ev.app_of_apply (Ev.app_of_apply (.var rfl) (.var rfl) hg) (.var rfl) hv

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
  | fold _ _ _ ihf ihz ihl =>
    intro ρ hb hρ
    obtain ⟨vf, hvf, hrf⟩ := ihf ρ (fun x hx => hb x (by simp [Expr.instRefs, hx])) hρ
    obtain ⟨vz, hvz, hrz⟩ := ihz ρ (fun x hx => hb x (by simp [Expr.instRefs, hx])) hρ
    obtain ⟨vl, hvl, hrl⟩ := ihl ρ (fun x hx => hb x (by simp [Expr.instRefs, hx])) hρ
    obtain ⟨vs, rfl, hvs⟩ := hrl
    cases vs with
    | nil => exact ⟨vz, .foldNil hvf hvz hvl, hrz⟩
    | cons x xs =>
      obtain ⟨r, hr, hrr⟩ := fold_total hrf hrz xs (fun w hw => hvs w (List.mem_cons_of_mem x hw))
      obtain ⟨g, hg, hrg⟩ := hrf x (hvs x List.mem_cons_self)
      obtain ⟨v, hv, hrv⟩ := hrg r hrr
      refine ⟨v, .foldCons hvf hvz hvl hr ?_, hrv⟩
      exact Ev.app_of_apply (Ev.app_of_apply (.var rfl) (.var rfl) hg) (.var rfl) hv

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
  | pairFst {a b : Value} : Value.Taints s a → Value.Taints s (.pair a b)
  | pairSnd {a b : Value} : Value.Taints s b → Value.Taints s (.pair a b)

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
    -- Phase 9b: pairs
    | (cases h with
        | pairFst h' => (refine ⟨_, ?_, h'⟩; simp; done)
        | pairSnd h' => (refine ⟨_, ?_, h'⟩; simp; done))
    | (rename_i a b; refine ⟨.pair a b, ?_, Value.Taints.pairFst h⟩; simp; done)
    | (rename_i a b; refine ⟨.pair a b, ?_, Value.Taints.pairSnd h⟩; simp; done)
    | (cases h with | listElem hm h' => (refine ⟨_, ?_, Value.Taints.listElem (List.mem_of_mem_drop hm) h'⟩; simp; done))
    | (cases h with | listElem hm h' => (simp at hm; subst hm; refine ⟨_, ?_, Value.Taints.someInner h'⟩; simp; done))

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
  | foldNil _ _ _ _ ihz _ => intro he hρ; exact ihz (fun h => he (Or.inr (Or.inl h))) hρ
  | @foldCons _ _ _ _ _ vf vz x xs r v _ _ _ _ _ ihf ihz ihl ihr ihv =>
    intro he hρ
    have hf := ihf (fun h => he (Or.inl h)) hρ
    have hz := ihz (fun h => he (Or.inr (Or.inl h))) hρ
    have hl := ihl (fun h => he (Or.inr (Or.inr h))) hρ
    have hxs : ∀ w ∈ [Value.list xs, vz, vf], ¬ w.Taints s := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · intro ht; cases ht with | listElem hm ht' => exact hl (.listElem (List.mem_cons_of_mem _ hm) ht')
      · exact hz
      · exact hf
    have hr := ihr (by simp [foldVarTerm, Expr.constructs]) hxs
    refine ihv (by simp [stepVarTerm, Expr.constructs]) ?_
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact hr
    · exact fun ht => hl (.listElem List.mem_cons_self ht)
    · exact hf

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
  | .fold f z l => f.Wiring ∧ z.Wiring ∧ l.Wiring
  | _ => True

/-- Wiring with variables allowed (no `lam`): the fragment the recursor's
    environment-passing sub-derivations live in. -/
def _root_.BDL.Expr.WiringV : Expr → Prop
  | .lam _ _ => False
  | .app f a => f.WiringV ∧ a.WiringV
  | .rep e => e.WiringV
  | .mk _ e => e.WiringV
  | .delay i e => i.WiringV ∧ e.WiringV
  | .sync _ i e => i.WiringV ∧ e.WiringV
  | .fold f z l => f.WiringV ∧ z.WiringV ∧ l.WiringV
  | _ => True

theorem _root_.BDL.Expr.Wiring.toV : ∀ {e : Expr}, e.Wiring → e.WiringV
  | .var _, h => h.elim
  | .lam _ _, h => h.elim
  | .boolLit _, _ | .natLit _, _ | .declRef _, _ | .prim _, _ => trivial
  | .app f a, h => ⟨Expr.Wiring.toV (e := f) h.1, Expr.Wiring.toV (e := a) h.2⟩
  | .rep e, h => Expr.Wiring.toV (e := e) h
  | .mk _ e, h => Expr.Wiring.toV (e := e) h
  | .delay i e, h => ⟨Expr.Wiring.toV (e := i) h.1, Expr.Wiring.toV (e := e) h.2⟩
  | .sync _ i e, h => ⟨Expr.Wiring.toV (e := i) h.1, Expr.Wiring.toV (e := e) h.2⟩
  | .fold f z l, h => ⟨Expr.Wiring.toV (e := f) h.1, Expr.Wiring.toV (e := z) h.2.1, Expr.Wiring.toV (e := l) h.2.2⟩

def DeclEnvWiring (Δ : DeclEnv) : Prop := ∀ d b, Δ.realizationOf d = some b → b.Wiring

inductive Value.HasClo : Value → Prop where
  | clo (ρ : List Value) (body : Expr) : Value.HasClo (.clo ρ body)
  | semInner {s : SemanticId} {v : Value} : Value.HasClo v → Value.HasClo (.sem s v)
  | someInner {v : Value} : Value.HasClo v → Value.HasClo (.some v)
  | primArg {p : Prim} {args : List Value} {v : Value} : v ∈ args → Value.HasClo v → Value.HasClo (.prim p args)
  | listElem {vs : List Value} {v : Value} : v ∈ vs → Value.HasClo v → Value.HasClo (.list vs)
  | pairFst {a b : Value} : Value.HasClo a → Value.HasClo (.pair a b)
  | pairSnd {a b : Value} : Value.HasClo b → Value.HasClo (.pair a b)

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
    -- Phase 9b: pairs
    | (cases hc with
        | pairFst hc' => (refine h _ ?_ hc'; simp; done)
        | pairSnd hc' => (refine h _ ?_ hc'; simp; done))
    | (rename_i a b; refine h (.pair a b) ?_ (Value.HasClo.pairFst hc); simp; done)
    | (rename_i a b; refine h (.pair a b) ?_ (Value.HasClo.pairSnd hc); simp; done)
    | (cases hc with | listElem hm hc' => (refine h _ ?_ (Value.HasClo.listElem (List.mem_of_mem_drop hm) hc'); simp; done))
    | (cases hc with | listElem hm hc' => (simp at hm; subst hm; refine h _ ?_ (Value.HasClo.someInner hc'); simp; done))

theorem applyPrim_noClo (p : Prim) (args : List Value) (h : ∀ v ∈ args, v.NoClo) : (applyPrim p args).NoClo := by
  unfold applyPrim; split
  · exact Prim.compute_noClo p args h
  · intro hc; cases hc with | primArg hm hc' => exact h _ hm hc'

/-- Closure-free environments and lambda-free terms never produce closures. -/
theorem Ev.noCloV {Δ : DeclEnv} (hΔ : DeclEnvWiring Δ) {I : Input} (hI : ∀ d t, (I d t).NoClo) :
    ∀ {t : Nat} {ρ : List Value} {e : Expr} {v : Value}, Ev Δ I t ρ e v → e.WiringV →
      (∀ w ∈ ρ, w.NoClo) → v.NoClo := by
  intro t ρ e v h
  induction h with
  | var hv => intro _ hρ; exact hρ _ (List.mem_of_getElem? hv)
  | boolLit | natLit => intro _ _ hc; cases hc
  | lam => intro hw; exact hw.elim
  | appClo _ _ _ ihf _ _ => intro hw hρ; exact (ihf hw.1 hρ (.clo _ _)).elim
  | appPrim _ _ ihf iha =>
    intro hw hρ
    have hf := ihf hw.1 hρ
    have ha := iha hw.2 hρ
    refine applyPrim_noClo _ _ ?_
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact fun hc => hf (.primArg hv hc)
    · simp at hv; subst hv; exact ha
  | refRealized hs _ ih => intro _ _; exact ih (hΔ _ _ hs).toV (fun _ h => by simp at h)
  | refInput _ => intro _ _; exact hI _ _
  | rep _ ih => intro hw hρ hc; exact ih hw hρ (.semInner hc)
  | mk _ ih => intro hw hρ hc; cases hc with | semInner hc' => exact ih hw hρ hc'
  | prim => intro _ _; exact applyPrim_noClo _ _ (fun _ h => by simp at h)
  | delayZero _ ih => intro hw hρ; exact ih hw.1 hρ
  | delaySucc _ ih => intro hw hρ; exact ih hw.2 hρ
  | syncZero _ ih => intro hw hρ; exact ih hw.1 hρ
  | syncSucc _ ih => intro hw hρ; exact ih hw.2 hρ
  | foldNil _ _ _ _ ihz _ => intro hw hρ; exact ihz hw.2.1 hρ
  | @foldCons _ _ _ _ _ vf vz x xs r v _ _ _ _ _ ihf ihz ihl ihr ihv =>
    intro hw hρ
    have hf := ihf hw.1 hρ
    have hz := ihz hw.2.1 hρ
    have hl := ihl hw.2.2 hρ
    have hxs : ∀ w ∈ [Value.list xs, vz, vf], w.NoClo := by
      intro w hw'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl | rfl
      · intro hc; cases hc with | listElem hm hc' => exact hl (.listElem (List.mem_cons_of_mem _ hm) hc')
      · exact hz
      · exact hf
    have hr := ihr (by simp [foldVarTerm, Expr.WiringV]) hxs
    refine ihv (by simp [stepVarTerm, Expr.WiringV]) ?_
    intro w hw'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl
    · exact hr
    · exact fun hc => hl (.listElem List.mem_cons_self hc)
    · exact hf

/-- Wiring designs never produce closures (any environment: a wiring term
    reads none). -/
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
  | foldNil _ _ _ _ ihz _ => intro hw; exact ihz hw.2.1
  | @foldCons _ _ _ _ _ vf vz x xs r v _ _ _ hr hv ihf ihz ihl _ _ =>
    intro hw
    have hf := ihf hw.1
    have hz := ihz hw.2.1
    have hl := ihl hw.2.2
    have hxs : ∀ w ∈ [Value.list xs, vz, vf], w.NoClo := by
      intro w hw'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl | rfl
      · intro hc; cases hc with | listElem hm hc' => exact hl (.listElem (List.mem_cons_of_mem _ hm) hc')
      · exact hz
      · exact hf
    have hr' := Ev.noCloV hΔ hI hr (by simp [foldVarTerm, Expr.WiringV]) hxs
    refine Ev.noCloV hΔ hI hv (by simp [stepVarTerm, Expr.WiringV]) ?_
    intro w hw'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl
    · exact hr'
    · exact fun hc => hl (.listElem List.mem_cons_self hc)
    · exact hf

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
  | foldNil _ _ _ ihf ihz ihl => intro hw ρ'; exact .foldNil (ihf hw.1 ρ') (ihz hw.2.1 ρ') (ihl hw.2.2 ρ')
  | foldCons _ _ _ hr hv ihf ihz ihl _ _ =>
    intro hw ρ'; exact .foldCons (ihf hw.1 ρ') (ihz hw.2.1 ρ') (ihl hw.2.2 ρ') hr hv

/-! ## Pure terms (Phase 9b): evaluation independent of design, input and tick

A *pure* term refers to no declaration and reads no earlier tick: the
fragment definitional library functions live in.  Its value in a pure
environment is the same in every design, at every tick, under every input
— the semantic half of library expansion (`Surface/Stdlib.lean`). -/

def _root_.BDL.Expr.Pure : Expr → Prop
  | .declRef _ => False
  | .delay _ _ => False
  | .sync _ _ _ => False
  | .lam _ b => b.Pure
  | .app f a => f.Pure ∧ a.Pure
  | .rep e => e.Pure
  | .mk _ e => e.Pure
  | .fold f z l => f.Pure ∧ z.Pure ∧ l.Pure
  | _ => True

instance : ∀ e : Expr, Decidable e.Pure
  | .var _ | .boolLit _ | .natLit _ | .prim _ => inferInstanceAs (Decidable True)
  | .declRef _ | .delay _ _ | .sync _ _ _ => inferInstanceAs (Decidable False)
  | .lam _ b => instDecidablePure b
  | .app f a =>
    have := instDecidablePure f
    have := instDecidablePure a
    inferInstanceAs (Decidable (f.Pure ∧ a.Pure))
  | .rep e => instDecidablePure e
  | .mk _ e => instDecidablePure e
  | .fold f z l =>
    have := instDecidablePure f
    have := instDecidablePure z
    have := instDecidablePure l
    inferInstanceAs (Decidable (f.Pure ∧ z.Pure ∧ l.Pure))

/-- A value whose closures (if any) have pure bodies and pure environments. -/
inductive Value.Pure : Value → Prop where
  | bool (b : Bool) : Value.Pure (.bool b)
  | nat (n : Nat) : Value.Pure (.nat n)
  | sem {s : SemanticId} {v : Value} : Value.Pure v → Value.Pure (.sem s v)
  | none : Value.Pure .none
  | some {v : Value} : Value.Pure v → Value.Pure (.some v)
  | clo {ρ : List Value} {body : Expr} : body.Pure → (∀ w ∈ ρ, Value.Pure w) → Value.Pure (.clo ρ body)
  | prim {p : Prim} {args : List Value} : (∀ w ∈ args, Value.Pure w) → Value.Pure (.prim p args)
  | list {vs : List Value} : (∀ w ∈ vs, Value.Pure w) → Value.Pure (.list vs)
  | pair {a b : Value} : Value.Pure a → Value.Pure b → Value.Pure (.pair a b)

/-- Closure-free values are pure. -/
theorem Value.Pure.of_noClo : ∀ {v : Value}, v.NoClo → v.Pure
  | .bool b, _ => .bool b
  | .nat n, _ => .nat n
  | .sem _ v, h => .sem (Value.Pure.of_noClo (v := v) fun hc => h (.semInner hc))
  | .none, _ => .none
  | .some v, h => .some (Value.Pure.of_noClo (v := v) fun hc => h (.someInner hc))
  | .clo _ _, h => (h (.clo _ _)).elim
  | .prim _ args, h => .prim fun w hw => Value.Pure.of_noClo fun hc => h (.primArg hw hc)
  | .list vs, h => .list fun w hw => Value.Pure.of_noClo fun hc => h (.listElem hw hc)
  | .pair a b, h => .pair (Value.Pure.of_noClo (v := a) fun hc => h (.pairFst hc))
      (Value.Pure.of_noClo (v := b) fun hc => h (.pairSnd hc))
termination_by v => sizeOf v
decreasing_by all_goals (simp_wf; (try omega); (try (have := List.sizeOf_lt_of_mem hw; omega)))

theorem Prim.compute_pure (p : Prim) (args : List Value) (h : ∀ v ∈ args, v.Pure) : (p.compute args).Pure := by
  unfold Prim.compute
  split <;> first
    | (exact .nat _)
    | (exact .bool _)
    | (exact .none)
    | (exact .list fun _ h => absurd h (List.not_mem_nil))
    | (exact .some (h _ List.mem_cons_self))
    | (exact h _ List.mem_cons_self)
    | (exact h _ (List.mem_cons_of_mem _ List.mem_cons_self))
    | (rename_i x d
       have hx := h (.some x) List.mem_cons_self
       cases hx with | some hx' => exact hx')
    | (rename_i c x y; cases c <;> simp only [Bool.false_eq_true, ↓reduceIte]
       · exact h y (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
       · exact h x (List.mem_cons_of_mem _ List.mem_cons_self))
    | (rename_i x xs
       have hl := h (.list (x :: xs)) List.mem_cons_self
       cases hl with | list hl' => exact .list fun w hw => hl' w (List.mem_cons_of_mem _ hw))
    | (rename_i x xs
       have hx := h x List.mem_cons_self
       have hl := h (.list xs) (List.mem_cons_of_mem _ List.mem_cons_self)
       cases hl with | list hl' => exact .list fun w hw => (List.mem_cons.mp hw).elim (fun e => e ▸ hx) (hl' w))
    | (rename_i k xs
       have hl := h (.list xs) (List.mem_cons_of_mem _ List.mem_cons_self)
       cases hl with | list hl' => exact .list fun w hw => hl' w (List.mem_of_mem_take hw))
    | (rename_i xs
       have hl := h (.list xs) List.mem_cons_self
       cases hl with | list hl' => exact .list fun w hw => hl' w (List.mem_reverse.mp hw))
    | (rename_i x xs
       have hl := h (.list (x :: xs)) List.mem_cons_self
       cases hl with | list hl' => exact .some (hl' x List.mem_cons_self))
    | (rename_i a b; exact .pair (h a List.mem_cons_self) (h b (List.mem_cons_of_mem _ List.mem_cons_self)))
    | (rename_i a b
       have hp := h (.pair a b) List.mem_cons_self
       cases hp with | pair ha _ => exact ha)
    | (rename_i a b
       have hp := h (.pair a b) List.mem_cons_self
       cases hp with | pair _ hb => exact hb)
    | (rename_i k xs
       have hl := h (.list xs) (List.mem_cons_of_mem _ List.mem_cons_self)
       cases hl with | list hl' => exact .list fun w hw => hl' w (List.mem_of_mem_drop hw))
    | (rename_i x
       have hx := h (.some x) List.mem_cons_self
       cases hx with | some hx' => exact .list fun w hw => by simp at hw; subst hw; exact hx')

theorem applyPrim_pure (p : Prim) (args : List Value) (h : ∀ v ∈ args, v.Pure) : (applyPrim p args).Pure := by
  unfold applyPrim; split
  · exact Prim.compute_pure p args h
  · exact .prim h

/-- **Pure evaluation is context-free**: a pure term in a pure environment
    has a pure value, and the same value in every design, input and tick. -/
theorem Ev.pure {Δ : DeclEnv} {I : Input} :
    ∀ {t : Nat} {ρ : List Value} {e : Expr} {v : Value}, Ev Δ I t ρ e v → e.Pure → (∀ w ∈ ρ, w.Pure) →
      v.Pure ∧ ∀ (Δ' : DeclEnv) (I' : Input) (t' : Nat), Ev Δ' I' t' ρ e v := by
  intro t ρ e v h
  induction h with
  | var hv => intro _ hρ; exact ⟨hρ _ (List.mem_of_getElem? hv), fun _ _ _ => .var hv⟩
  | boolLit => intro _ _; exact ⟨.bool _, fun _ _ _ => .boolLit⟩
  | natLit => intro _ _; exact ⟨.nat _, fun _ _ _ => .natLit⟩
  | lam => intro he hρ; exact ⟨.clo he hρ, fun _ _ _ => .lam⟩
  | appClo _ _ _ ihf iha ihb =>
    intro he hρ
    obtain ⟨hf, hf'⟩ := ihf he.1 hρ
    obtain ⟨ha, ha'⟩ := iha he.2 hρ
    cases hf with
    | clo hb hρ' =>
      obtain ⟨hv, hv'⟩ := ihb hb (fun w hw => (List.mem_cons.mp hw).elim (fun e => e ▸ ha) (hρ' w))
      exact ⟨hv, fun Δ' I' t' => .appClo (hf' Δ' I' t') (ha' Δ' I' t') (hv' Δ' I' t')⟩
  | appPrim _ _ ihf iha =>
    intro he hρ
    obtain ⟨hf, hf'⟩ := ihf he.1 hρ
    obtain ⟨ha, ha'⟩ := iha he.2 hρ
    cases hf with
    | prim hargs =>
      refine ⟨applyPrim_pure _ _ ?_, fun Δ' I' t' => .appPrim (hf' Δ' I' t') (ha' Δ' I' t')⟩
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hargs w hw
      · simp at hw; subst hw; exact ha
  | refRealized _ _ _ => intro he; exact he.elim
  | refInput _ => intro he; exact he.elim
  | rep _ ih =>
    intro he hρ
    obtain ⟨hv, hv'⟩ := ih he hρ
    cases hv with
    | sem hw => exact ⟨hw, fun Δ' I' t' => .rep (hv' Δ' I' t')⟩
  | mk _ ih =>
    intro he hρ
    obtain ⟨hv, hv'⟩ := ih he hρ
    exact ⟨.sem hv, fun Δ' I' t' => .mk (hv' Δ' I' t')⟩
  | prim => intro _ _; exact ⟨applyPrim_pure _ _ (fun _ h => by simp at h), fun _ _ _ => .prim⟩
  | delayZero _ _ => intro he; exact he.elim
  | delaySucc _ _ => intro he; exact he.elim
  | syncZero _ _ => intro he; exact he.elim
  | syncSucc _ _ => intro he; exact he.elim
  | foldNil _ _ _ ihf ihz ihl =>
    intro he hρ
    obtain ⟨_, hf'⟩ := ihf he.1 hρ
    obtain ⟨hz, hz'⟩ := ihz he.2.1 hρ
    obtain ⟨_, hl'⟩ := ihl he.2.2 hρ
    exact ⟨hz, fun Δ' I' t' => .foldNil (hf' Δ' I' t') (hz' Δ' I' t') (hl' Δ' I' t')⟩
  | @foldCons _ _ _ _ _ vf vz x xs r v _ _ _ _ _ ihf ihz ihl ihr ihv =>
    intro he hρ
    obtain ⟨hf, hf'⟩ := ihf he.1 hρ
    obtain ⟨hz, hz'⟩ := ihz he.2.1 hρ
    obtain ⟨hl, hl'⟩ := ihl he.2.2 hρ
    have hxs : ∀ w ∈ [Value.list xs, vz, vf], w.Pure := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · cases hl with | list hl'' => exact .list fun w hw => hl'' w (List.mem_cons_of_mem _ hw)
      · exact hz
      · exact hf
    obtain ⟨hr, hr'⟩ := ihr (by simp [foldVarTerm, Expr.Pure]) hxs
    have hrs : ∀ w ∈ [r, x, vf], w.Pure := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact hr
      · cases hl with | list hl'' => exact hl'' _ List.mem_cons_self
      · exact hf
    obtain ⟨hv, hv'⟩ := ihv (by simp [stepVarTerm, Expr.Pure]) hrs
    exact ⟨hv, fun Δ' I' t' => .foldCons (hf' Δ' I' t') (hz' Δ' I' t') (hl' Δ' I' t') (hr' Δ' I' t') (hv' Δ' I' t')⟩

/-- The recursor's environment-passing sub-derivations move between designs
    whenever the passed values are closure-free. -/
theorem Ev.foldVar_move {Δ Δ' : DeclEnv} {I I' : Input} {t t' : Nat} {ρ : List Value} {v : Value}
    (h : Ev Δ I t ρ foldVarTerm v) (hρ : ∀ w ∈ ρ, w.NoClo) : Ev Δ' I' t' ρ foldVarTerm v :=
  (Ev.pure h (by simp [foldVarTerm, Expr.Pure]) (fun w hw => Value.Pure.of_noClo (hρ w hw))).2 Δ' I' t'

theorem Ev.stepVar_move {Δ Δ' : DeclEnv} {I I' : Input} {t t' : Nat} {ρ : List Value} {v : Value}
    (h : Ev Δ I t ρ stepVarTerm v) (hρ : ∀ w ∈ ρ, w.NoClo) : Ev Δ' I' t' ρ stepVarTerm v :=
  (Ev.pure h (by simp [stepVarTerm, Expr.Pure]) (fun w hw => Value.Pure.of_noClo (hρ w hw))).2 Δ' I' t'

theorem foldEnv_noClo {vf vz x : Value} {xs : List Value} (hf : vf.NoClo) (hz : vz.NoClo)
    (hl : (Value.list (x :: xs)).NoClo) : (∀ w ∈ [Value.list xs, vz, vf], w.NoClo) ∧ x.NoClo := by
  refine ⟨?_, fun hc => hl (.listElem List.mem_cons_self hc)⟩
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · intro hc; cases hc with | listElem hm hc' => exact hl (.listElem (List.mem_cons_of_mem _ hm) hc')
  · exact hz
  · exact hf

theorem stepEnv_noClo {r x vf : Value} (hr : r.NoClo) (hx : x.NoClo) (hf : vf.NoClo) :
    ∀ w ∈ [r, x, vf], w.NoClo := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact hr
  · exact hx
  · exact hf

/-- Moving a `foldCons` evaluation between designs: given the three
    operands' evaluations in the target design and closure-free values, the
    environment-passing sub-derivations transfer. -/
theorem Ev.foldCons_move {Δ Δ' : DeclEnv} {I I' : Input} {t t' : Nat} {ρ' : List Value} {f' z' l' : Expr}
    {vf vz x r v : Value} {xs : List Value}
    (hf' : Ev Δ' I' t' ρ' f' vf) (hz' : Ev Δ' I' t' ρ' z' vz) (hl' : Ev Δ' I' t' ρ' l' (.list (x :: xs)))
    (hr : Ev Δ I t [.list xs, vz, vf] foldVarTerm r) (hv : Ev Δ I t [r, x, vf] stepVarTerm v)
    (hΔ : DeclEnvWiring Δ) (hI : ∀ d t, (I d t).NoClo)
    (hvf : vf.NoClo) (hvz : vz.NoClo) (hvl : (Value.list (x :: xs)).NoClo) :
    Ev Δ' I' t' ρ' (.fold f' z' l') v := by
  obtain ⟨hxs, hx⟩ := foldEnv_noClo hvf hvz hvl
  have hrn : r.NoClo := Ev.noCloV hΔ hI hr (by simp [foldVarTerm, Expr.WiringV]) hxs
  exact .foldCons hf' hz' hl' (Ev.foldVar_move hr hxs) (Ev.stepVar_move hv (stepEnv_noClo hrn hx hvf))

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
  | fold _ _ _ ihf ihz ihl => exact ⟨ihf hw.1, ihz hw.2.1, ihl hw.2.2⟩

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
  | fold _ _ _ ihf ihz ihl =>
    intro t ρ v h
    cases h with
    | foldNil hf hz hl => exact .foldNil (ihf hw.1 _ _ _ hf) (ihz hw.2.1 _ _ _ hz) (ihl hw.2.2 _ _ _ hl)
    | foldCons hf hz hl hr hv =>
      exact .foldCons (ihf hw.1 _ _ _ hf) (ihz hw.2.1 _ _ _ hz) (ihl hw.2.2 _ _ _ hl) hr hv

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
