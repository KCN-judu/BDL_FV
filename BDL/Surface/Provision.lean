import BDL.Core.Clock
import BDL.Core.Output
import BDL.Core.Env
import BDL.Surface.UnitDomain

/-!
# Phase 13 — Source provision by device transducers (PRP-0001, audited)

Production proposal PRP-0001 (`KCN-judu/BDL` `876005c`): a Source
`s : () -> C` is, at deployment, a raw peripheral reading `r : () -> R`
composed with a device's transfer function `R -> rep(C)`, and the design
cannot tell the difference.  This module tests that hypothesis as a
*construction over designs* — no `Ty`, `Expr`, typing, grant, clock or
evaluation rule is added — and records where the proposal's claims had to
be corrected.

## What is defined

* `Channel` — one transducer from the raw reading to a representation:
  `rep`, the term `tr`, and its *transfer function* `transfer` on values,
  with the coherence `computes` (the term computes the function on every
  raw-typed value).  The term is required **pure** (`Expr.Pure`): no
  `declRef`, `delay`, `sync`.  Typing at `raw -> rep` under `Grant.none` is
  `Channel.WF`.
* `DeviceProfile` — `raw` (sem-free data) and a list of channels.  The
  profile mentions no concept; the Source's own signature supplies the
  grant (`grant_of_sem`).
* `Provision` — one fresh raw declaration `r`, its clock, and the assignment
  `chan : DeclId → Option Channel` of channels to target Sources.  Shared
  raw, several targets: the singleton is the case of one target
  (`Provision.one`).
* `provision Δ P` — `r` added unresolved at `raw`; every target `s` keeps
  its id and interface and gains the realization `mk c (tr r)` (at `sem c`)
  or `tr r` (at a representation type).  `provisionΚ`.
* `induced Δ P I'` — the abstract input a raw input determines:
  `I s t = wrap (transfer (I' r t))` at targets, `I' d t` elsewhere.
-/

namespace BDL.Provision
open BDL BDL.Reactive BDL.Clock BDL.Output BDL.UnitDomain

/-! ## Pure terms: what purity buys -/

theorem _root_.BDL.Expr.Pure.refs_nil : ∀ {e : Expr}, e.Pure → e.refs = []
  | .var _, _ | .boolLit _, _ | .natLit _, _ | .prim _, _ => rfl
  | .lam _ b, h => Expr.Pure.refs_nil (e := b) h
  | .app f a, h => by simp [Expr.refs, Expr.Pure.refs_nil (e := f) h.1, Expr.Pure.refs_nil (e := a) h.2]
  | .declRef _, h => h.elim
  | .rep e, h => Expr.Pure.refs_nil (e := e) h
  | .mk _ e, h => Expr.Pure.refs_nil (e := e) h
  | .delay _ _, h => h.elim
  | .sync _ _ _, h => h.elim
  | .fold f z l, h => by
    simp [Expr.refs, Expr.Pure.refs_nil (e := f) h.1, Expr.Pure.refs_nil (e := z) h.2.1,
      Expr.Pure.refs_nil (e := l) h.2.2]

theorem _root_.BDL.Expr.Pure.instRefs_nil : ∀ {e : Expr}, e.Pure → e.instRefs = []
  | .var _, _ | .boolLit _, _ | .natLit _, _ | .prim _, _ => rfl
  | .lam _ b, h => Expr.Pure.instRefs_nil (e := b) h
  | .app f a, h => by
    simp [Expr.instRefs, Expr.Pure.instRefs_nil (e := f) h.1, Expr.Pure.instRefs_nil (e := a) h.2]
  | .declRef _, h => h.elim
  | .rep e, h => Expr.Pure.instRefs_nil (e := e) h
  | .mk _ e, h => Expr.Pure.instRefs_nil (e := e) h
  | .delay _ _, h => h.elim
  | .sync _ _ _, h => h.elim
  | .fold f z l, h => by
    simp [Expr.instRefs, Expr.Pure.instRefs_nil (e := f) h.1, Expr.Pure.instRefs_nil (e := z) h.2.1,
      Expr.Pure.instRefs_nil (e := l) h.2.2]

theorem _root_.BDL.Expr.Pure.refFree {e : Expr} (h : e.Pure) : e.RefFree := Expr.Pure.refs_nil h

/-- A pure term is clocked in every domain: it mentions no declaration and
    holds no memory. -/
theorem _root_.BDL.Expr.Pure.clocked (Κ : ClockEnv) (c : Option ClockId) : ∀ {e : Expr}, e.Pure → clockedB Κ c e = true
  | .var _, _ | .boolLit _, _ | .natLit _, _ | .prim _, _ => by cases c <;> rfl
  | .lam _ b, h => by
    have := Expr.Pure.clocked Κ c (e := b) h
    cases c <;> simpa [clockedB] using this
  | .app f a, h => by
    have hf := Expr.Pure.clocked Κ c (e := f) h.1
    have ha := Expr.Pure.clocked Κ c (e := a) h.2
    cases c <;> simp [clockedB, hf, ha] at *
  | .declRef _, h => h.elim
  | .rep e, h => by
    have := Expr.Pure.clocked Κ c (e := e) h
    cases c <;> simpa [clockedB] using this
  | .mk _ e, h => by
    have := Expr.Pure.clocked Κ c (e := e) h
    cases c <;> simpa [clockedB] using this
  | .delay _ _, h => h.elim
  | .sync _ _ _, h => h.elim
  | .fold f z l, h => by
    have hf := Expr.Pure.clocked Κ c (e := f) h.1
    have hz := Expr.Pure.clocked Κ c (e := z) h.2.1
    have hl := Expr.Pure.clocked Κ c (e := l) h.2.2
    cases c <;> simp [clockedB, hf, hz, hl] at *

/-! ## Values whose closures satisfy a property

`Value.All P v`: every closure body inside `v` satisfies `P`.  `Value.Pure`
is the instance `P = Expr.Pure`; the observation boundary below uses
`P = (r ∉ ·.refs)`.  The three lemmas mirror `Value.Pure.of_noClo`,
`Prim.compute_pure` and `applyPrim_pure`. -/

inductive Value.All (P : Expr → Prop) : Value → Prop where
  | bool (b : Bool) : Value.All P (.bool b)
  | nat (n : Nat) : Value.All P (.nat n)
  | sem {s : SemanticId} {v : Value} : Value.All P v → Value.All P (.sem s v)
  | none : Value.All P .none
  | some {v : Value} : Value.All P v → Value.All P (.some v)
  | clo {ρ : List Value} {body : Expr} : P body → (∀ w ∈ ρ, Value.All P w) → Value.All P (.clo ρ body)
  | prim {p : Prim} {args : List Value} : (∀ w ∈ args, Value.All P w) → Value.All P (.prim p args)
  | list {vs : List Value} : (∀ w ∈ vs, Value.All P w) → Value.All P (.list vs)
  | pair {a b : Value} : Value.All P a → Value.All P b → Value.All P (.pair a b)

theorem Value.All.of_noClo {P : Expr → Prop} : ∀ {v : Value}, v.NoClo → Value.All P v
  | .bool b, _ => .bool b
  | .nat n, _ => .nat n
  | .sem _ v, h => .sem (Value.All.of_noClo (v := v) fun hc => h (.semInner hc))
  | .none, _ => .none
  | .some v, h => .some (Value.All.of_noClo (v := v) fun hc => h (.someInner hc))
  | .clo _ _, h => (h (.clo _ _)).elim
  | .prim _ args, h => .prim fun w hw => Value.All.of_noClo fun hc => h (.primArg hw hc)
  | .list vs, h => .list fun w hw => Value.All.of_noClo fun hc => h (.listElem hw hc)
  | .pair a b, h => .pair (Value.All.of_noClo (v := a) fun hc => h (.pairFst hc))
      (Value.All.of_noClo (v := b) fun hc => h (.pairSnd hc))
termination_by v => sizeOf v
decreasing_by all_goals (simp_wf; (try omega); (try (have := List.sizeOf_lt_of_mem hw; omega)))

theorem Value.All.of_pure {P : Expr → Prop} (hP : ∀ e, e.Pure → P e) : ∀ {v : Value}, v.Pure → Value.All P v
  | _, .bool b => .bool b
  | _, .nat n => .nat n
  | _, .sem h => .sem (Value.All.of_pure hP h)
  | _, .none => .none
  | _, .some h => .some (Value.All.of_pure hP h)
  | _, .clo hb hρ => .clo (hP _ hb) fun w hw => Value.All.of_pure hP (hρ w hw)
  | _, .prim hargs => .prim fun w hw => Value.All.of_pure hP (hargs w hw)
  | _, .list hvs => .list fun w hw => Value.All.of_pure hP (hvs w hw)
  | _, .pair ha hb => .pair (Value.All.of_pure hP ha) (Value.All.of_pure hP hb)

theorem Prim.compute_all {P : Expr → Prop} (p : Prim) (args : List Value) (h : ∀ v ∈ args, Value.All P v) :
    Value.All P (p.compute args) := by
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

theorem applyPrim_all {P : Expr → Prop} (p : Prim) (args : List Value) (h : ∀ v ∈ args, Value.All P v) :
    Value.All P (applyPrim p args) := by
  unfold applyPrim; split
  · exact Prim.compute_all p args h
  · exact .prim h

/-! ## Pure single-domain evaluation is multi-domain evaluation -/

/-- A pure term evaluated in a pure environment has the same derivation in
    every domain of every schedule: `Ev` and `MEv` coincide on it. -/
theorem MEv.of_ev_pure {Δ : DeclEnv} {I : Input} {S : Sched} {Δ' : DeclEnv} {I' : Input} {c : ClockId} {t' : Nat} :
    ∀ {t : Nat} {ρ : List Value} {e : Expr} {v : Value}, Ev Δ I t ρ e v → e.Pure → (∀ w ∈ ρ, w.Pure) →
      MEv S Δ' I' c t' ρ e v := by
  intro t ρ e v h
  induction h with
  | var hv => intro _ _; exact .var hv
  | boolLit => intro _ _; exact .boolLit
  | natLit => intro _ _; exact .natLit
  | lam => intro _ _; exact .lam
  | appClo hf ha _ ihf iha ihb =>
    intro he hρ
    have hfp := (Ev.pure hf he.1 hρ).1
    have hap := (Ev.pure ha he.2 hρ).1
    cases hfp with
    | clo hb hρ' =>
      exact .appClo (ihf he.1 hρ) (iha he.2 hρ)
        (ihb hb (fun w hw => (List.mem_cons.mp hw).elim (fun e => e ▸ hap) (hρ' w)))
  | appPrim _ _ ihf iha => intro he hρ; exact .appPrim (ihf he.1 hρ) (iha he.2 hρ)
  | refRealized _ _ _ => intro he; exact he.elim
  | refInput _ => intro he; exact he.elim
  | rep _ ih => intro he hρ; exact .rep (ih he hρ)
  | mk _ ih => intro he hρ; exact .mk (ih he hρ)
  | prim => intro _ _; exact .prim
  | delayZero _ _ => intro he; exact he.elim
  | delaySucc _ _ => intro he; exact he.elim
  | syncZero _ _ => intro he; exact he.elim
  | syncSucc _ _ => intro he; exact he.elim
  | foldNil _ _ _ ihf ihz ihl => intro he hρ; exact .foldNil (ihf he.1 hρ) (ihz he.2.1 hρ) (ihl he.2.2 hρ)
  | @foldCons _ _ _ _ _ vf vz x xs r v hf hz hl hr _ ihf ihz ihl ihr ihv =>
    intro he hρ
    have hfp := (Ev.pure hf he.1 hρ).1
    have hzp := (Ev.pure hz he.2.1 hρ).1
    have hlp := (Ev.pure hl he.2.2 hρ).1
    have hxs : ∀ w ∈ [Value.list xs, vz, vf], w.Pure := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · cases hlp with | list hl'' => exact .list fun w hw => hl'' w (List.mem_cons_of_mem _ hw)
      · exact hzp
      · exact hfp
    have hrp := (Ev.pure hr (by simp [foldVarTerm, Expr.Pure]) hxs).1
    have hrs : ∀ w ∈ [r, x, vf], w.Pure := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact hrp
      · cases hlp with | list hl'' => exact hl'' _ List.mem_cons_self
      · exact hfp
    exact .foldCons (ihf he.1 hρ) (ihz he.2.1 hρ) (ihl he.2.2 hρ)
      (ihr (by simp [foldVarTerm, Expr.Pure]) hxs) (ihv (by simp [stepVarTerm, Expr.Pure]) hrs)

/-! ## Transducers -/

/-- `Transduces tr v w`: the closed term `tr` applied to the value `v`
    yields `w`.  Stated as one evaluation in the empty design whose input
    is constantly `v`, so that it is checkable by `evalF` for concrete
    values; `Transduces.mev` moves it to any design, input, domain and tick
    when `tr` is pure and `v` closure-free. -/
def Transduces (tr : Expr) (v w : Value) : Prop :=
  Ev DeclEnv.empty (fun _ _ => v) 0 [] (.app tr (.declRef ⟨0⟩)) w

theorem Transduces.det {tr : Expr} {v w₁ w₂ : Value} (h₁ : Transduces tr v w₁) (h₂ : Transduces tr v w₂) :
    w₁ = w₂ := Ev.det h₁ h₂

theorem Ev.declRef_unresolved {Δ : DeclEnv} {I : Input} {t : Nat} {ρ : List Value} {d : DeclId} {v : Value}
    (h : Ev Δ I t ρ (.declRef d) v) (hn : Δ.realizationOf d = none) : v = I d t := by
  cases h with
  | refRealized hs _ => rw [hs] at hn; exact nomatch hn
  | refInput _ => rfl

/-- The result of a pure transducer on a closure-free value is pure. -/
theorem Transduces.pure {tr : Expr} (htr : tr.Pure) {v w : Value} (hv : v.NoClo) (h : Transduces tr v w) : w.Pure := by
  unfold Transduces at h
  cases h with
  | appClo hf ha hb =>
    have hfp := (Ev.pure hf htr (fun _ h => by simp at h)).1
    have hva : _ = v := Ev.declRef_unresolved ha rfl
    rw [hva] at hb
    cases hfp with
    | clo hbp hρ' =>
      exact (Ev.pure hb hbp (fun w hw => (List.mem_cons.mp hw).elim (fun e => e ▸ Value.Pure.of_noClo hv) (hρ' w))).1
  | appPrim hf ha =>
    have hfp := (Ev.pure hf htr (fun _ h => by simp at h)).1
    have hva : _ = v := Ev.declRef_unresolved ha rfl
    rw [hva]
    cases hfp with
    | prim hargs =>
      refine applyPrim_pure _ _ ?_
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hargs w hw
      · simp at hw; subst hw; exact Value.Pure.of_noClo hv

/-- **`Transduces.mev`**: a pure transducer applied, at top level, to any
    term evaluating to a closure-free `v` yields `w` in every design, input,
    domain and tick.  (Top level — the empty environment — is where a
    realization is evaluated, `MEv.refRealized`.) -/
theorem Transduces.mev {tr : Expr} (htr : tr.Pure) {v w : Value} (hv : v.NoClo) (h : Transduces tr v w)
    {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat} {e : Expr}
    (he : MEv S Δ I c t [] e v) : MEv S Δ I c t [] (.app tr e) w := by
  unfold Transduces at h
  cases h with
  | appClo hf ha hb =>
    have hfp := Ev.pure hf htr (fun _ h => by simp at h)
    have hva : _ = v := Ev.declRef_unresolved ha rfl
    rw [hva] at hb
    cases hfp.1 with
    | clo hbp hρ' =>
      have hρv : ∀ w ∈ v :: _, w.Pure := fun w hw =>
        (List.mem_cons.mp hw).elim (fun e => e ▸ Value.Pure.of_noClo hv) (hρ' w)
      have hf' : MEv S Δ I c t [] tr (.clo _ _) :=
        MEv.of_ev_pure (hfp.2 Δ I t) htr (fun _ h => by simp at h)
      exact .appClo hf' he (MEv.of_ev_pure hb hbp hρv)
  | appPrim hf ha =>
    have hfp := Ev.pure hf htr (fun _ h => by simp at h)
    have hva : _ = v := Ev.declRef_unresolved ha rfl
    rw [hva]
    have hf' : MEv S Δ I c t [] tr (.prim _ _) :=
      MEv.of_ev_pure (hfp.2 Δ I t) htr (fun _ h => by simp at h)
    exact .appPrim hf' he

/-- A binary primitive applied to two evaluated arguments computes. -/
theorem Ev.prim2 {Δ : DeclEnv} {I : Input} {t : Nat} {ρ : List Value} {p : Prim} (h2 : p.arity = 2)
    {a b : Expr} {va vb : Value} (ha : Ev Δ I t ρ a va) (hb : Ev Δ I t ρ b vb) :
    Ev Δ I t ρ (.app (.app (.prim p) a) b) (p.compute [va, vb]) := by
  have h1 : Ev Δ I t ρ (.app (.prim p) a) (.prim p [va]) := by
    have := Ev.appPrim (Δ := Δ) (I := I) (t := t) (ρ := ρ) (f := .prim p) (a := a) (p := p) (args := []) (va := va)
      (by simpa [applyPrim, h2] using (Ev.prim (Δ := Δ) (I := I) (t := t) (ρ := ρ) (p := p))) ha
    simpa [applyPrim, h2] using this
  have := Ev.appPrim h1 hb
  simpa [applyPrim, h2] using this

/-! ## Raw and representation values -/

/-- A value of a sem-free data type: the logical relation at that type,
    which does not depend on the application relation (`RedSF_data`). -/
def TyVal (τ : Ty) (v : Value) : Prop := RedSF (fun _ _ _ => False) τ v

theorem TyVal.noClo : ∀ {τ : Ty}, τ.Data → ∀ {v : Value}, TyVal τ v → v.NoClo
  | .bool, _, _, ⟨b, h⟩ => by subst h; intro hc; cases hc
  | .nat, _, _, ⟨n, h⟩ => by subst h; intro hc; cases hc
  | .q _, _, _, ⟨n, h⟩ => by subst h; intro hc; cases hc
  | .sem _, _, _, h => h.elim
  | .arr _ _, hd, _, _ => hd.elim
  | .opt τ, hd, v, h => by
    rcases h with rfl | ⟨w, rfl, hw⟩
    · intro hc; cases hc
    · intro hc; cases hc with | someInner hc' => exact TyVal.noClo (τ := τ) hd hw hc'
  | .list τ, hd, v, h => by
    obtain ⟨vs, rfl, hvs⟩ := h
    intro hc; cases hc with | listElem hm hc' => exact TyVal.noClo (τ := τ) hd (hvs _ hm) hc'
  | .prod a b, hd, v, h => by
    obtain ⟨x, y, rfl, hx, hy⟩ := h
    intro hc
    cases hc with
    | pairFst hc' => exact TyVal.noClo (τ := a) hd.1 hx hc'
    | pairSnd hc' => exact TyVal.noClo (τ := b) hd.2 hy hc'

/-! ## Device profiles -/

/-- One **channel** of a device: the transducer from the raw reading to a
    representation.  `transfer` is the transfer function (what the data
    sheet says); `tr` is the BDL term that computes it (what the compiler
    compiles); `computes` ties them on every raw-typed value.  The term is
    pure: it reads no declaration, no earlier tick, no other domain. -/
structure Channel (raw : Ty) where
  rep : Ty
  tr : Expr
  transfer : Value → Value
  rep_semFree : rep.SemFree
  rep_data : rep.Data
  tr_pure : tr.Pure
  computes : ∀ v, TyVal raw v → Transduces tr v (transfer v)

/-- The channel's term is typed at `raw -> rep` under **no** grant: a
    profile constructs no concept. -/
def Channel.WF (Θ : ConceptEnv) {raw : Ty} (ch : Channel raw) : Prop :=
  HasType Θ DeclEnv.empty Grant.none [] ch.tr (.arr raw ch.rep)

/-- A **device profile**: the raw reading's type and the channels it
    offers.  No concept, no declaration, no clock: a catalog entry. -/
structure DeviceProfile where
  raw : Ty
  raw_semFree : raw.SemFree
  raw_data : raw.Data
  channels : List (Channel raw)

/-- **`channel_constructs_nothing`** (the grant boundary, one half): a
    well-formed channel term constructs no semantic concept whatsoever —
    `Grant.none` admits no `mk`. -/
theorem channel_constructs_nothing {Θ : ConceptEnv} {raw : Ty} {ch : Channel raw} (h : ch.WF Θ) :
    ∀ c, ¬ ch.tr.constructs c :=
  fun c hc => h.constructs_granted c hc

/-- **`grant_of_sem`** (the other half): a declaration whose expected type
    is `sem c` is realized under the grant `{c}` and nothing else — the
    grant a provisioned Source uses for its `mk c` is its own signature's. -/
theorem grant_of_sem (c s : SemanticId) : Grant.of (.sem c) s ↔ s = c := by
  simp [Grant.of, Ty.grant]

/-- Where the grant is used: a realized declaration's body is checked under
    `Grant.of` its expected type (`Satisfies`, `GlobalWF`). -/
theorem realization_checked_under_own_grant {ev : Evidence} {Θ : ConceptEnv} {Δ : DeclEnv}
    (g : GlobalWF ev Θ Δ) {s : DeclId} {h : DesignDecl} (hs : Δ s = some h) {e : Expr}
    (he : h.realization = some e) :
    HasType Θ Δ (Grant.of h.interface.expectedType) [] e h.interface.expectedType :=
  ((g s h hs).2 e he).1

/-! ## Fitting -/

/-- `Fits Θ τ ch`: the channel produces the Source's values.  At `sem c`
    the concept's representation is the channel's; at a representation
    type the types coincide.  Nothing else fits. -/
def Fits (Θ : ConceptEnv) (τ : Ty) {raw : Ty} (ch : Channel raw) : Prop :=
  match τ with
  | .sem c => Θ c = some ch.rep
  | τ => τ = ch.rep

instance (Θ : ConceptEnv) (τ : Ty) {raw : Ty} (ch : Channel raw) : Decidable (Fits Θ τ ch) := by
  unfold Fits
  cases τ <;> exact inferInstance

/-- The realization a target receives: `mk c (tr r)` at `sem c`, `tr r`
    elsewhere.  `r` is the kernel identity of the raw declaration; its
    canonical type is `() -> raw`, its kernel type `raw` (Phase 12). -/
def realizeAt (τ : Ty) (tr : Expr) (r : DeclId) : Expr :=
  match τ with
  | .sem c => .mk c (.app tr (.declRef r))
  | _ => .app tr (.declRef r)

/-- The value such a realization produces from a transferred raw value. -/
def wrapAt (τ : Ty) (w : Value) : Value :=
  match τ with
  | .sem c => .sem c w
  | _ => w

def unwrapAt (τ : Ty) (v : Value) : Value :=
  match τ, v with
  | .sem _, .sem _ w => w
  | _, v => v

/-! ## Provision -/

/-- A **provision**: one fresh raw declaration `r` read in domain `clock`,
    and the assignment of channels to the Sources it provisions.  Several
    targets may share the one raw reading (an IMU register image feeding
    pitch, roll and acceleration); one target is the singleton case. -/
structure Provision (raw : Ty) where
  r : DeclId
  clock : Option ClockId
  chan : DeclId → Option (Channel raw)

/-- The singleton provision. -/
def Provision.one {raw : Ty} (r s : DeclId) (clock : Option ClockId) (ch : Channel raw) : Provision raw :=
  ⟨r, clock, fun d => if d = s then some ch else none⟩

/-- **The construction.**  `r` is added unresolved at `raw`; a target keeps
    its identity and interface and gains the realization; everything else
    is untouched.  Total on environments; its preconditions are `WF`. -/
def provision {raw : Ty} (Δ : DeclEnv) (P : Provision raw) : DeclEnv := fun d =>
  if d = P.r then some ⟨P.r, ⟨raw, []⟩, none⟩
  else match Δ d, P.chan d with
    | some h, some ch => some ⟨h.id, h.interface, some (realizeAt h.interface.expectedType ch.tr P.r)⟩
    | some h, none => some h
    | none, _ => none

def provisionΚ {raw : Ty} (Κ : ClockEnv) (P : Provision raw) : ClockEnv := fun d =>
  if d = P.r then P.clock else Κ d

/-- **The induced abstract input.**  A raw input `I'` determines the input
    the abstract design sees: at a target, the transferred (and wrapped)
    raw value; elsewhere `I'` itself. -/
def induced {raw : Ty} (Δ : DeclEnv) (P : Provision raw) (I' : Input) : Input := fun d t =>
  match P.chan d, Δ.tyView d with
  | some ch, some τ => wrapAt τ (ch.transfer (I' P.r t))
  | _, _ => I' d t

/-- Preconditions of a provision: `r` fresh; the raw type sem-free data;
    every target a declared, unresolved Source that the channel fits, with
    a well-typed channel. -/
structure WF (Θ : ConceptEnv) (Δ : DeclEnv) {raw : Ty} (P : Provision raw) : Prop where
  fresh : Δ P.r = none
  raw_semFree : raw.SemFree
  raw_data : raw.Data
  targets : ∀ s ch, P.chan s = some ch →
    ∃ h, Δ s = some h ∧ h.realization = none ∧ Fits Θ h.interface.expectedType ch ∧ ch.WF Θ

/-- Every target is read in the raw declaration's domain (the least
    commitment; a device with its own rate is a later `sync`). -/
def ClockWF {raw : Ty} (Κ : ClockEnv) (P : Provision raw) : Prop :=
  ∀ s ch, P.chan s = some ch → Κ s = P.clock

/-- The raw input is well-typed at `r` and closure-free everywhere. -/
def RawInput {raw : Ty} (P : Provision raw) (I' : Input) : Prop :=
  (∀ t, TyVal raw (I' P.r t)) ∧ ∀ d t, (I' d t).NoClo

/-- No realization of `Δ` mentions `r`. -/
def NoMention (Δ : DeclEnv) (r : DeclId) : Prop :=
  ∀ d b, Δ.realizationOf d = some b → r ∉ b.refs

/-- A globally well-typed design never mentions an undeclared identity. -/
theorem NoMention.of_globalWF {ev : Evidence} {Θ : ConceptEnv} {Δ : DeclEnv} (g : GlobalWF ev Θ Δ)
    {r : DeclId} (hr : Δ r = none) : NoMention Δ r := by
  intro d b hb hmem
  simp only [DeclEnv.realizationOf, Option.bind_eq_some_iff] at hb
  obtain ⟨h, hd, hre⟩ := hb
  obtain ⟨τ, hτ⟩ := ((g d h hd).2 b hre).1.refs_declared r hmem
  simp [DeclEnv.tyView, hr] at hτ

/-- Likewise, a term typed in `Δ` cannot name an undeclared identity — the
    observation boundary, stated over typing rather than syntax. -/
theorem typed_avoids {Θ : ConceptEnv} {Δ : DeclEnv} {G : Grant} {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : HasType Θ Δ G Γ e τ) {r : DeclId} (hr : Δ r = none) : r ∉ e.refs := by
  intro hmem
  obtain ⟨τ', hτ⟩ := h.refs_declared r hmem
  simp [DeclEnv.tyView, hr] at hτ

/-! ## Basic facts about the construction -/

section Basic
variable {raw : Ty} {Δ : DeclEnv} {P : Provision raw}

theorem provision_r : provision Δ P P.r = some ⟨P.r, ⟨raw, []⟩, none⟩ := by
  simp [provision]

theorem provision_target {s : DeclId} {h : DesignDecl} {ch : Channel raw} (hs : s ≠ P.r)
    (hh : Δ s = some h) (hc : P.chan s = some ch) :
    provision Δ P s = some ⟨h.id, h.interface, some (realizeAt h.interface.expectedType ch.tr P.r)⟩ := by
  simp [provision, hs, hh, hc]

theorem provision_other {d : DeclId} (hd : d ≠ P.r) (hc : P.chan d = none) : provision Δ P d = Δ d := by
  simp only [provision, hd, ↓reduceIte, hc]
  cases Δ d <;> rfl

theorem provision_tyView_r : (provision Δ P).tyView P.r = some raw := by
  simp [DeclEnv.tyView, provision_r]

theorem provision_tyView {d : DeclId} (hd : d ≠ P.r) : (provision Δ P).tyView d = Δ.tyView d := by
  simp only [DeclEnv.tyView, provision, hd, ↓reduceIte]
  cases Δ d <;> cases P.chan d <;> rfl

theorem provision_realizationOf_r : (provision Δ P).realizationOf P.r = none := by
  simp [DeclEnv.realizationOf, provision_r]

theorem provision_realizationOf_other {d : DeclId} (hd : d ≠ P.r) (hc : P.chan d = none) :
    (provision Δ P).realizationOf d = Δ.realizationOf d := by
  simp [DeclEnv.realizationOf, provision_other hd hc]

theorem provision_realizationOf_target {s : DeclId} {h : DesignDecl} {ch : Channel raw} (hs : s ≠ P.r)
    (hh : Δ s = some h) (hc : P.chan s = some ch) :
    (provision Δ P).realizationOf s = some (realizeAt h.interface.expectedType ch.tr P.r) := by
  simp [DeclEnv.realizationOf, provision_target hs hh hc]

theorem provisionΚ_r (Κ : ClockEnv) : provisionΚ Κ P P.r = P.clock := by simp [provisionΚ]
theorem provisionΚ_other (Κ : ClockEnv) {d : DeclId} (hd : d ≠ P.r) : provisionΚ Κ P d = Κ d := by
  simp [provisionΚ, hd]

theorem induced_target {I' : Input} {s : DeclId} {ch : Channel raw} {τ : Ty} (hc : P.chan s = some ch)
    (hτ : Δ.tyView s = some τ) (t : Nat) :
    induced Δ P I' s t = wrapAt τ (ch.transfer (I' P.r t)) := by
  simp [induced, hc, hτ]

theorem induced_other {I' : Input} {d : DeclId} (hc : P.chan d = none) (t : Nat) :
    induced Δ P I' d t = I' d t := by
  simp [induced, hc]

/-- A target is a declared identity distinct from `r`. -/
theorem WF.target_ne_r {Θ : ConceptEnv} (wf : WF Θ Δ P) {s : DeclId} {ch : Channel raw}
    (hc : P.chan s = some ch) : s ≠ P.r := by
  intro hsr
  obtain ⟨h, hh, _⟩ := wf.targets s ch hc
  rw [hsr, wf.fresh] at hh
  exact nomatch hh

theorem WF.r_not_target {Θ : ConceptEnv} (wf : WF Θ Δ P) : P.chan P.r = none := by
  cases hc : P.chan P.r with
  | none => rfl
  | some ch => exact absurd rfl (wf.target_ne_r hc)

end Basic

/-! ## Refinement, typing, well-formedness -/

section Refinement
variable {raw : Ty} {Θ : ConceptEnv} {Δ : DeclEnv} {P : Provision raw}

/-- **`provision_envRefines`**: provision is an environment refinement —
    every target keeps its id and interface and goes from unresolved to
    realized; `r` is new; nothing else moves. -/
theorem provision_envRefines (wf : WF Θ Δ P) : EnvRefines Δ (provision Δ P) := by
  intro d h hd
  have hdr : d ≠ P.r := by intro e; rw [e, wf.fresh] at hd; exact nomatch hd
  cases hc : P.chan d with
  | none => exact ⟨h, (provision_other hdr hc).trans hd, DeclLeq.refl h⟩
  | some ch =>
    obtain ⟨h', hh', hun, _, _⟩ := wf.targets d ch hc
    rw [hd] at hh'; cases hh'
    refine ⟨_, provision_target hdr hd hc, rfl, InterfaceRefines.refl _, ?_⟩
    intro e he; rw [hun] at he; exact nomatch he

/-- The type view is unchanged on every pre-existing identity. -/
theorem provision_tyView_eq (wf : WF Θ Δ P) {d : DeclId} {τ : Ty} (h : Δ.tyView d = some τ) :
    (provision Δ P).tyView d = some τ :=
  (provision_envRefines wf).tyView h

/-- The realization every target receives is typed at its interface under
    its own grant.  The channel term, typed under `Grant.none` in the empty
    design, is moved to the provisioned design because it is reference-free
    (`refFree_env_irrelevant`) and its grant is weakened (`mono_grant`). -/
theorem realizeAt_typed (wf : WF Θ Δ P) {s : DeclId} {h : DesignDecl} {ch : Channel raw}
    (hs : Δ s = some h) (hc : P.chan s = some ch) :
    HasType Θ (provision Δ P) (Grant.of h.interface.expectedType) []
      (realizeAt h.interface.expectedType ch.tr P.r) h.interface.expectedType := by
  obtain ⟨h', hh', _, hfit, hty⟩ := wf.targets s ch hc
  rw [hs] at hh'; cases hh'
  have htr : HasType Θ (provision Δ P) (Grant.of h.interface.expectedType) [] ch.tr (.arr raw ch.rep) :=
    (hty.refFree_env_irrelevant ch.tr_pure.refFree).mono_grant (fun _ hf => hf.elim)
  have hr : HasType Θ (provision Δ P) (Grant.of h.interface.expectedType) [] (.declRef P.r) raw :=
    .declRef provision_tyView_r
  unfold Fits at hfit
  generalize hτ : h.interface.expectedType = τ at *
  cases τ with
  | sem c =>
    simp only [realizeAt]
    exact .mk (by simp [Grant.of, Ty.grant]) hfit (.app htr hr)
  | bool | nat | arr _ _ | q _ | opt _ | list _ | prod _ _ =>
    simp only at hfit
    rw [← hfit] at htr
    simp only [realizeAt]
    exact .app htr hr

/-- **`provision_wf`**: the provisioned design is globally well formed,
    from: the abstract design well formed, monotone evidence (so the other
    declarations' evidence survives the refinement), the provision's
    preconditions, and — a hypothesis the proposal did not state — evidence
    for each target's *commitments* discharged by its new realization.  A
    Source's commitments become obligations on the profile. -/
theorem provision_wf {ev : Evidence} (mono : ev.Monotone) (g : GlobalWF ev Θ Δ) (wf : WF Θ Δ P)
    (hcomm : ∀ s ch h, P.chan s = some ch → Δ s = some h →
      ∀ p ∈ h.interface.commitments, ev (provision Δ P) (realizeAt h.interface.expectedType ch.tr P.r) p) :
    GlobalWF ev Θ (provision Δ P) := by
  have er := provision_envRefines wf
  intro d h hd
  by_cases hdr : d = P.r
  · subst hdr
    rw [provision_r] at hd; cases hd
    exact ⟨rfl, WellFormedDecl.unresolved _ _ _ _ _ _⟩
  cases hc : P.chan d with
  | none =>
    rw [provision_other hdr hc] at hd
    exact ⟨g.stored_id hd, (g.wellFormed hd).of_envRefines mono er⟩
  | some ch =>
    obtain ⟨h', hh', _, _, _⟩ := wf.targets d ch hc
    rw [provision_target hdr hh' hc] at hd
    rw [← Option.some.inj hd]
    have hid : h'.id = d := g.stored_id hh'
    have ht := realizeAt_typed wf hh' hc
    refine ⟨hid, ?_⟩
    intro e he
    simp only at he
    rw [← Option.some.inj he]
    exact ⟨ht, hcomm d ch h' hc hh'⟩

end Refinement

/-! ## Causality and clocks -/

section Causal
variable {raw : Ty} {Θ : ConceptEnv} {Δ : DeclEnv} {P : Provision raw}

theorem realizeAt_instRefs (τ : Ty) {tr : Expr} (htr : tr.Pure) (r : DeclId) :
    (realizeAt τ tr r).instRefs = [r] := by
  cases τ <;> simp [realizeAt, Expr.instRefs, Expr.Pure.instRefs_nil htr]

theorem realizeAt_refs (τ : Ty) {tr : Expr} (htr : tr.Pure) (r : DeclId) :
    (realizeAt τ tr r).refs = [r] := by
  cases τ <;> simp [realizeAt, Expr.refs, Expr.Pure.refs_nil htr]

/-- **`provision_causal`**: the instantaneous graph gains the edges
    `s → r` for each target and nothing else (purity: the channel term
    carries no reference), and `r` has no out-edges.  Ranks shift by one
    with `r` at the bottom. -/
theorem provision_causal (wf : WF Θ Δ P) (nm : NoMention Δ P.r) (hc : Causal Δ) : Causal (provision Δ P) := by
  obtain ⟨rank, R, hR, hedge⟩ := hc
  refine ⟨fun d => if d = P.r then 0 else rank d + 1, R + 1, ?_, ?_⟩
  · intro d; by_cases h : d = P.r
    · simp [h]
    · simp [h]; exact hR d
  · intro a b hab
    obtain ⟨e, he, hb⟩ := InstDependsOn.iff.mp hab
    by_cases har : a = P.r
    · subst har; rw [provision_realizationOf_r] at he; exact nomatch he
    cases hca : P.chan a with
    | none =>
      rw [provision_realizationOf_other har hca] at he
      have hab' : InstDependsOn Δ a b := InstDependsOn.iff.mpr ⟨e, he, hb⟩
      have hbr : b ≠ P.r := by
        intro e'; subst e'
        exact nm a _ he (InstDependsOn.toDependsOn.instRefs_sub hb)
      simp [har, hbr]
      exact hedge a b hab'
    | some ch =>
      obtain ⟨h, hh, _, _, _⟩ := wf.targets a ch hca
      rw [provision_realizationOf_target har hh hca] at he
      cases he
      rw [realizeAt_instRefs _ ch.tr_pure] at hb
      simp at hb; subst hb
      simp [har]

/-- The domain judgment consults the clock environment only at the term's
    references. -/
theorem clockedB_congr {Κ Κ' : ClockEnv} (h : ∀ d ∈ e.refs, Κ d = Κ' d) :
    ∀ c, clockedB Κ c e = clockedB Κ' c e := by
  induction e with
  | var _ | boolLit _ | natLit _ | prim _ => intro c; cases c <;> rfl
  | lam _ b ih => intro c; cases c <;> simp [clockedB, ih h]
  | app f a ihf iha =>
    intro c
    have hf := ihf (fun d hd => h d (by simp [Expr.refs, hd]))
    have ha := iha (fun d hd => h d (by simp [Expr.refs, hd]))
    cases c <;> simp [clockedB, hf, ha]
  | declRef d => intro c; cases c <;> simp [clockedB, h d (by simp [Expr.refs])]
  | rep e ih => intro c; cases c <;> simp [clockedB, ih h]
  | mk _ e ih => intro c; cases c <;> simp [clockedB, ih h]
  | delay i e ihi ihe =>
    intro c
    have hi := ihi (fun d hd => h d (by simp [Expr.refs, hd]))
    have he := ihe (fun d hd => h d (by simp [Expr.refs, hd]))
    cases c <;> simp [clockedB, hi, he]
  | sync _ i e ihi ihe =>
    intro c
    have hi := ihi (fun d hd => h d (by simp [Expr.refs, hd]))
    have he := ihe (fun d hd => h d (by simp [Expr.refs, hd]))
    cases c <;> simp [clockedB, hi, he]
  | fold f z l ihf ihz ihl =>
    intro c
    have hf := ihf (fun d hd => h d (by simp [Expr.refs, hd]))
    have hz := ihz (fun d hd => h d (by simp [Expr.refs, hd]))
    have hl := ihl (fun d hd => h d (by simp [Expr.refs, hd]))
    cases c <;> simp [clockedB, hf, hz, hl]

/-- **`provision_wellClocked`**: with `Κ' r = Κ s` for every target, the
    domain judgment is preserved: the new realization reads `r` in its own
    domain, the channel term is clocked everywhere, and no other
    realization mentions `r`.  No device clock is introduced. -/
theorem provision_wellClocked {Κ : ClockEnv} (wf : WF Θ Δ P) (cwf : ClockWF Κ P) (nm : NoMention Δ P.r)
    (hw : WellClocked Κ Δ) : WellClocked (provisionΚ Κ P) (provision Δ P) := by
  intro d b hb
  by_cases hdr : d = P.r
  · subst hdr; rw [provision_realizationOf_r] at hb; exact nomatch hb
  rw [provisionΚ_other Κ hdr]
  cases hc : P.chan d with
  | none =>
    rw [provision_realizationOf_other hdr hc] at hb
    have := hw d b hb
    unfold Clocked at *
    rw [← clockedB_congr (Κ := Κ) (Κ' := provisionΚ Κ P)]
    · exact this
    · intro x hx
      have hxr : x ≠ P.r := fun e => nm d b hb (e ▸ hx)
      simp [provisionΚ, hxr]
  | some ch =>
    obtain ⟨h, hh, _, _, _⟩ := wf.targets d ch hc
    rw [provision_realizationOf_target hdr hh hc] at hb
    cases hb
    have hk : provisionΚ Κ P P.r = Κ d := by rw [provisionΚ_r, cwf d ch hc]
    unfold Clocked
    cases hτ : h.interface.expectedType <;>
      simp [realizeAt, clockedB, Expr.Pure.clocked (provisionΚ Κ P) (Κ d) ch.tr_pure, hk] <;>
      (cases Κ d <;> simp [clockedB])

end Causal

/-! ## The simulation lemma

Two designs evaluate every term that does not mention `r` alike when every
declaration other than `r` is simulated: a realized declaration either has
the same `r`-free body on both sides, or its observations are matched
directly; an unresolved declaration's input is matched by an observation on
the other side.  The invariant carried through closures is `Avoids r`: no
closure body anywhere in a value mentions `r`. -/

/-- No closure inside the value mentions `r`. -/
def Avoids (r : DeclId) : Value → Prop := Value.All (fun b => r ∉ b.refs)

theorem Avoids.of_noClo {r : DeclId} {v : Value} (h : v.NoClo) : Avoids r v := Value.All.of_noClo h
theorem Avoids.of_pure {r : DeclId} {v : Value} (h : v.Pure) : Avoids r v :=
  Value.All.of_pure (fun _ he => by rw [Expr.Pure.refs_nil he]; simp) h

theorem simulate {S : Sched} {Δ₁ Δ₂ : DeclEnv} {I₁ I₂ : Input} (r : DeclId)
    (hreal : ∀ d, d ≠ r → ∀ body, Δ₁.realizationOf d = some body →
      (Δ₂.realizationOf d = some body ∧ r ∉ body.refs) ∨
      (∀ c t v, MEv S Δ₁ I₁ c t [] body v → MEv S Δ₂ I₂ c t [] (.declRef d) v ∧ Avoids r v))
    (hinp : ∀ d, d ≠ r → Δ₁.realizationOf d = none →
      ∀ c t, MEv S Δ₂ I₂ c t [] (.declRef d) (I₁ d t) ∧ Avoids r (I₁ d t)) :
    ∀ {c : ClockId} {t : Nat} {ρ : List Value} {e : Expr} {v : Value}, MEv S Δ₁ I₁ c t ρ e v →
      r ∉ e.refs → (∀ w ∈ ρ, Avoids r w) → MEv S Δ₂ I₂ c t ρ e v ∧ Avoids r v := by
  intro c t ρ e v h
  induction h with
  | var hv => intro _ hρ; exact ⟨.var hv, hρ _ (List.mem_of_getElem? hv)⟩
  | boolLit => intro _ _; exact ⟨.boolLit, .bool _⟩
  | natLit => intro _ _; exact ⟨.natLit, .nat _⟩
  | lam => intro he hρ; exact ⟨.lam, .clo he hρ⟩
  | appClo _ _ _ ihf iha ihb =>
    intro he hρ
    simp only [Expr.refs, List.mem_append, not_or] at he
    obtain ⟨hf, hfa⟩ := ihf he.1 hρ
    obtain ⟨ha, haa⟩ := iha he.2 hρ
    cases hfa with
    | clo hb hρ' =>
      obtain ⟨hv, hva⟩ := ihb hb (fun w hw => (List.mem_cons.mp hw).elim (fun e => e ▸ haa) (hρ' w))
      exact ⟨.appClo hf ha hv, hva⟩
  | appPrim _ _ ihf iha =>
    intro he hρ
    simp only [Expr.refs, List.mem_append, not_or] at he
    obtain ⟨hf, hfa⟩ := ihf he.1 hρ
    obtain ⟨ha, haa⟩ := iha he.2 hρ
    cases hfa with
    | prim hargs =>
      refine ⟨.appPrim hf ha, applyPrim_all _ _ ?_⟩
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hargs w hw
      · simp at hw; subst hw; exact haa
  | @refRealized c t ρ d b v hs hb ih =>
    intro he _
    have hdr : d ≠ r := by simp [Expr.refs] at he; exact fun e => he e.symm
    rcases hreal d hdr b hs with ⟨hs', hbr⟩ | hobs
    · obtain ⟨hv, hva⟩ := ih hbr (fun _ h => by simp at h)
      exact ⟨.refRealized hs' hv, hva⟩
    · obtain ⟨hv, hva⟩ := hobs c t v hb
      exact ⟨MEv.declRef_env_irrelevant hv, hva⟩
  | @refInput c t ρ d hn =>
    intro he _
    have hdr : d ≠ r := by simp [Expr.refs] at he; exact fun e => he e.symm
    obtain ⟨hv, hva⟩ := hinp d hdr hn c t
    exact ⟨MEv.declRef_env_irrelevant hv, hva⟩
  | rep _ ih =>
    intro he hρ
    obtain ⟨hv, hva⟩ := ih he hρ
    cases hva with
    | sem hw => exact ⟨.rep hv, hw⟩
  | mk _ ih =>
    intro he hρ
    obtain ⟨hv, hva⟩ := ih he hρ
    exact ⟨.mk hv, .sem hva⟩
  | prim => intro _ _; exact ⟨.prim, applyPrim_all _ _ (fun _ h => by simp at h)⟩
  | delayNone hp _ ih =>
    intro he hρ
    simp only [Expr.refs, List.mem_append, not_or] at he
    obtain ⟨hv, hva⟩ := ih he.1 hρ
    exact ⟨.delayNone hp hv, hva⟩
  | delaySome hp _ ih =>
    intro he hρ
    simp only [Expr.refs, List.mem_append, not_or] at he
    obtain ⟨hv, hva⟩ := ih he.2 hρ
    exact ⟨.delaySome hp hv, hva⟩
  | syncNone hp _ ih =>
    intro he hρ
    simp only [Expr.refs, List.mem_append, not_or] at he
    obtain ⟨hv, hva⟩ := ih he.1 hρ
    exact ⟨.syncNone hp hv, hva⟩
  | syncSome hp _ ih =>
    intro he hρ
    simp only [Expr.refs, List.mem_append, not_or] at he
    obtain ⟨hv, hva⟩ := ih he.2 hρ
    exact ⟨.syncSome hp hv, hva⟩
  | foldNil _ _ _ ihf ihz ihl =>
    intro he hρ
    simp only [Expr.refs, List.mem_append, not_or] at he
    obtain ⟨hf, _⟩ := ihf he.1.1 hρ
    obtain ⟨hz, hza⟩ := ihz he.1.2 hρ
    obtain ⟨hl, _⟩ := ihl he.2 hρ
    exact ⟨.foldNil hf hz hl, hza⟩
  | @foldCons c t ρ f z l vf vz x xs rr v _ _ _ _ _ ihf ihz ihl ihr ihv =>
    intro he hρ
    simp only [Expr.refs, List.mem_append, not_or] at he
    obtain ⟨hf, hfa⟩ := ihf he.1.1 hρ
    obtain ⟨hz, hza⟩ := ihz he.1.2 hρ
    obtain ⟨hl, hla⟩ := ihl he.2 hρ
    have hxs : ∀ w ∈ [Value.list xs, vz, vf], Avoids r w := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · cases hla with | list hl'' => exact .list fun w hw => hl'' w (List.mem_cons_of_mem _ hw)
      · exact hza
      · exact hfa
    obtain ⟨hr, hra⟩ := ihr (by simp [foldVarTerm, Expr.refs]) hxs
    have hrs : ∀ w ∈ [rr, x, vf], Avoids r w := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact hra
      · cases hla with | list hl'' => exact hl'' _ List.mem_cons_self
      · exact hfa
    obtain ⟨hv, hva⟩ := ihv (by simp [stepVarTerm, Expr.refs]) hrs
    exact ⟨.foldCons hf hz hl hr hv, hva⟩

/-! ## Transparency -/

section Transparency
variable {raw : Ty} {Θ : ConceptEnv} {Δ : DeclEnv} {P : Provision raw} {S : Sched} {I' : Input}

/-- The provisioned target evaluates, in the provisioned design under the
    raw input, to exactly the induced abstract value. -/
theorem target_value (wf : WF Θ Δ P) (hI : RawInput P I') {s : DeclId} {ch : Channel raw} {h : DesignDecl}
    (_hc : P.chan s = some ch) (_hh : Δ s = some h) (c : ClockId) (t : Nat) :
    MEv S (provision Δ P) I' c t [] (realizeAt h.interface.expectedType ch.tr P.r)
      (wrapAt h.interface.expectedType (ch.transfer (I' P.r t))) := by
  have hraw := hI.1 t
  have hv : (I' P.r t).NoClo := TyVal.noClo wf.raw_data hraw
  have hr : MEv S (provision Δ P) I' c t [] (.declRef P.r) (I' P.r t) :=
    .refInput provision_realizationOf_r
  have happ := (ch.computes _ hraw).mev ch.tr_pure hv hr
  cases h.interface.expectedType with
  | sem c => exact .mk happ
  | bool | nat | arr _ _ | q _ | opt _ | list _ | prod _ _ => exact happ

theorem target_value_avoids (wf : WF Θ Δ P) (hI : RawInput P I') {ch : Channel raw} (τ : Ty) (t : Nat) :
    Avoids P.r (wrapAt τ (ch.transfer (I' P.r t))) := by
  have hraw := hI.1 t
  have hv : (I' P.r t).NoClo := TyVal.noClo wf.raw_data hraw
  have hp : (ch.transfer (I' P.r t)).Pure := (ch.computes _ hraw).pure ch.tr_pure hv
  cases τ with
  | sem c => exact .sem (Avoids.of_pure hp)
  | bool | nat | arr _ _ | q _ | opt _ | list _ | prod _ _ => exact Avoids.of_pure hp

/-- Abstract ⇒ provisioned. -/
theorem provision_forward (wf : WF Θ Δ P) (nm : NoMention Δ P.r) (hI : RawInput P I') :
    ∀ {c : ClockId} {t : Nat} {ρ : List Value} {e : Expr} {v : Value},
      MEv S Δ (induced Δ P I') c t ρ e v → P.r ∉ e.refs → (∀ w ∈ ρ, Avoids P.r w) →
      MEv S (provision Δ P) I' c t ρ e v ∧ Avoids P.r v := by
  intro c t ρ e v h he hρ
  refine simulate P.r ?_ ?_ h he hρ
  · intro d hdr body hb
    left
    cases hc : P.chan d with
    | none => exact ⟨by rw [provision_realizationOf_other hdr hc]; exact hb, nm d body hb⟩
    | some ch =>
      obtain ⟨h', hh', hun, _, _⟩ := wf.targets d ch hc
      simp [DeclEnv.realizationOf, hh', hun] at hb
  · intro d hdr hn c t
    cases hc : P.chan d with
    | none =>
      refine ⟨?_, ?_⟩
      · rw [induced_other hc]; exact .refInput (by rw [provision_realizationOf_other hdr hc]; exact hn)
      · rw [induced_other hc]; exact Avoids.of_noClo (hI.2 d t)
    | some ch =>
      obtain ⟨h', hh', _, _, _⟩ := wf.targets d ch hc
      have hτ : Δ.tyView d = some h'.interface.expectedType := by simp [DeclEnv.tyView, hh']
      rw [induced_target hc hτ]
      exact ⟨.refRealized (provision_realizationOf_target hdr hh' hc) (target_value wf hI hc hh' c t),
        target_value_avoids wf hI _ t⟩

/-- Provisioned ⇒ abstract. -/
theorem provision_backward (wf : WF Θ Δ P) (nm : NoMention Δ P.r) (hI : RawInput P I') :
    ∀ {c : ClockId} {t : Nat} {ρ : List Value} {e : Expr} {v : Value},
      MEv S (provision Δ P) I' c t ρ e v → P.r ∉ e.refs → (∀ w ∈ ρ, Avoids P.r w) →
      MEv S Δ (induced Δ P I') c t ρ e v ∧ Avoids P.r v := by
  intro c t ρ e v h he hρ
  refine simulate P.r ?_ ?_ h he hρ
  · intro d hdr body hb
    cases hc : P.chan d with
    | none =>
      left
      rw [provision_realizationOf_other hdr hc] at hb
      exact ⟨hb, nm d body hb⟩
    | some ch =>
      right
      obtain ⟨h', hh', hun, _, _⟩ := wf.targets d ch hc
      rw [provision_realizationOf_target hdr hh' hc] at hb
      cases hb
      intro c t v hv
      have hval := (target_value (S := S) wf hI hc hh' c t).det hv
      have hτ : Δ.tyView d = some h'.interface.expectedType := by simp [DeclEnv.tyView, hh']
      have hun' : Δ.realizationOf d = none := by simp [DeclEnv.realizationOf, hh', hun]
      refine ⟨?_, ?_⟩
      · rw [← hval, ← induced_target hc hτ]; exact .refInput hun'
      · rw [← hval]; exact target_value_avoids wf hI _ t
  · intro d hdr hn c t
    cases hc : P.chan d with
    | none =>
      rw [provision_realizationOf_other hdr hc] at hn
      have hv := MEv.refInput (S := S) (Δ := Δ) (I := induced Δ P I') (c := c) (t := t) (ρ := []) hn
      rw [induced_other hc] at hv
      exact ⟨hv, Avoids.of_noClo (hI.2 d t)⟩
    | some ch =>
      obtain ⟨h', hh', _, _, _⟩ := wf.targets d ch hc
      rw [provision_realizationOf_target hdr hh' hc] at hn
      exact nomatch hn

/-- **`provision_transparent`** (the main theorem).  For every schedule,
    domain, tick, environment whose values avoid `r`, and term that does
    not mention `r`: the abstract design under the induced input and the
    provisioned design under the raw input evaluate it to the same values.
    Hypotheses beyond the proposal's: the raw input is well typed at `r`
    and closure-free (`RawInput`), the abstract design mentions no `r`
    (true of every globally well-typed design, `NoMention.of_globalWF`),
    and the local environment avoids `r` (true of `[]`). -/
theorem provision_transparent (wf : WF Θ Δ P) (nm : NoMention Δ P.r) (hI : RawInput P I')
    {c : ClockId} {t : Nat} {ρ : List Value} {e : Expr} {v : Value}
    (he : P.r ∉ e.refs) (hρ : ∀ w ∈ ρ, Avoids P.r w) :
    MEv S Δ (induced Δ P I') c t ρ e v ↔ MEv S (provision Δ P) I' c t ρ e v :=
  ⟨fun h => (provision_forward wf nm hI h he hρ).1, fun h => (provision_backward wf nm hI h he hρ).1⟩

/-- The observation boundary by typing: any term typed in the abstract
    design is transparent. -/
theorem provision_transparent_typed {ev : Evidence} (g : GlobalWF ev Θ Δ) (wf : WF Θ Δ P) (hI : RawInput P I')
    {G : Grant} {Γ : Ctx} {e : Expr} {τ : Ty} (ht : HasType Θ Δ G Γ e τ) {c : ClockId} {t : Nat} {v : Value} :
    MEv S Δ (induced Δ P I') c t [] e v ↔ MEv S (provision Δ P) I' c t [] e v :=
  provision_transparent wf (NoMention.of_globalWF g wf.fresh) hI (typed_avoids ht wf.fresh) (fun _ h => by simp at h)

/-- Every declaration of the abstract design is observed identically. -/
theorem provision_decl_transparent (wf : WF Θ Δ P) (nm : NoMention Δ P.r) (hI : RawInput P I')
    {d : DeclId} (hd : Δ d ≠ none) {c : ClockId} {t : Nat} {v : Value} :
    MEv S Δ (induced Δ P I') c t [] (.declRef d) v ↔ MEv S (provision Δ P) I' c t [] (.declRef d) v := by
  refine provision_transparent wf nm hI ?_ (fun _ h => by simp at h)
  simp [Expr.refs]
  intro e; subst e; exact hd wf.fresh

/-- Physical outputs are unchanged: the sink sees the same value. -/
theorem provision_physicalOutput (wf : WF Θ Δ P) (nm : NoMention Δ P.r) (hI : RawInput P I')
    {Ω : OutputEnv} {β : DriveEnv} (hβ : ∀ d o, β d = some o → Δ d ≠ none) {o : OutputId} {t : Nat} {v : Value} :
    PhysicalOutput S Δ (induced Δ P I') Ω β o t v ↔ PhysicalOutput S (provision Δ P) I' Ω β o t v := by
  unfold PhysicalOutput
  constructor
  · rintro ⟨d, spec, hb, hΩ, he⟩
    exact ⟨d, spec, hb, hΩ, (provision_decl_transparent wf nm hI (hβ d o hb)).mp he⟩
  · rintro ⟨d, spec, hb, hΩ, he⟩
    exact ⟨d, spec, hb, hΩ, (provision_decl_transparent wf nm hI (hβ d o hb)).mpr he⟩

end Transparency

/-! ## Trace abstraction and exactness -/

section Traces
variable {raw : Ty} {Θ : ConceptEnv} {Δ : DeclEnv} {P : Provision raw} {S : Sched}

/-- **`provision_abstracts`**: every behaviour of the provisioned design
    under a raw input is a behaviour of the abstract design under some
    input — the induced one.  Deployment *restricts* the abstract
    environment; it does not give the abstract design its meaning. -/
theorem provision_abstracts (wf : WF Θ Δ P) (nm : NoMention Δ P.r) {I' : Input} (hI : RawInput P I') :
    ∃ I : Input, ∀ d, Δ d ≠ none → ∀ c t v,
      MEv S (provision Δ P) I' c t [] (.declRef d) v ↔ MEv S Δ I c t [] (.declRef d) v :=
  ⟨induced Δ P I', fun _ hd _ _ _ => (provision_decl_transparent wf nm hI hd).symm⟩

/-- Evaluation depends on the input only off `r` when nothing mentions `r`. -/
theorem input_congr (r : DeclId) (nm : NoMention Δ r) {I J : Input} (hIJ : ∀ d t, d ≠ r → I d t = J d t)
    (hJ : ∀ d t, d ≠ r → Δ.realizationOf d = none → Avoids r (I d t))
    {c : ClockId} {t : Nat} {ρ : List Value} {e : Expr} {v : Value}
    (he : r ∉ e.refs) (hρ : ∀ w ∈ ρ, Avoids r w) (h : MEv S Δ I c t ρ e v) : MEv S Δ J c t ρ e v := by
  refine (simulate r ?_ ?_ h he hρ).1
  · intro d _ body hb; exact Or.inl ⟨hb, nm d body hb⟩
  · intro d hdr hn c t
    rw [hIJ d t hdr]
    exact ⟨.refInput hn, hIJ d t hdr ▸ hJ d t hdr hn⟩

/-- A **joint section** of the provision for an abstract input `I`: a raw
    trace `sec` that every channel transfers to what `I` gives its target.
    With one channel this is a right inverse of `transfer`; with several
    channels sharing the raw reading it is the joint preimage, which need
    not exist even when every channel is surjective. -/
def JointSection (Δ : DeclEnv) (P : Provision raw) (I : Input) (sec : Nat → Value) : Prop :=
  ∀ t, TyVal raw (sec t) ∧ ∀ s ch τ, P.chan s = some ch → Δ.tyView s = some τ →
    I s t = wrapAt τ (ch.transfer (sec t))

/-- The raw input a joint section determines. -/
def rawOf (P : Provision raw) (I : Input) (sec : Nat → Value) : Input :=
  fun d t => if d = P.r then sec t else I d t

theorem induced_rawOf (wf : WF Θ Δ P) {I : Input} {sec : Nat → Value} (hs : JointSection Δ P I sec) :
    ∀ d t, d ≠ P.r → induced Δ P (rawOf P I sec) d t = I d t := by
  intro d t hdr
  cases hc : P.chan d with
  | none => simp [induced, hc, rawOf, hdr]
  | some ch =>
    obtain ⟨h, hh, _, _, _⟩ := wf.targets d ch hc
    have hτ : Δ.tyView d = some h.interface.expectedType := by simp [DeclEnv.tyView, hh]
    rw [induced_target hc hτ, (hs t).2 d ch _ hc hτ]
    simp [rawOf]

/-- **`provision_exact`**: when the abstract input has a joint section,
    the provisioned design under the determined raw input evaluates every
    `r`-free term exactly as the abstract design under `I`.  Together with
    `provision_abstracts`: the trace sets coincide exactly for the abstract
    inputs that have a joint section. -/
theorem provision_exact (wf : WF Θ Δ P) (nm : NoMention Δ P.r) {I : Input} (hI : ∀ d t, (I d t).NoClo)
    {sec : Nat → Value} (hs : JointSection Δ P I sec)
    {c : ClockId} {t : Nat} {ρ : List Value} {e : Expr} {v : Value}
    (he : P.r ∉ e.refs) (hρ : ∀ w ∈ ρ, Avoids P.r w) :
    MEv S Δ I c t ρ e v ↔ MEv S (provision Δ P) (rawOf P I sec) c t ρ e v := by
  have hraw : RawInput P (rawOf P I sec) := by
    refine ⟨fun t => by simp [rawOf, (hs t).1], fun d t => ?_⟩
    by_cases hdr : d = P.r
    · simp [rawOf, hdr]; exact TyVal.noClo wf.raw_data (hs t).1
    · simp [rawOf, hdr]; exact hI d t
  have hind := induced_rawOf wf hs
  rw [← provision_transparent wf nm hraw he hρ]
  constructor
  · intro h
    exact input_congr P.r nm (fun d t hdr => (hind d t hdr).symm)
      (fun d t _ _ => Avoids.of_noClo (hI d t)) he hρ h
  · intro h
    refine input_congr P.r nm (fun d t hdr => hind d t hdr) ?_ he hρ h
    intro d t hdr hn
    rw [hind d t hdr]; exact Avoids.of_noClo (hI d t)

end Traces

/-! ## Re-application, commutation, permutation -/

section Algebra
variable {raw : Ty} {Θ : ConceptEnv} {Δ : DeclEnv} {P : Provision raw}

/-- After provision, no target is a Source: the operation's precondition no
    longer holds for it, and `r` is no longer fresh.  This — not
    idempotence — is the lifecycle fact: provision is a one-way step. -/
theorem provision_not_reapplicable (wf : WF Θ Δ P) :
    (∀ s ch, P.chan s = some ch → ¬ Source (provision Δ P) s) ∧ ¬ WF Θ (provision Δ P) P := by
  refine ⟨fun s ch hc hsrc => ?_, fun wf' => ?_⟩
  · obtain ⟨h, hh, _, _, _⟩ := wf.targets s ch hc
    unfold Source at hsrc
    rw [provision_realizationOf_target (wf.target_ne_r hc) hh hc] at hsrc
    exact nomatch hsrc
  · have := wf'.fresh
    rw [provision_r] at this
    exact nomatch this

/-- As a *total function on environments* the construction is idempotent:
    a second pass overwrites `r` and every target with the same declaration.
    This is a fact about the function's totalization, not a lifecycle
    property — `provision_not_reapplicable` says the second pass is not a
    legal step. -/
theorem provision_idem_total : provision (provision Δ P) P = provision Δ P := by
  funext d
  by_cases hdr : d = P.r
  · subst hdr; simp [provision]
  · simp only [provision, hdr, ↓reduceIte]
    cases Δ d <;> cases P.chan d <;> rfl

/-- Provisioning the same target twice with *different* terms is not a
    refinement: a realization, once written, is write-once (`DeclLeq`). -/
theorem provision_reprovision_not_refinement {raw₂ : Ty} {P₂ : Provision raw₂} (wf : WF Θ Δ P)
    {s : DeclId} {ch : Channel raw} {ch₂ : Channel raw₂} {h : DesignDecl}
    (hc : P.chan s = some ch) (hc₂ : P₂.chan s = some ch₂) (hh : Δ s = some h) (hs₂ : s ≠ P₂.r)
    (hne : realizeAt h.interface.expectedType ch.tr P.r ≠ realizeAt h.interface.expectedType ch₂.tr P₂.r) :
    ¬ EnvRefines (provision Δ P) (provision (provision Δ P) P₂) := by
  intro er
  have hsr := wf.target_ne_r hc
  obtain ⟨h₂, hh₂, le⟩ := er s _ (provision_target hsr hh hc)
  rw [provision_target hs₂ (provision_target hsr hh hc) hc₂] at hh₂
  cases hh₂
  have := le.2.2 _ rfl
  simp at this
  exact hne this.symm

/-- **`provision_comm`**: independent provisions commute *exactly*: distinct
    raw identities, neither a target of the other, disjoint targets. -/
theorem provision_comm {raw₂ : Ty} {P₂ : Provision raw₂} (hr : P.r ≠ P₂.r)
    (h₁₂ : P.chan P₂.r = none) (h₂₁ : P₂.chan P.r = none)
    (hdisj : ∀ d, P.chan d ≠ none → P₂.chan d = none) :
    provision (provision Δ P) P₂ = provision (provision Δ P₂) P := by
  funext d
  by_cases hd₁ : d = P.r
  · subst hd₁
    simp [provision, hr, h₂₁]
  by_cases hd₂ : d = P₂.r
  · subst hd₂
    simp [provision, Ne.symm hr, h₁₂]
  simp only [provision, hd₁, hd₂, ↓reduceIte]
  cases hΔ : Δ d with
  | none => cases P.chan d <;> cases P₂.chan d <;> rfl
  | some h =>
    cases hc₁ : P.chan d with
    | none => cases P₂.chan d <;> rfl
    | some ch =>
      have := hdisj d (by rw [hc₁]; simp)
      rw [this]

/-- A provision from a finite assignment list. -/
def Provision.ofList (r : DeclId) (clock : Option ClockId) (l : List (DeclId × Channel raw)) : Provision raw :=
  ⟨r, clock, fun d => (l.find? (·.1 = d)).map (·.2)⟩

theorem find?_eq_of_nodup {l : List (DeclId × Channel raw)} (hn : (l.map Prod.fst).Nodup) {d : DeclId}
    {p : DeclId × Channel raw} (hp : p ∈ l) (hd : p.1 = d) : l.find? (·.1 = d) = some p := by
  induction l with
  | nil => simp at hp
  | cons q l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.mp hp with rfl | hp'
    · simp [List.find?, hd]
    · have hqd : q.1 ≠ d := by
        intro e; exact hn.1 ⟨p, hp', by rw [hd, e]⟩
      simp only [List.find?_cons, hqd, decide_false]
      exact ih hn.2 hp'

/-- **`provision_perm`**: the assignment is a set — any order of the list
    yields the same provision, hence the same provisioned design. -/
theorem provision_perm {r : DeclId} {clock : Option ClockId} {l l' : List (DeclId × Channel raw)}
    (hn : (l.map Prod.fst).Nodup) (hp : l.Perm l') :
    Provision.ofList r clock l = Provision.ofList r clock l' := by
  have hn' : (l'.map Prod.fst).Nodup := (hp.map Prod.fst).nodup_iff.mp hn
  simp only [Provision.ofList, Provision.mk.injEq, true_and]
  funext d
  cases hf : l.find? (·.1 = d) with
  | none =>
    cases hf' : l'.find? (·.1 = d) with
    | none => rfl
    | some p =>
      have hmem := List.mem_of_find?_eq_some hf'
      have hpd : p.1 = d := by simpa using List.find?_some hf'
      rw [find?_eq_of_nodup hn (hp.mem_iff.mpr hmem) hpd] at hf
      exact nomatch hf
  | some p =>
    have hmem := List.mem_of_find?_eq_some hf
    have hpd : p.1 = d := by simpa using List.find?_some hf
    rw [find?_eq_of_nodup hn' (hp.mem_iff.mp hmem) hpd]

end Algebra

/-! ## The raw declaration and the Source role -/

section Raw
variable {raw : Ty} {Θ : ConceptEnv} {Δ : DeclEnv} {P : Provision raw}

theorem Ty.Data.not_arr {τ : Ty} (h : τ.Data) : ¬ Ty.IsArr τ := by
  cases τ <;> first | exact fun h' => h' | exact fun _ => h

/-- The raw declaration's interface: kernel type `raw`, canonical type
    `() -> raw` (Phase 12), no commitments, no realization. -/
theorem raw_interface (hd : raw.Data) :
    (provision Δ P).tyView P.r = some raw ∧ (provision Δ P).realizationOf P.r = none ∧
    canonicalOfKernel raw = .arr .unit (.k raw) :=
  ⟨provision_tyView_r, provision_realizationOf_r,
   canonicalOfKernel_encode ⟨[], raw⟩ (Ty.Data.not_arr hd)⟩

/-- The Source role moves from the targets to `r`: after provision `r` is
    the simulation input and no target is. -/
theorem provision_source_role (wf : WF Θ Δ P) :
    SimulationInput (provision Δ P) P.r ∧ ∀ s ch, P.chan s = some ch → ¬ SimulationInput (provision Δ P) s := by
  refine ⟨⟨provision_realizationOf_r, raw, provision_tyView_r, Ty.Data.not_arr wf.raw_data⟩, ?_⟩
  intro s ch hc hsim
  exact (provision_not_reapplicable wf).1 s ch hc hsim.1

end Raw

/-! ## The singleton -/

section One
variable {raw : Ty} {Θ : ConceptEnv} {Δ : DeclEnv}

theorem Provision.one_chan_self (r s : DeclId) (clock : Option ClockId) (ch : Channel raw) :
    (Provision.one r s clock ch).chan s = some ch := by simp [Provision.one]

theorem Provision.one_chan_other (r s : DeclId) (clock : Option ClockId) (ch : Channel raw) {d : DeclId}
    (hd : d ≠ s) : (Provision.one r s clock ch).chan d = none := by simp [Provision.one, hd]

/-- The singleton's preconditions, in the proposal's terms. -/
theorem WF.one {r s : DeclId} {clock : Option ClockId} {ch : Channel raw} {h : DesignDecl}
    (hfresh : Δ r = none) (hsf : raw.SemFree) (hdata : raw.Data)
    (hs : Δ s = some h) (hun : h.realization = none) (hfit : Fits Θ h.interface.expectedType ch) (hty : ch.WF Θ) :
    WF Θ Δ (Provision.one r s clock ch) := by
  refine ⟨hfresh, hsf, hdata, fun s' ch' hc => ?_⟩
  simp only [Provision.one] at hc
  split at hc
  · rename_i e; subst e; cases hc; exact ⟨h, hs, hun, hfit, hty⟩
  · exact nomatch hc

/-- **`provisionOne_transparent`**: the proposal's theorem 4, as the
    singleton instance of `provision_transparent`. -/
theorem provisionOne_transparent {S : Sched} {r s : DeclId} {clock : Option ClockId} {ch : Channel raw}
    (wf : WF Θ Δ (Provision.one r s clock ch)) (nm : NoMention Δ r) {I' : Input}
    (hI : RawInput (Provision.one r s clock ch) I')
    {c : ClockId} {t : Nat} {e : Expr} {v : Value} (he : r ∉ e.refs) :
    MEv S Δ (induced Δ (Provision.one r s clock ch) I') c t [] e v ↔
      MEv S (provision Δ (Provision.one r s clock ch)) I' c t [] e v :=
  provision_transparent wf nm hI he (fun _ h => by simp at h)

/-- The singleton's induced input: `s` gets the wrapped transfer of the raw
    reading, every other identity is untouched. -/
theorem induced_one {r s : DeclId} {clock : Option ClockId} {ch : Channel raw} {I' : Input} {τ : Ty}
    (hτ : Δ.tyView s = some τ) (t : Nat) :
    induced Δ (Provision.one r s clock ch) I' s t = wrapAt τ (ch.transfer (I' r t)) ∧
    ∀ d, d ≠ s → induced Δ (Provision.one r s clock ch) I' d t = I' d t :=
  ⟨induced_target (Provision.one_chan_self r s clock ch) hτ t,
   fun _ hd => induced_other (Provision.one_chan_other r s clock ch hd) t⟩

/-- A pointwise section of one channel is a joint section of the singleton
    for every abstract input typed at the target. -/
theorem JointSection.one {r s : DeclId} {clock : Option ClockId} {ch : Channel raw} {τ : Ty}
    (hτ : Δ.tyView s = some τ) {inv : Value → Value}
    (hinv : ∀ w, TyVal ch.rep w → TyVal raw (inv w) ∧ ch.transfer (inv w) = w)
    {I : Input} (hI : ∀ t, TyVal ch.rep (unwrapAt τ (I s t)) ∧ wrapAt τ (unwrapAt τ (I s t)) = I s t) :
    JointSection Δ (Provision.one r s clock ch) I (fun t => inv (unwrapAt τ (I s t))) := by
  intro t
  refine ⟨(hinv _ (hI t).1).1, fun s' ch' τ' hc hτ' => ?_⟩
  simp only [Provision.one] at hc
  split at hc
  · rename_i e; subst e; cases hc
    rw [hτ] at hτ'; cases hτ'
    rw [(hinv _ (hI t).1).2, (hI t).2]
  · exact nomatch hc

end One

end BDL.Provision
