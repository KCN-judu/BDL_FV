import BDL.Behavior.Preservation

/-!
# Semantics — hierarchical execution agrees with flattened execution

**Theorem J (restricted fragment).**  The *modular* semantics of a system
evaluates each instance in isolation — its renamed template, every port an
input — under an input `I'` that feeds each bound port with the value its
source produces under the same `I'` (a *consistent* input).  The
*flattened* semantics evaluates `flatten S` under the system input `I`.

Proved here, for the single-domain semantics `Ev` (Phase 4), on wiring
designs (no lambdas; the precedent of `unfolds_preserves_eval`), with
direct and constant bindings only:

* flattened ⇒ modular, for every consistent `I'` (`eval_flat_to_inst`);
* modular ⇒ flattened, given totality of the flattened design
  (`eval_inst_to_flat`, discharged from `reactive_total` in
  `eval_inst_to_flat_of_causal`);
* hence the modular value of any declaration is unique and equals the
  flattened value (`modular_unique`).

Not proved (recorded obligations): the multi-domain relation `MEv` with
`sync` bindings; the higher-order case; and the *existence* of a consistent
`I'`, which follows from totality by choice and is not proved
constructively here.
-/

namespace BDL
open BDL.Reactive

namespace BehaviorSystem

variable {ev : Evidence} {S : BehaviorSystem}

/-! ## The modular semantics -/

/-- Which instance owns a flattened identity. -/
def Owns (S : BehaviorSystem) (k : Nat) (d : DeclId) : Prop := ∃ n, decode S.W d.n = some (k, n)

/-- Instance `k` alone: its renamed template, every port an input. -/
def instΔ (S : BehaviorSystem) (k : Nat) : DeclEnv := fun id =>
  match decode S.W id.n with
  | some (k', _) => if k' = k then S.unionΔ id else none
  | none => none

def BoundDst (S : BehaviorSystem) (d : DeclId) : Prop := ∃ b ∈ S.bindings, S.declOf b.dstInst b.dst = d

/-- No transport bindings: the single-domain fragment. -/
def DirectOnly (S : BehaviorSystem) : Prop := ∀ b ∈ S.bindings, b.transport = none

/-- A **consistent** (modular) input: agrees with `I` off the bound ports,
    and feeds each bound port with the value its source produces when the
    source's instance is evaluated alone under the same input. -/
def Consistent (S : BehaviorSystem) (I I' : Input) : Prop :=
  (∀ d t, ¬ S.BoundDst d → I' d t = I d t) ∧
  ∀ b ∈ S.bindings, ∀ t,
    match b.src with
    | .port k id => Ev (S.instΔ k) I' t [] (.declRef (S.declOf k id)) (I' (S.declOf b.dstInst b.dst) t)
    | .const e => Ev (S.instΔ b.dstInst) I' t [] e (I' (S.declOf b.dstInst b.dst) t)

/-! ## Ownership lemmas -/

theorem owns_declOf (hW : 0 < S.W) {k : Nat} {d : DeclId} (hd : d.n < S.W) : S.Owns k (S.declOf k d) :=
  ⟨d.n, decode_fresh hW hd⟩

theorem owns_unique {k k' : Nat} {d : DeclId} (h : S.Owns k d) (h' : S.Owns k' d) : k = k' := by
  obtain ⟨n, hn⟩ := h; obtain ⟨n', hn'⟩ := h'
  rw [hn] at hn'; cases hn'; rfl

theorem instΔ_owned {k : Nat} {d : DeclId} (h : S.Owns k d) : S.instΔ k d = S.unionΔ d := by
  obtain ⟨n, hn⟩ := h
  unfold instΔ; simp [hn]

theorem instΔ_some {k : Nat} {d : DeclId} {h : DesignDecl} (hd : S.instΔ k d = some h) : S.Owns k d := by
  unfold instΔ at hd
  cases hdec : decode S.W d.n with
  | none => simp [hdec] at hd
  | some kn =>
    obtain ⟨k', n⟩ := kn
    simp only [hdec] at hd
    by_cases hk : k' = k
    · subst hk; exact ⟨n, hdec⟩
    · simp [hk] at hd

/-- The flattened body of an unbound declaration is its union body. -/
theorem flattenΔ_unbound (c : ComposeWF ev S) (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound)
    {d : DeclId} (hnb : ¬ S.BoundDst d) : S.flattenΔ d = S.unionΔ d :=
  (flatten_inv c mono eq ps).untouched d (fun b hb heq => hnb ⟨b, hb, heq⟩)

theorem bound_realized (c : ComposeWF ev S) (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound)
    {d : DeclId} (hb : S.BoundDst d) : ∃ e, S.flattenΔ.realizationOf d = some e := by
  obtain ⟨b, hbm, rfl⟩ := hb
  obtain ⟨Id, pd, -, -, -, hΔ⟩ := (flatten_inv c mono eq ps).bound b hbm
  exact ⟨S.bindingBody b, by simp [DeclEnv.realizationOf, hΔ]⟩

theorem bound_open_in_union (c : ComposeWF ev S) {d : DeclId} (hb : S.BoundDst d) :
    S.unionΔ.realizationOf d = none := by
  obtain ⟨b, hbm, rfl⟩ := hb
  obtain ⟨Id, hId, pd, hpd, hpid, -⟩ := c.bindings b hbm
  rw [← hpid]
  simp [DeclEnv.realizationOf, union_port c hId hpd]

/-- References of a template body are owned by its instance. -/
theorem template_refs_owned (c : ComposeWF ev S) {k : Nat} {I : Inst} (hI : S.instAt k = some I)
    {n : Nat} {h : DesignDecl} {e₀ : Expr} (hΔ : I.comp.design.Δ ⟨n⟩ = some h) (he : h.realization = some e₀) :
    ∀ x ∈ (e₀.rename (S.ren k I)).refs, S.Owns k x := by
  intro x hx
  rw [Expr.rename_refs, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact owns_declOf c.width (template_refs_bounded c hI hΔ he y hy).2

instance (S : BehaviorSystem) (d : DeclId) : Decidable (S.BoundDst d) :=
  inferInstanceAs (Decidable (∃ b, b ∈ S.bindings ∧ S.declOf b.dstInst b.dst = d))

/-- `declRef` evaluation does not depend on the local environment. -/
theorem _root_.BDL.Reactive.Ev.declRef_env {Δ : DeclEnv} {I : Input} {t : Nat} {ρ ρ' : List Value} {d : DeclId} {v : Value}
    (h : Ev Δ I t ρ (.declRef d) v) : Ev Δ I t ρ' (.declRef d) v := by
  cases h with
  | refRealized hs hb => exact .refRealized hs hb
  | refInput hn => exact .refInput hn

/-! ## Theorem J, forward: flattened ⇒ modular -/

theorem eval_flat_to_inst (c : ComposeWF ev S) (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound)
    (hdir : DirectOnly S) (hw : DeclEnvWiring S.flattenΔ) {I I' : Input} (hI : ∀ d t, (I d t).NoClo)
    (hc : Consistent S I I') :
    ∀ {t : Nat} {ρ : List Value} {e : Expr} {v : Value}, Ev S.flattenΔ I t ρ e v → e.Wiring →
      ∀ k, (∀ d ∈ e.refs, S.Owns k d) → Ev (S.instΔ k) I' t ρ e v := by
  intro t ρ e v h
  induction h with
  | var _ => intro hw; exact hw.elim
  | boolLit => intro _ _ _; exact .boolLit
  | natLit => intro _ _ _; exact .natLit
  | lam => intro hw; exact hw.elim
  | appClo hf _ _ _ _ _ => intro hw'; exact ((Ev.noClo hw hI hf hw'.1) (.clo _ _)).elim
  | appPrim _ _ ihf iha =>
    intro hw' k hown
    simp only [Expr.refs, List.mem_append] at hown
    exact .appPrim (ihf hw'.1 k fun d hd => hown d (Or.inl hd)) (iha hw'.2 k fun d hd => hown d (Or.inr hd))
  | @refRealized t ρ d b v hs hb ih =>
    intro _ k hown
    have hownd : S.Owns k d := hown d (by simp [Expr.refs])
    rcases flatten_body c mono eq ps hs with
      ⟨k', I, n, h, e₀, hI', hΔ, he₀, rfl, hn, rfl, hnb⟩ | ⟨b', hbm, rfl, rfl, Id, pd, hId, hpd, hpid⟩
    · -- a template declaration: evaluate its body in the instance alone
      have hk : k' = k := owns_unique (owns_declOf c.width hn) hownd
      subst hk
      have hinst : (S.instΔ k').realizationOf (S.declOf k' ⟨n⟩) = some (e₀.rename (S.ren k' I)) := by
        rw [DeclEnv.realizationOf, instΔ_owned hownd, ← flattenΔ_unbound c mono eq ps (fun hb => hnb hb),
          ← DeclEnv.realizationOf]
        exact hs
      exact .refRealized hinst (ih (hw _ _ hs) k' (template_refs_owned c hI' hΔ he₀))
    · -- a bound port: an input of the instance alone, fed consistently
      have hk : b'.dstInst = k := owns_unique (owns_declOf c.width (port_bounded c hId (Or.inl hpd) |> fun h => hpid ▸ h)) hownd
      have hopen : (S.instΔ k).realizationOf (S.declOf b'.dstInst b'.dst) = none := by
        rw [DeclEnv.realizationOf, instΔ_owned hownd, ← DeclEnv.realizationOf]
        exact bound_open_in_union c ⟨b', hbm, rfl⟩
      have hcons := hc.2 b' hbm t
      have hv : v = I' (S.declOf b'.dstInst b'.dst) t := by
        cases hsrc : b'.src with
        | port ks id =>
          simp only [hsrc] at hcons
          obtain ⟨Id', hId', pd', -, -, hsrc'⟩ := c.bindings b' hbm
          rw [hsrc] at hsrc'
          obtain ⟨Is, hIs, psrc, hpsrc, rfl, -⟩ := hsrc'
          have hbody : S.bindingBody b' = .declRef (S.declOf ks psrc.id) := by
            simp [bindingBody, hsrc, hdir b' hbm]
          rw [hbody] at ih
          have h₁ := ih (by simp [Expr.Wiring]) ks
            (fun d hd => by
              simp only [Expr.refs, List.mem_singleton] at hd; subst hd
              exact owns_declOf c.width (port_bounded c hIs (Or.inr hpsrc)))
          exact h₁.det hcons
        | const e =>
          simp only [hsrc] at hcons
          have hbody : S.bindingBody b' = e := by simp [bindingBody, hsrc]
          rw [hbody] at ih
          obtain ⟨Id', hId', pd', -, -, hsrc'⟩ := c.bindings b' hbm
          rw [hsrc] at hsrc'
          obtain ⟨-, hf, -⟩ := hsrc'
          have h₁ := ih (hw _ _ (hbody ▸ hs)) b'.dstInst (fun d hd => by rw [hf] at hd; simp at hd)
          subst hk
          exact h₁.det hcons
      rw [hv]
      exact .refInput hopen
  | @refInput t ρ d hn =>
    intro _ k hown
    have hownd : S.Owns k d := hown d (by simp [Expr.refs])
    have hnb : ¬ S.BoundDst d := fun hb => by
      obtain ⟨e, he⟩ := bound_realized c mono eq ps hb
      rw [hn] at he; exact nomatch he
    rw [← hc.1 d t hnb]
    refine .refInput ?_
    rw [DeclEnv.realizationOf, instΔ_owned hownd, ← flattenΔ_unbound c mono eq ps hnb, ← DeclEnv.realizationOf]
    exact hn
  | rep _ ih => intro hw' k hown; exact .rep (ih hw' k hown)
  | mk _ ih => intro hw' k hown; exact .mk (ih hw' k hown)
  | prim => intro _ _ _; exact .prim
  | delayZero _ ih =>
    intro hw' k hown
    simp only [Expr.refs, List.mem_append] at hown
    exact .delayZero (ih hw'.1 k fun d hd => hown d (Or.inl hd))
  | delaySucc _ ih =>
    intro hw' k hown
    simp only [Expr.refs, List.mem_append] at hown
    exact .delaySucc (ih hw'.2 k fun d hd => hown d (Or.inr hd))
  | syncZero _ ih =>
    intro hw' k hown
    simp only [Expr.refs, List.mem_append] at hown
    exact .syncZero (ih hw'.1 k fun d hd => hown d (Or.inl hd))
  | syncSucc _ ih =>
    intro hw' k hown
    simp only [Expr.refs, List.mem_append] at hown
    exact .syncSucc (ih hw'.2 k fun d hd => hown d (Or.inr hd))
  | foldNil _ _ _ ihf ihz ihl =>
    intro hw' k hown
    simp only [Expr.refs, List.mem_append] at hown
    exact .foldNil (ihf hw'.1 k fun d hd => hown d (Or.inl (Or.inl hd)))
      (ihz hw'.2.1 k fun d hd => hown d (Or.inl (Or.inr hd))) (ihl hw'.2.2 k fun d hd => hown d (Or.inr hd))
  | foldCons hf hz hl hr hv ihf ihz ihl _ _ =>
    intro hw' k hown
    simp only [Expr.refs, List.mem_append] at hown
    exact Ev.foldCons_move (ihf hw'.1 k fun d hd => hown d (Or.inl (Or.inl hd)))
      (ihz hw'.2.1 k fun d hd => hown d (Or.inl (Or.inr hd))) (ihl hw'.2.2 k fun d hd => hown d (Or.inr hd))
      hr hv hw hI (Ev.noClo hw hI hf hw'.1) (Ev.noClo hw hI hz hw'.2.1) (Ev.noClo hw hI hl hw'.2.2)


/-! ## Theorem J, converse: modular ⇒ flattened, given totality -/

theorem instΔ_wiring (c : ComposeWF ev S) (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound)
    (hw : DeclEnvWiring S.flattenΔ) (k : Nat) : DeclEnvWiring (S.instΔ k) := by
  intro d b hd
  simp only [DeclEnv.realizationOf, Option.bind_eq_some_iff] at hd
  obtain ⟨h, hh, hre⟩ := hd
  have hown := instΔ_some hh
  rw [instΔ_owned hown] at hh
  have hnb : ¬ S.BoundDst d := fun hb => by
    have := bound_open_in_union c hb
    simp [DeclEnv.realizationOf, hh, hre] at this
  apply hw d b
  rw [DeclEnv.realizationOf, flattenΔ_unbound c mono eq ps hnb]
  simp [hh, hre]

theorem _root_.BDL.Reactive.Ev.declRef_input {Δ : DeclEnv} {I : Input} {t : Nat} {ρ : List Value} {d : DeclId} {v : Value}
    (h : Ev Δ I t ρ (.declRef d) v) (hn : Δ.realizationOf d = none) : v = I d t := by
  cases h with
  | refRealized hs _ => rw [hs] at hn; exact nomatch hn
  | refInput _ => rfl

theorem eval_inst_to_flat (c : ComposeWF ev S) (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound)
    (hdir : DirectOnly S) (hw : DeclEnvWiring S.flattenΔ) {I I' : Input}
    (hI : ∀ d t, (I d t).NoClo) (hI' : ∀ d t, (I' d t).NoClo) (hc : Consistent S I I')
    (htot : ∀ d, (∃ h, S.flattenΔ d = some h) → ∀ t, ∃ v, Ev S.flattenΔ I t [] (.declRef d) v)
    {k : Nat} :
    ∀ {t : Nat} {ρ : List Value} {e : Expr} {v : Value}, Ev (S.instΔ k) I' t ρ e v → e.Wiring →
      (∀ d ∈ e.refs, S.Owns k d) → Ev S.flattenΔ I t ρ e v := by
  intro t ρ e v h
  induction h with
  | var _ => intro hw'; exact hw'.elim
  | boolLit => intro _ _; exact .boolLit
  | natLit => intro _ _; exact .natLit
  | lam => intro hw'; exact hw'.elim
  | appClo hf _ _ _ _ _ => intro hw'; exact ((Ev.noClo (instΔ_wiring c mono eq ps hw k) hI' hf hw'.1) (.clo _ _)).elim
  | appPrim _ _ ihf iha =>
    intro hw' hown
    simp only [Expr.refs, List.mem_append] at hown
    exact .appPrim (ihf hw'.1 fun d hd => hown d (Or.inl hd)) (iha hw'.2 fun d hd => hown d (Or.inr hd))
  | @refRealized t ρ d b v hs hb ih =>
    intro _ hown
    have hownd : S.Owns k d := hown d (by simp [Expr.refs])
    have hu : S.unionΔ.realizationOf d = some b := by
      rw [DeclEnv.realizationOf, ← instΔ_owned hownd]; exact hs
    have hnb : ¬ S.BoundDst d := fun hbd => by rw [bound_open_in_union c hbd] at hu; exact nomatch hu
    have hf : S.flattenΔ.realizationOf d = some b := by
      rw [DeclEnv.realizationOf, flattenΔ_unbound c mono eq ps hnb]; exact hu
    -- references of the body are owned by `k`
    have hrefs : ∀ x ∈ b.refs, S.Owns k x := by
      simp only [DeclEnv.realizationOf, Option.bind_eq_some_iff] at hu
      obtain ⟨h', hh', hre⟩ := hu
      obtain ⟨k', I, n, h₀, hI', hΔ, rfl, rfl, hn⟩ := unionΔ_some hh'
      have hk : k' = k := owns_unique (owns_declOf c.width hn) hownd
      subst hk
      simp only [DesignDecl.rename, Option.map_eq_some_iff] at hre
      obtain ⟨e₀, he₀, rfl⟩ := hre
      exact template_refs_owned c hI' hΔ he₀
    exact .refRealized hf (ih (hw _ _ hf) hrefs)
  | @refInput t ρ d hn =>
    intro _ hown
    have hownd : S.Owns k d := hown d (by simp [Expr.refs])
    have hu : S.unionΔ.realizationOf d = none := by
      rw [DeclEnv.realizationOf, ← instΔ_owned hownd]; exact hn
    by_cases hbd : S.BoundDst d
    · -- a bound port: the flattened value exists (totality) and, read back
      -- through the forward direction, is the consistent input
      have hdecl : ∃ h, S.flattenΔ d = some h := by
        obtain ⟨b, hbm, rfl⟩ := hbd
        obtain ⟨Id, pd, -, -, -, hΔ⟩ := (flatten_inv c mono eq ps).bound b hbm
        exact ⟨_, hΔ⟩
      obtain ⟨v₀, hv₀⟩ := htot d hdecl t
      have hfwd := eval_flat_to_inst c mono eq ps hdir hw hI hc hv₀ (by simp [Expr.Wiring]) k
        (fun x hx => by simp only [Expr.refs, List.mem_singleton] at hx; subst hx; exact hownd)
      have := hfwd.declRef_input hn
      subst this
      exact hv₀.declRef_env
    · rw [hc.1 d t hbd]
      refine .refInput ?_
      rw [DeclEnv.realizationOf, flattenΔ_unbound c mono eq ps hbd]; exact hu
  | rep _ ih => intro hw' hown; exact .rep (ih hw' hown)
  | mk _ ih => intro hw' hown; exact .mk (ih hw' hown)
  | prim => intro _ _; exact .prim
  | delayZero _ ih =>
    intro hw' hown
    simp only [Expr.refs, List.mem_append] at hown
    exact .delayZero (ih hw'.1 fun d hd => hown d (Or.inl hd))
  | delaySucc _ ih =>
    intro hw' hown
    simp only [Expr.refs, List.mem_append] at hown
    exact .delaySucc (ih hw'.2 fun d hd => hown d (Or.inr hd))
  | syncZero _ ih =>
    intro hw' hown
    simp only [Expr.refs, List.mem_append] at hown
    exact .syncZero (ih hw'.1 fun d hd => hown d (Or.inl hd))
  | syncSucc _ ih =>
    intro hw' hown
    simp only [Expr.refs, List.mem_append] at hown
    exact .syncSucc (ih hw'.2 fun d hd => hown d (Or.inr hd))
  | foldNil _ _ _ ihf ihz ihl =>
    intro hw' hown
    simp only [Expr.refs, List.mem_append] at hown
    exact .foldNil (ihf hw'.1 fun d hd => hown d (Or.inl (Or.inl hd)))
      (ihz hw'.2.1 fun d hd => hown d (Or.inl (Or.inr hd))) (ihl hw'.2.2 fun d hd => hown d (Or.inr hd))
  | foldCons hf hz hl hr hv ihf ihz ihl _ _ =>
    intro hw' hown
    simp only [Expr.refs, List.mem_append] at hown
    have hwk := instΔ_wiring c mono eq ps hw k
    exact Ev.foldCons_move (ihf hw'.1 fun d hd => hown d (Or.inl (Or.inl hd)))
      (ihz hw'.2.1 fun d hd => hown d (Or.inl (Or.inr hd))) (ihl hw'.2.2 fun d hd => hown d (Or.inr hd))
      hr hv hwk hI' (Ev.noClo hwk hI' hf hw'.1) (Ev.noClo hwk hI' hz hw'.2.1) (Ev.noClo hwk hI' hl hw'.2.2)

/-- **Theorem J (restricted).**  Under a consistent modular input, the
    modular and the flattened semantics agree on every declaration of every
    instance; in particular the modular value is unique and is the
    flattened value. -/
theorem modular_iff_flat (c : ComposeWF ev S) (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound)
    (hdir : DirectOnly S) (hw : DeclEnvWiring S.flattenΔ) {I I' : Input}
    (hI : ∀ d t, (I d t).NoClo) (hI' : ∀ d t, (I' d t).NoClo) (hc : Consistent S I I')
    (htot : ∀ d, (∃ h, S.flattenΔ d = some h) → ∀ t, ∃ v, Ev S.flattenΔ I t [] (.declRef d) v)
    {k : Nat} {d : DeclId} (hown : S.Owns k d) (t : Nat) (v : Value) :
    Ev (S.instΔ k) I' t [] (.declRef d) v ↔ Ev S.flattenΔ I t [] (.declRef d) v :=
  ⟨fun h => eval_inst_to_flat c mono eq ps hdir hw hI hI' hc htot h (by simp [Expr.Wiring])
      (fun x hx => by simp only [Expr.refs, List.mem_singleton] at hx; subst hx; exact hown),
   fun h => eval_flat_to_inst c mono eq ps hdir hw hI hc h (by simp [Expr.Wiring]) k
      (fun x hx => by simp only [Expr.refs, List.mem_singleton] at hx; subst hx; exact hown)⟩

/-- Totality of the flattened design, from Phase 4's `reactive_total`, under
    the composition hypotheses and an acyclic inter-instance graph. -/
theorem flatten_total (c : ComposeWF ev S) (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound)
    (hacyc : InstAcyclic S) {I : Input}
    (hRed : ∀ d τ t, S.flattenΔ.tyView d = some τ → S.flattenΔ.realizationOf d = none →
      Red S.unionΘ (Apply S.flattenΔ I t) τ (I d t)) :
    ∀ d, (∃ h, S.flattenΔ d = some h) → ∀ t, ∃ v, Ev S.flattenΔ I t [] (.declRef d) v := by
  intro d hd t
  obtain ⟨h, hh⟩ := hd
  obtain ⟨v, hv, -⟩ := reactive_total (unionΘ_WF c) (flatten_causal c mono eq ps hacyc) (flatten_globalWF c mono eq ps)
    hRed (d := d) (τ := h.interface.expectedType) (by show S.flattenΔ.tyView d = _; simp [DeclEnv.tyView, hh]) t
  exact ⟨v, hv⟩

end BehaviorSystem
end BDL
