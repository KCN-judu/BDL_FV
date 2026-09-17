import BDL.Behavior.Extract
import BDL.Behavior.Semantics

/-!
# ExtractPreservation — "Package as Component" preserves the design

Theorems M–R of Phase 8b.  The extracted system is a Phase-8a system, so
its flattening is well formed by the Phase-8a theorems once `ComposeWF` is
established (M, N, P, Q).  Causality (O) needs its own argument: the
inter-instance graph of an extraction has edges in *both* directions
whenever the group has both inputs and outputs, so the coarse Phase-8a
condition does not apply; instead the flattened instantaneous graph is the
original graph with each crossing edge subdivided through a port copy, and
a rank for it is built from the original rank.  Semantic preservation (R)
is proved on the single-domain wiring fragment of Phase 8a.

One further evidence condition appears: `Evidence.InterfaceLocal` — a
discharged commitment depends only on the *interfaces* of the declarations
the term refers to.  It is what lets a member's commitment, discharged in
the whole design, remain discharged inside the template, where the
declarations it refers to are present only as unresolved port copies.
-/

namespace BDL
open BDL.Output (OutputId OutputSpec DriveWF SingleDriver)
open BDL.Clock (ClockEnv Clocked WellClocked clockedB)
open BDL.Reactive
open Boundary

/-- Evidence depending only on the interfaces of the referenced declarations. -/
def Evidence.InterfaceLocal (ev : Evidence) : Prop :=
  ∀ (Δ Δ' : DeclEnv) (e : Expr) (p : PropertyId),
    (∀ d ∈ e.refs, ∀ h, Δ d = some h → ∃ h', Δ' d = some h' ∧ h'.interface = h.interface) →
    ev Δ e p → ev Δ' e p

/-- Typing depends on the type view of the *referenced* declarations only. -/
theorem HasType.mono_env_refs {Θ : ConceptEnv} {Δ₁ Δ₂ : DeclEnv} {G : Grant}
    {Γ : Ctx} {e : Expr} {τ : Ty}
    (hv : ∀ d ∈ e.refs, ∀ τ', Δ₁.tyView d = some τ' → Δ₂.tyView d = some τ')
    (h : HasType Θ Δ₁ G Γ e τ) : HasType Θ Δ₂ G Γ e τ := by
  induction h with
  | var h => exact .var h
  | boolLit => exact .boolLit
  | natLit => exact .natLit
  | lam _ ih => exact .lam (ih hv)
  | app _ _ ihf iha =>
    simp only [Expr.refs, List.mem_append] at hv
    exact .app (ihf fun d hd => hv d (Or.inl hd)) (iha fun d hd => hv d (Or.inr hd))
  | declRef h => exact .declRef (hv _ (by simp [Expr.refs]) _ h)
  | rep hΘ _ ih => exact .rep hΘ (ih hv)
  | mk hg hΘ _ ih => exact .mk hg hΘ (ih hv)
  | prim => exact .prim
  | delay hd _ _ ihi ihe =>
    simp only [Expr.refs, List.mem_append] at hv
    exact .delay hd (ihi fun d hd => hv d (Or.inl hd)) (ihe fun d hd => hv d (Or.inr hd))
  | sync hd _ _ ihi ihe =>
    simp only [Expr.refs, List.mem_append] at hv
    exact .sync hd (ihi fun d hd => hv d (Or.inl hd)) (ihe fun d hd => hv d (Or.inr hd))

/-- The domain judgment depends on the clocks of the referenced declarations only. -/
theorem Clock.clockedB_congr {Κ Κ' : ClockEnv} :
    ∀ (c : Option ClockId) (e : Expr), (∀ d ∈ e.refs, Κ d = Κ' d) → clockedB Κ c e = clockedB Κ' c e
  | _, .var _, _ | _, .boolLit _, _ | _, .natLit _, _ | _, .prim _, _ => rfl
  | c, .lam _ b, h => Clock.clockedB_congr c b h
  | c, .app f a, h => by
    simp only [Expr.refs, List.mem_append] at h
    simp only [clockedB, Clock.clockedB_congr c f (fun d hd => h d (Or.inl hd)),
      Clock.clockedB_congr c a (fun d hd => h d (Or.inr hd))]
  | c, .declRef d, h => by simp [clockedB, h d (by simp [Expr.refs])]
  | c, .rep e, h => Clock.clockedB_congr c e h
  | c, .mk _ e, h => Clock.clockedB_congr c e h
  | some c, .delay i e, h => by
    simp only [Expr.refs, List.mem_append] at h
    simp only [clockedB, Clock.clockedB_congr (some c) i (fun d hd => h d (Or.inl hd)),
      Clock.clockedB_congr (some c) e (fun d hd => h d (Or.inr hd))]
  | none, .delay _ _, _ => rfl
  | some c, .sync c' i e, h => by
    simp only [Expr.refs, List.mem_append] at h
    simp only [clockedB, Clock.clockedB_congr (some c) i (fun d hd => h d (Or.inl hd)),
      Clock.clockedB_congr (some c') e (fun d hd => h d (Or.inr hd))]
  | none, .sync _ _ _, _ => rfl

namespace Extract

/-! ## A restriction realizes its template interface -/

section Restrict

variable {ev : Evidence} {D : Design} {ids : List DeclId} {keep port : DeclId → Bool}
  {required provided : List DeclId} {clocks : List ClockId} {W : Nat}

/-- The conditions under which `template D keep port …` realizes its interface. -/
structure RestrictWF (ev : Evidence) (D : Design) (ids : List DeclId) (keep port : DeclId → Bool)
    (required provided : List DeclId) (clocks : List ClockId) (W : Nat) : Prop where
  wf : D.WF ev
  enum : D.Enumerates ids
  hkeep : ∀ d, keep d = true → d ∈ ids
  hport : ∀ d, port d = true → d ∈ ids ∧ keep d = false
  /-- Every dependency of a kept declaration is kept or a port. -/
  hclosed : ∀ a b, keep a = true → DependsOn D.Δ a b → keep b = true ∨ port b = true
  hreq : ∀ r ∈ required, port r = true
  hprov : ∀ q ∈ provided, keep q = true
  bound : ∀ d ∈ ids, d.n < W
  kDeclared : ∀ d c, D.Κ d = some c → d ∈ ids
  cover : ∀ d c, D.Κ d = some c → c ∈ clocks
  loc : ev.InterfaceLocal

theorem restrictΔ_keep {d : DeclId} (h : keep d = true) : restrictΔ D keep port d = D.Δ d := by
  simp [restrictΔ, h]

theorem restrictΔ_port {d : DeclId} (hk : keep d = false) (hp : port d = true) :
    restrictΔ D keep port d = (D.Δ d).map unresolve := by
  simp [restrictΔ, hk, hp]

theorem restrictΔ_none {d : DeclId} (hk : keep d = false) (hp : port d = false) :
    restrictΔ D keep port d = none := by
  simp [restrictΔ, hk, hp]

theorem restrictΔ_tyView {d : DeclId} (h : keep d = true ∨ port d = true) :
    (restrictΔ D keep port).tyView d = D.Δ.tyView d := by
  cases hk : keep d with
  | true => rw [DeclEnv.tyView, restrictΔ_keep hk]; rfl
  | false =>
    have hp : port d = true := by
      rcases h with h | h
      · rw [hk] at h; exact nomatch h
      · exact h
    rw [DeclEnv.tyView, restrictΔ_port hk hp, DeclEnv.tyView]
    cases D.Δ d <;> rfl

theorem restrictΔ_some {d : DeclId} {h : DesignDecl} (hd : restrictΔ D keep port d = some h) :
    (keep d = true ∧ D.Δ d = some h) ∨
    (keep d = false ∧ port d = true ∧ ∃ h₀, D.Δ d = some h₀ ∧ h = unresolve h₀) := by
  unfold restrictΔ at hd
  cases hk : keep d with
  | true => rw [hk] at hd; simp at hd; exact Or.inl ⟨rfl, hd⟩
  | false =>
    rw [hk] at hd
    cases hp : port d with
    | true =>
      rw [hp] at hd; simp only [if_true, if_false, Bool.false_eq_true, Option.map_eq_some_iff] at hd
      obtain ⟨h₀, hh, rfl⟩ := hd
      exact Or.inr ⟨rfl, rfl, h₀, hh, rfl⟩
    | false => rw [hp] at hd; simp at hd

theorem restrictΔ_realizationOf {d : DeclId} {e : Expr} (hd : (restrictΔ D keep port).realizationOf d = some e) :
    keep d = true ∧ D.Δ.realizationOf d = some e := by
  simp only [DeclEnv.realizationOf, Option.bind_eq_some_iff] at hd
  obtain ⟨h, hh, hre⟩ := hd
  rcases restrictΔ_some hh with ⟨hk, hD⟩ | ⟨-, -, h₀, -, rfl⟩
  · exact ⟨hk, by simp [DeclEnv.realizationOf, hD, hre]⟩
  · simp [unresolve] at hre

theorem restrictΚ_of {d : DeclId} (h : keep d = true ∨ port d = true) :
    restrictΚ D keep port d = D.Κ d := by
  unfold restrictΚ
  rcases h with h | h <;> simp [h]

/-- The references of a kept realized declaration are kept or ports. -/
theorem refs_kept_or_port (R : RestrictWF ev D ids keep port required provided clocks W)
    {d : DeclId} {e : Expr} (hk : keep d = true) (he : D.Δ.realizationOf d = some e) :
    ∀ x ∈ e.refs, keep x = true ∨ port x = true :=
  fun x hx => R.hclosed d x hk (DependsOn.iff.mpr ⟨e, he, hx⟩)

/-- Every declared identity of `D` with a clock is declared. -/
theorem declared_of_mem (R : RestrictWF ev D ids keep port required provided clocks W) {d : DeclId}
    (h : d ∈ ids) : ∃ h', D.Δ d = some h' := (R.enum.2 d).mpr h

/-- **Theorem (template realization).**  A closed restriction of a
    well-formed design realizes its inferred interface. -/
theorem restrict_realizes (R : RestrictWF ev D ids keep port required provided clocks W) :
    (template D keep port required provided clocks W).Realizes ev := by
  have hrefs : ∀ d e, D.Δ.realizationOf d = some e → keep d = true →
      ∀ x ∈ e.refs, (restrictΔ D keep port).tyView x = D.Δ.tyView x :=
    fun d e he hk x hx => restrictΔ_tyView (refs_kept_or_port R hk he x hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only [template, restrict]
  · -- Design.WF of the restriction
    refine ⟨?_, R.wf.concepts, ?_, ?_, ?_, ?_⟩
    · -- global well-formedness
      intro id h hh
      rcases restrictΔ_some hh with ⟨hk, hD⟩ | ⟨-, -, h₀, hD, rfl⟩
      · refine ⟨R.wf.global.stored_id hD, ?_⟩
        intro e he
        have hre : D.Δ.realizationOf id = some e := by simp [DeclEnv.realizationOf, hD, he]
        obtain ⟨ht, hc⟩ := R.wf.global.wellFormed hD e he
        refine ⟨ht.mono_env_refs fun x hx τ' hτ => by rw [hrefs id e hre hk x hx]; exact hτ, ?_⟩
        intro p hp
        refine R.loc D.Δ _ e p ?_ (hc p hp)
        intro x hx hx' hDx
        have := refs_kept_or_port R hk hre x hx
        rcases this with hkx | hpx
        · exact ⟨hx', by show restrictΔ D keep port x = _; rw [restrictΔ_keep hkx]; exact hDx, rfl⟩
        · cases hkx : keep x with
          | true => exact ⟨hx', by show restrictΔ D keep port x = _; rw [restrictΔ_keep hkx]; exact hDx, rfl⟩
          | false =>
            exact ⟨unresolve hx', by show restrictΔ D keep port x = _; rw [restrictΔ_port hkx hpx, hDx]; rfl, rfl⟩
      · refine ⟨?_, fun _ h => nomatch h⟩
        show h₀.id = id
        exact R.wf.global.stored_id hD
    · -- well clocked
      intro d b hb
      obtain ⟨hk, hre⟩ := restrictΔ_realizationOf hb
      have hcl := R.wf.clocked d b hre
      show Clocked (restrictΚ D keep port) (restrictΚ D keep port d) b
      rw [restrictΚ_of (Or.inl hk)]
      unfold Clocked
      rw [Clock.clockedB_congr _ _ (fun x hx => restrictΚ_of (refs_kept_or_port R hk hre x hx))]
      exact hcl
    · -- causal: a subgraph of the original
      obtain ⟨rank, Rb, hRb, hr⟩ := R.wf.causal
      refine ⟨rank, Rb, hRb, ?_⟩
      intro a b hab
      obtain ⟨e, he, hb⟩ := InstDependsOn.iff.mp hab
      obtain ⟨-, hre⟩ := restrictΔ_realizationOf he
      exact hr a b (InstDependsOn.iff.mpr ⟨e, hre, hb⟩)
    · -- drives
      intro d o hβ
      simp only [restrictβ] at hβ
      cases hk : keep d with
      | false => rw [hk] at hβ; exact nomatch hβ
      | true =>
        rw [hk] at hβ; simp only [if_true] at hβ
        obtain ⟨spec, hΩ, htv, hK⟩ := R.wf.drives d o hβ
        refine ⟨spec, hΩ, ?_, ?_⟩
        · show (restrictΔ D keep port).tyView d = _
          rw [restrictΔ_tyView (Or.inl hk)]; exact htv
        · show restrictΚ D keep port d = _
          rw [restrictΚ_of (Or.inl hk)]; exact hK
    · -- single driver
      intro d₁ d₂ o h₁ h₂
      simp only [restrictβ] at h₁ h₂
      cases hk₁ : keep d₁ with
      | false => rw [hk₁] at h₁; exact nomatch h₁
      | true =>
        rw [hk₁] at h₁; simp only [if_true] at h₁
        cases hk₂ : keep d₂ with
        | false => rw [hk₂] at h₂; exact nomatch h₂
        | true =>
          rw [hk₂] at h₂; simp only [if_true] at h₂
          exact R.wf.single d₁ d₂ o h₁ h₂
  · -- declarations bounded
    intro d h hd
    rcases restrictΔ_some hd with ⟨hk, -⟩ | ⟨-, hp, -⟩
    · exact R.bound d (R.hkeep d hk)
    · exact R.bound d (R.hport d hp).1
  · -- internal clocks bounded: there are none
    intro d c hK hi
    simp only [restrictΚ] at hK
    split at hK
    · exfalso
      have := R.cover d c hK
      simp [BehaviorComponent.internalClock, this] at hi
    · exact nomatch hK
  · -- clocks are declared
    intro d c hK
    simp only [restrictΚ] at hK
    split at hK
    · rename_i hkp
      obtain ⟨h', hh'⟩ := declared_of_mem R (R.kDeclared d c hK)
      rcases Bool.or_eq_true_iff.mp hkp with hk | hp
      · exact ⟨h', by rw [restrictΔ_keep hk]; exact hh'⟩
      · exact ⟨unresolve h', by rw [restrictΔ_port (R.hport d hp).2 hp, hh']; rfl⟩
    · exact nomatch hK
  · intro s R' _ hi; simp at hi
  · intro o spec _ hi; simp at hi
  · -- drives are declared
    intro d o hβ
    simp only [restrictβ] at hβ
    cases hk : keep d with
    | false => rw [hk] at hβ; exact nomatch hβ
    | true =>
      rw [hk] at hβ; simp only [if_true] at hβ
      obtain ⟨spec, -, htv, -⟩ := R.wf.drives d o hβ
      simp only [DeclEnv.tyView, Option.map_eq_some_iff] at htv
      obtain ⟨h', hh', -⟩ := htv
      exact ⟨h', by rw [restrictΔ_keep hk]; exact hh'⟩
  · -- required ports
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    have hpr := R.hreq r hr
    obtain ⟨hr', hkr⟩ := R.hport r hpr
    obtain ⟨h', hh'⟩ := declared_of_mem R hr'
    have hid := R.wf.global.stored_id hh'
    refine ⟨?_, ?_⟩
    · show restrictΔ D keep port r = _
      rw [restrictΔ_port hkr hpr, hh']
      simp [unresolve, portOf, hh', hid]
    · show restrictΚ D keep port r = _
      rw [restrictΚ_of (Or.inr hpr)]; rfl
  · -- provided ports
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hkq := R.hprov q hq
    obtain ⟨h', hh'⟩ := declared_of_mem R (R.hkeep q hkq)
    refine ⟨⟨h', ?_, ?_⟩, ?_⟩
    · show restrictΔ D keep port q = _
      rw [restrictΔ_keep hkq]; exact hh'
    · simp [portOf, hh']
    · show restrictΚ D keep port q = _
      rw [restrictΚ_of (Or.inl hkq)]; rfl
  · intro p hp; simp at hp

end Restrict


/-! ## The extraction input, and its two templates -/

namespace Input

variable {ev : Evidence} {X : Input}

/-- The conditions on an extraction input. -/
structure WF (ev : Evidence) (X : Input) : Prop where
  wf : X.D.WF ev
  enum : X.D.Enumerates X.ids
  members : ∀ d ∈ X.G, d ∈ X.ids
  nodupG : X.G.Nodup
  widthPos : 0 < X.W
  boundIds : ∀ d ∈ X.ids, d.n < X.W
  boundSem : ∀ s R, X.D.Θ s = some R → s.n < X.W
  kDeclared : ∀ d c, X.D.Κ d = some c → d ∈ X.ids
  cover : ∀ d c, X.D.Κ d = some c → c ∈ X.clocks
  sinkClocks : ∀ o spec, X.D.Ω o = some spec → spec.clock ∈ X.clocks
  boundClocks : ∀ c ∈ X.clocks, c.n < X.W
  boundOut : ∀ o spec, X.D.Ω o = some spec → o.n < X.W
  loc : ev.InterfaceLocal

/-- A dependency target is declared (typing declares every reference). -/
theorem dep_declared (H : WF ev X) {a b : DeclId} (h : DependsOn X.D.Δ a b) : b ∈ X.ids := by
  obtain ⟨e, he, hb⟩ := DependsOn.iff.mp h
  simp only [DeclEnv.realizationOf, Option.bind_eq_some_iff] at he
  obtain ⟨h', hh', hre⟩ := he
  have ht := (H.wf.global.wellFormed hh' e hre).1
  obtain ⟨τ, hτ⟩ := ht.refs_declared b hb
  simp only [DeclEnv.tyView, Option.map_eq_some_iff] at hτ
  obtain ⟨hb', hhb, -⟩ := hτ
  exact (H.enum.2 b).mp ⟨hb', hhb⟩

theorem comp_restrictWF (H : WF ev X) :
    RestrictWF ev X.D X.ids X.isMember X.isCrossIn (crossIn X.D X.ids X.G) (crossOut X.D X.ids X.G) X.clocks X.W where
  wf := H.wf
  enum := H.enum
  hkeep := fun d hd => H.members d ((X.isMember_iff).mp hd)
  hport := fun d hd => by
    have h := (X.isCrossIn_iff).mp hd
    exact ⟨((mem_crossIn _ _ _).mp h).1, X.crossIn_not_member h⟩
  hclosed := fun a b ha hab => by
    by_cases hb : b ∈ X.G
    · exact Or.inl ((X.isMember_iff).mpr hb)
    · right
      apply (X.isCrossIn_iff).mpr
      exact (mem_crossIn _ _ _).mpr ⟨dep_declared H hab, hb, a, (X.isMember_iff).mp ha, hab⟩
  hreq := fun r hr => (X.isCrossIn_iff).mpr hr
  hprov := fun q hq => (X.isMember_iff).mpr ((mem_crossOut _ _ _).mp hq).1
  bound := H.boundIds
  kDeclared := H.kDeclared
  cover := H.cover
  loc := H.loc

theorem resid_restrictWF (H : WF ev X) :
    RestrictWF ev X.D X.ids X.isOutside X.isCrossOut (crossOut X.D X.ids X.G) (crossIn X.D X.ids X.G) X.clocks X.W where
  wf := H.wf
  enum := H.enum
  hkeep := fun d hd => ((X.isOutside_iff).mp hd).1
  hport := fun d hd => by
    have h := (X.isCrossOut_iff).mp hd
    exact ⟨H.members d ((mem_crossOut _ _ _).mp h).1, X.crossOut_not_outside h⟩
  hclosed := fun a b ha hab => by
    have hb := dep_declared H hab
    by_cases hbG : b ∈ X.G
    · right
      apply (X.isCrossOut_iff).mpr
      obtain ⟨ha₁, ha₂⟩ := (X.isOutside_iff).mp ha
      exact (mem_crossOut _ _ _).mpr ⟨hbG, a, ha₁, ha₂, hab⟩
    · exact Or.inl ((X.isOutside_iff).mpr ⟨hb, hbG⟩)
  hreq := fun r hr => (X.isCrossOut_iff).mpr hr
  hprov := fun q hq => by
    obtain ⟨hq₁, hq₂, -⟩ := (mem_crossIn _ _ _).mp hq
    exact (X.isOutside_iff).mpr ⟨hq₁, hq₂⟩
  bound := H.boundIds
  kDeclared := H.kDeclared
  cover := H.cover
  loc := H.loc

theorem comp_realizes (H : WF ev X) : X.comp.Realizes ev := restrict_realizes (comp_restrictWF H)
theorem resid_realizes (H : WF ev X) : X.resid.Realizes ev := restrict_realizes (resid_restrictWF H)

/-! ## The extracted system is a well-formed composition -/

theorem instAt_zero : X.system.instAt 0 = some ⟨X.resid, fun c => c⟩ := rfl
theorem instAt_one : X.system.instAt 1 = some ⟨X.comp, fun c => c⟩ := rfl
theorem instAt_ge {k : Nat} (hk : 2 ≤ k) : X.system.instAt k = none := by
  simp only [BehaviorSystem.instAt, system]
  match k, hk with
  | k + 2, _ => rfl

/-- Both templates have no internal concepts or sinks, and every covered
    clock is a parameter, so the instance renamings fix concepts, sinks,
    and covered clocks. -/
theorem ren_s (_H : WF ev X) (k : Nat) (I : Inst) (hI : X.system.instAt k = some I) :
    (X.system.ren k I).s = fun s => s := by
  funext s
  rcases Nat.lt_or_ge k 2 with hk | hk
  · match k, hk with
    | 0, _ => cases hI; rfl
    | 1, _ => cases hI; rfl
  · rw [instAt_ge hk] at hI; exact nomatch hI

theorem ren_o (_H : WF ev X) (k : Nat) (I : Inst) (hI : X.system.instAt k = some I) :
    (X.system.ren k I).o = fun o => o := by
  funext o
  rcases Nat.lt_or_ge k 2 with hk | hk
  · match k, hk with
    | 0, _ => cases hI; rfl
    | 1, _ => cases hI; rfl
  · rw [instAt_ge hk] at hI; exact nomatch hI

theorem ren_c (_H : WF ev X) (k : Nat) (I : Inst) (hI : X.system.instAt k = some I) {c : ClockId}
    (hc : c ∈ X.clocks) : (X.system.ren k I).c c = c := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have hint : ∀ C : BehaviorComponent, C.iface.clockParams = X.clocks → C.internalClock c = false := by
      intro C hC; simp [BehaviorComponent.internalClock, hC, hc]
    match k, hk with
    | 0, _ => cases hI; simp [BehaviorSystem.ren, Ren.inst, hint X.resid rfl]
    | 1, _ => cases hI; simp [BehaviorSystem.ren, Ren.inst, hint X.comp rfl]
  · rw [instAt_ge hk] at hI; exact nomatch hI

theorem ty_rename_ren_s (H : WF ev X) (k : Nat) (I : Inst) (hI : X.system.instAt k = some I) (τ : Ty) :
    τ.rename (X.system.ren k I).s = τ := by
  rw [ren_s H k I hI]; exact Ty.rename_id τ

/-- **ComposeWF of the extraction.** -/
theorem system_composeWF (H : WF ev X) : BehaviorSystem.ComposeWF ev X.system := by
  have hinst : ∀ k I, X.system.instAt k = some I →
      I.comp.Realizes ev ∧ I.comp.width = X.W ∧ I.comp.iface.clockParams = X.clocks ∧
      I.comp.design.Θ = X.D.Θ ∧ I.comp.design.Ω = X.D.Ω ∧ I.κ = (fun c => c) := by
    intro k I hI
    rcases Nat.lt_or_ge k 2 with hk | hk
    · match k, hk with
      | 0, _ => cases hI; exact ⟨resid_realizes H, rfl, rfl, rfl, rfl, rfl⟩
      | 1, _ => cases hI; exact ⟨comp_realizes H, rfl, rfl, rfl, rfl, rfl⟩
    · rw [instAt_ge hk] at hI; exact nomatch hI
  refine ⟨H.widthPos, ?_, H.wf.concepts, H.boundSem, ?_, ?_, ?_⟩
  · -- InstsWF
    intro k I hI
    obtain ⟨hr, hw, hcp, hΘ, hΩ, hκ⟩ := hinst k I hI
    refine ⟨hr, hw ▸ Nat.le_refl _, ?_, ?_, ?_⟩
    · intro c hc
      rw [hκ]
      apply H.boundClocks
      simpa [BehaviorComponent.internalClock, hcp] using hc
    · intro s R hs _
      rw [hΘ] at hs
      exact ⟨H.boundSem s R hs, by show X.D.Θ s = some R; exact hs⟩
    · intro o spec hΩo _
      rw [hΩ] at hΩo
      refine ⟨H.boundOut o spec hΩo, ?_⟩
      show X.D.Ω o = some (BehaviorSystem.OutputSpec.rename (X.system.ren k I) spec)
      have : BehaviorSystem.OutputSpec.rename (X.system.ren k I) spec = spec := by
        cases spec with
        | mk acc clk =>
          simp only [BehaviorSystem.OutputSpec.rename, ty_rename_ren_s H k I hI,
            ren_c H k I hI (H.sinkClocks o _ hΩo)]
      rw [this]; exact hΩo
  · -- bindings
    intro b hb
    simp only [system, bindings, List.mem_append, List.mem_map] at hb
    rcases hb with ⟨r, hr, rfl⟩ | ⟨p, hp, rfl⟩
    · -- C.r := R.r
      refine ⟨⟨X.comp, fun c => c⟩, rfl, portOf X.D r, ?_, rfl, ⟨X.resid, fun c => c⟩, rfl, portOf X.D r, ?_, rfl, ?_, List.Subset.refl _, ?_⟩
      · show portOf X.D r ∈ (crossIn X.D X.ids X.G).map (portOf X.D) ++ []
        simp [List.mem_map]; exact ⟨r, hr, rfl⟩
      · show portOf X.D r ∈ (crossIn X.D X.ids X.G).map (portOf X.D)
        simp [List.mem_map]; exact ⟨r, hr, rfl⟩
      · rw [ren_s H 0 _ rfl, ren_s H 1 _ rfl]
      · show (portOf X.D r).clock.map (X.system.ren 0 _).c = none ∨
          (portOf X.D r).clock.map (X.system.ren 0 _).c = (portOf X.D r).clock.map (X.system.ren 1 _).c
        right
        show (X.D.Κ r).map _ = (X.D.Κ r).map _
        cases hK : X.D.Κ r with
        | none => rfl
        | some c =>
          have hc := H.cover r c hK
          simp only [Option.map_some, ren_c H 0 _ rfl hc, ren_c H 1 _ rfl hc]
    · -- R.p := C.p
      refine ⟨⟨X.resid, fun c => c⟩, rfl, portOf X.D p, ?_, rfl, ⟨X.comp, fun c => c⟩, rfl, portOf X.D p, ?_, rfl, ?_, List.Subset.refl _, ?_⟩
      · show portOf X.D p ∈ (crossOut X.D X.ids X.G).map (portOf X.D) ++ []
        simp [List.mem_map]; exact ⟨p, hp, rfl⟩
      · show portOf X.D p ∈ (crossOut X.D X.ids X.G).map (portOf X.D)
        simp [List.mem_map]; exact ⟨p, hp, rfl⟩
      · rw [ren_s H 0 _ rfl, ren_s H 1 _ rfl]
      · right
        show (X.D.Κ p).map _ = (X.D.Κ p).map _
        cases hK : X.D.Κ p with
        | none => rfl
        | some c =>
          have hc := H.cover p c hK
          simp only [Option.map_some, ren_c H 0 _ rfl hc, ren_c H 1 _ rfl hc]
  · -- destinations bound at most once
    show ((crossIn X.D X.ids X.G).map (fun r => (⟨.port 0 r, 1, r, none⟩ : Binding)) ++
        (crossOut X.D X.ids X.G).map (fun p => (⟨.port 1 p, 0, p, none⟩ : Binding))).map
        (fun b => X.system.declOf b.dstInst b.dst) |>.Nodup
    rw [List.map_append, List.map_map, List.map_map, List.nodup_append]
    have hIn := crossIn_nodup X.D X.ids X.G H.enum.1
    have hOut := crossOut_nodup X.D X.ids X.G H.nodupG
    have hbIn : ∀ r ∈ crossIn X.D X.ids X.G, r.n < X.W := fun r hr => H.boundIds r ((mem_crossIn _ _ _).mp hr).1
    have hbOut : ∀ p ∈ crossOut X.D X.ids X.G, p.n < X.W :=
      fun p hp => H.boundIds p (H.members p ((mem_crossOut _ _ _).mp hp).1)
    refine ⟨?_, ?_, ?_⟩
    · rw [List.nodup_iff_pairwise_ne] at hIn ⊢
      rw [List.pairwise_map]
      refine hIn.imp_of_mem ?_
      intro a b ha hb hne heq
      simp only [Function.comp, BehaviorSystem.declOf, DeclId.mk.injEq] at heq
      exact hne (by
        have := (fresh_inj H.widthPos (hbIn a ha) (hbIn b hb) heq).2
        cases a; cases b; simp only at this; simp [this])
    · rw [List.nodup_iff_pairwise_ne] at hOut ⊢
      rw [List.pairwise_map]
      refine hOut.imp_of_mem ?_
      intro a b ha hb hne heq
      simp only [Function.comp, BehaviorSystem.declOf, DeclId.mk.injEq] at heq
      exact hne (by
        have := (fresh_inj H.widthPos (hbOut a ha) (hbOut b hb) heq).2
        cases a; cases b; simp only at this; simp [this])
    · intro x hx y hy heq
      simp only [List.mem_map, Function.comp] at hx hy
      obtain ⟨r, hr, rfl⟩ := hx
      obtain ⟨p, hp, rfl⟩ := hy
      simp only [BehaviorSystem.declOf, DeclId.mk.injEq] at heq
      have := (fresh_inj H.widthPos (hbIn r hr) (hbOut p hp) heq).1
      omega
  · -- external sinks: the two templates partition the original drives
    intro k₁ I₁ d₁ k₂ I₂ d₂ o hI₁ hI₂ hβ₁ _ hβ₂ _
    have drive : ∀ k I d, X.system.instAt k = some I → I.comp.design.β d = some o →
        X.D.β d = some o ∧ ((k = 0 ∧ X.isOutside d = true) ∨ (k = 1 ∧ X.isMember d = true)) := by
      intro k I d hI hβ
      rcases Nat.lt_or_ge k 2 with hk | hk
      · match k, hk with
        | 0, _ =>
          cases hI
          simp only [resid, template, restrict, restrictβ] at hβ
          cases ho : X.isOutside d with
          | false => rw [ho] at hβ; exact nomatch hβ
          | true => rw [ho] at hβ; exact ⟨by simpa using hβ, Or.inl ⟨rfl, rfl⟩⟩
        | 1, _ =>
          cases hI
          simp only [comp, template, restrict, restrictβ] at hβ
          cases hm : X.isMember d with
          | false => rw [hm] at hβ; exact nomatch hβ
          | true => rw [hm] at hβ; exact ⟨by simpa using hβ, Or.inr ⟨rfl, rfl⟩⟩
      · rw [instAt_ge hk] at hI; exact nomatch hI
    obtain ⟨hD₁, hk₁⟩ := drive k₁ I₁ d₁ hI₁ hβ₁
    obtain ⟨hD₂, hk₂⟩ := drive k₂ I₂ d₂ hI₂ hβ₂
    have hd : d₁ = d₂ := H.wf.single d₁ d₂ o hD₁ hD₂
    subst hd
    refine ⟨?_, rfl⟩
    rcases hk₁ with ⟨rfl, h₁⟩ | ⟨rfl, h₁⟩ <;> rcases hk₂ with ⟨rfl, h₂⟩ | ⟨rfl, h₂⟩
    · rfl
    · exact absurd ((X.isMember_iff).mp h₂) ((X.isOutside_iff).mp h₁).2
    · exact absurd ((X.isMember_iff).mp h₁) ((X.isOutside_iff).mp h₂).2
    · rfl


/-! ## Theorems M, N, P, Q — the flattened extraction is well formed (by reuse) -/

/-- **Theorem N (typing).** -/
theorem flat_globalWF (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound) (H : WF ev X) :
    GlobalWF ev X.flat.Θ X.flat.Δ :=
  BehaviorSystem.flatten_globalWF (system_composeWF H) mono eq ps

theorem flat_conceptsWF (H : WF ev X) : X.flat.Θ.WF :=
  BehaviorSystem.unionΘ_WF (system_composeWF H)

/-- **Theorem P (clocks).** -/
theorem flat_wellClocked (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound) (H : WF ev X) :
    WellClocked X.flat.Κ X.flat.Δ :=
  BehaviorSystem.flatten_wellClocked (system_composeWF H) mono eq ps

/-- **Theorem Q (outputs).** -/
theorem flat_driveWF (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound) (H : WF ev X) :
    DriveWF X.flat.Ω X.flat.Κ X.flat.Δ X.flat.β :=
  BehaviorSystem.flatten_driveWF (system_composeWF H) mono eq ps

theorem flat_singleDriver (H : WF ev X) : SingleDriver X.flat.β :=
  BehaviorSystem.flatten_singleDriver (system_composeWF H)

/-! ## Theorem O — causality: the original graph, with crossing edges subdivided -/

theorem home_not_bound (H : WF ev X) {d : DeclId} (hd : d ∈ X.ids) :
    ¬ X.system.BoundDst (X.home d) := by
  rintro ⟨b, hb, heq⟩
  simp only [system, bindings, List.mem_append, List.mem_map] at hb
  have hdW := H.boundIds d hd
  rcases hb with ⟨r, hr, rfl⟩ | ⟨p, hp, rfl⟩
  · -- destination `declOf 1 r`, `r ∉ G`; `home d` is `declOf 1 d` only for `d ∈ G`
    have hrW := H.boundIds r ((mem_crossIn _ _ _).mp hr).1
    unfold home at heq
    cases hm : X.isMember d with
    | true =>
      rw [hm] at heq; simp only [if_true] at heq
      simp only [BehaviorSystem.declOf, DeclId.mk.injEq] at heq
      have := (fresh_inj H.widthPos hrW hdW heq).2
      have hne := ((mem_crossIn _ _ _).mp hr).2.1
      apply hne
      have : r = d := by cases r; cases d; simp only at this; simp [this]
      rw [this]; exact (X.isMember_iff).mp hm
    | false =>
      rw [hm] at heq; simp only [Bool.false_eq_true, if_false] at heq
      simp only [BehaviorSystem.declOf, DeclId.mk.injEq] at heq
      have := (fresh_inj H.widthPos hrW hdW heq).1
      omega
  · have hpW := H.boundIds p (H.members p ((mem_crossOut _ _ _).mp hp).1)
    unfold home at heq
    cases hm : X.isMember d with
    | true =>
      rw [hm] at heq; simp only [if_true] at heq
      simp only [BehaviorSystem.declOf, DeclId.mk.injEq] at heq
      have := (fresh_inj H.widthPos hpW hdW heq).1
      omega
    | false =>
      rw [hm] at heq; simp only [Bool.false_eq_true, if_false] at heq
      simp only [BehaviorSystem.declOf, DeclId.mk.injEq] at heq
      have := (fresh_inj H.widthPos hpW hdW heq).2
      have hpG := ((mem_crossOut _ _ _).mp hp).1
      have : p = d := by cases p; cases d; simp only at this; simp [this]
      rw [this] at hpG
      exact absurd ((X.isMember_iff).mpr hpG) (by simp [hm])

/-- The flattened home copy of an original declaration is its renamed
    original. -/
theorem flat_home (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound) (H : WF ev X)
    {d : DeclId} (hd : d ∈ X.ids) :
    X.flat.Δ (X.home d) =
      (X.D.Δ d).map (DesignDecl.rename (X.system.ren (if X.isMember d then 1 else 0)
        (if X.isMember d then ⟨X.comp, fun c => c⟩ else ⟨X.resid, fun c => c⟩))) := by
  have c := system_composeWF H
  show X.system.flattenΔ (X.home d) = _
  rw [BehaviorSystem.flattenΔ_unbound c mono eq ps (home_not_bound H hd)]
  have hdW := H.boundIds d hd
  unfold home
  cases hm : X.isMember d with
  | true =>
    simp only [if_true]
    rw [BehaviorSystem.unionΔ_fresh c.width instAt_one hdW]
    show ((restrictΔ X.D X.isMember X.isCrossIn) d).map _ = _
    rw [restrictΔ_keep hm]
  | false =>
    simp only [Bool.false_eq_true, if_false]
    rw [BehaviorSystem.unionΔ_fresh c.width instAt_zero hdW]
    show ((restrictΔ X.D X.isOutside X.isCrossOut) d).map _ = _
    have ho : X.isOutside d = true := (X.isOutside_iff).mpr ⟨hd, by simpa [isMember] using hm⟩
    rw [restrictΔ_keep ho]

/-- **Theorem (open members stay open).**  An unresolved member is an
    unresolved declaration of the flattened extraction (progressive
    formalization survives packaging). -/
theorem flat_open_member (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound) (H : WF ev X)
    {d : DeclId} (hd : d ∈ X.ids) (ho : X.D.Open d) : X.flat.Open (X.home d) := by
  obtain ⟨h, hh, hre⟩ := ho
  refine ⟨h.rename (X.system.ren (if X.isMember d then 1 else 0)
    (if X.isMember d then ⟨X.comp, fun c => c⟩ else ⟨X.resid, fun c => c⟩)), ?_, by simp [DesignDecl.rename, hre]⟩
  rw [flat_home mono eq ps H hd, hh]; rfl

/-- The flattened rank: the original rank doubled, plus one on port copies. -/
def flatRank (rank : DeclId → Nat) : DeclId → Nat := fun id =>
  match decode X.W id.n with
  | some (0, n) => if X.isMember ⟨n⟩ then 2 * rank ⟨n⟩ + 1 else 2 * rank ⟨n⟩
  | some (1, n) => if X.isMember ⟨n⟩ then 2 * rank ⟨n⟩ else 2 * rank ⟨n⟩ + 1
  | _ => 0

theorem flatRank_zero (H : WF ev X) (rank : DeclId → Nat) {d : DeclId} (hd : d.n < X.W) :
    X.flatRank rank (X.system.declOf 0 d) = if X.isMember d then 2 * rank d + 1 else 2 * rank d := by
  show (match decode X.W (fresh X.W 0 d.n) with
    | some (0, n) => if X.isMember ⟨n⟩ then 2 * rank ⟨n⟩ + 1 else 2 * rank ⟨n⟩
    | some (1, n) => if X.isMember ⟨n⟩ then 2 * rank ⟨n⟩ else 2 * rank ⟨n⟩ + 1
    | _ => 0) = _
  rw [decode_fresh H.widthPos hd]
  cases d; rfl

theorem flatRank_one (H : WF ev X) (rank : DeclId → Nat) {d : DeclId} (hd : d.n < X.W) :
    X.flatRank rank (X.system.declOf 1 d) = if X.isMember d then 2 * rank d else 2 * rank d + 1 := by
  show (match decode X.W (fresh X.W 1 d.n) with
    | some (0, n) => if X.isMember ⟨n⟩ then 2 * rank ⟨n⟩ + 1 else 2 * rank ⟨n⟩
    | some (1, n) => if X.isMember ⟨n⟩ then 2 * rank ⟨n⟩ else 2 * rank ⟨n⟩ + 1
    | _ => 0) = _
  rw [decode_fresh H.widthPos hd]
  cases d; rfl

theorem flatRank_bound (rank : DeclId → Nat) (R : Nat) (hR : ∀ d, rank d < R) (id : DeclId) :
    X.flatRank rank id < 2 * R + 2 := by
  unfold flatRank
  split
  · rename_i n _; split <;> (have := hR ⟨n⟩; omega)
  · rename_i n _; split <;> (have := hR ⟨n⟩; omega)
  · omega

/-- **Theorem O.**  The flattened extraction is causal: its instantaneous
    graph is the original one with every crossing edge subdivided through
    a port copy, and the doubled rank witnesses it.  No acyclicity
    condition on the inter-instance graph is needed (and none would hold:
    a group with both inputs and outputs has instance edges both ways). -/
theorem flat_causal (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound) (H : WF ev X) :
    Causal X.flat.Δ := by
  have c := system_composeWF H
  obtain ⟨rank, R, hR, hr⟩ := H.wf.causal
  refine ⟨X.flatRank rank, 2 * R + 2, flatRank_bound rank R hR, ?_⟩
  intro a b hab
  obtain ⟨e, he, hb⟩ := InstDependsOn.iff.mp hab
  rcases BehaviorSystem.flatten_body c mono eq ps he with
    ⟨k, I, n, h, e₀, hI, hΔ, he₀, rfl, hn, rfl, -⟩ | ⟨b', hbm, rfl, rfl, -, -, -, -, -⟩
  · -- an edge inside one side: an original edge
    rw [Expr.rename_instRefs, List.mem_map] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    have hreal : I.comp.design.Δ.realizationOf ⟨n⟩ = some e₀ := by simp [DeclEnv.realizationOf, hΔ, he₀]
    -- the template's realization is the original's, on a kept declaration
    have key : ∀ keep port, I.comp.design = restrict X.D keep port →
        keep ⟨n⟩ = true ∧ X.D.Δ.realizationOf ⟨n⟩ = some e₀ := by
      intro keep port hd
      have : (restrictΔ X.D keep port).realizationOf ⟨n⟩ = some e₀ := by rw [← hreal, hd]; rfl
      exact restrictΔ_realizationOf this
    have hedge : InstDependsOn X.D.Δ ⟨n⟩ x := by
      rcases Nat.lt_or_ge k 2 with hk | hk
      · match k, hk with
        | 0, _ => cases hI; exact InstDependsOn.iff.mpr ⟨e₀, (key _ _ rfl).2, hx⟩
        | 1, _ => cases hI; exact InstDependsOn.iff.mpr ⟨e₀, (key _ _ rfl).2, hx⟩
      · rw [instAt_ge hk] at hI; exact nomatch hI
    have hlt := hr _ _ hedge
    have hxW : x.n < X.W := H.boundIds x (dep_declared H hedge.toDependsOn)
    rw [BehaviorSystem.ren_d]
    rcases Nat.lt_or_ge k 2 with hk | hk
    · match k, hk with
      | 0, _ =>
        cases hI
        have hkeep := (key _ _ rfl).1
        rw [flatRank_zero H rank hn, flatRank_zero H rank hxW]
        have hnm : X.isMember ⟨n⟩ = false := by
          have := ((X.isOutside_iff).mp hkeep).2; simpa [isMember] using this
        rw [hnm]; simp only [Bool.false_eq_true, if_false]
        split <;> omega
      | 1, _ =>
        cases hI
        have hkeep := (key _ _ rfl).1
        rw [flatRank_one H rank hn, flatRank_one H rank hxW, hkeep]
        simp only [if_true]
        split <;> omega
    · rw [instAt_ge hk] at hI; exact nomatch hI
  · -- a binding edge: port copy → home copy
    simp only [system, bindings, List.mem_append, List.mem_map] at hbm
    rcases hbm with ⟨r, hr', rfl⟩ | ⟨p, hp', rfl⟩
    · have hbody : X.system.bindingBody ⟨.port 0 r, 1, r, none⟩ = .declRef (X.system.declOf 0 r) := rfl
      rw [hbody] at hb
      simp only [Expr.instRefs, List.mem_singleton] at hb
      subst hb
      have hrW := H.boundIds r ((mem_crossIn _ _ _).mp hr').1
      have hnm : X.isMember r = false := X.crossIn_not_member hr'
      show X.flatRank rank (X.system.declOf 0 r) < X.flatRank rank (X.system.declOf 1 r)
      rw [flatRank_zero H rank hrW, flatRank_one H rank hrW, hnm]
      simp
    · have hbody : X.system.bindingBody ⟨.port 1 p, 0, p, none⟩ = .declRef (X.system.declOf 1 p) := rfl
      rw [hbody] at hb
      simp only [Expr.instRefs, List.mem_singleton] at hb
      subst hb
      have hpG := ((mem_crossOut _ _ _).mp hp').1
      have hpW := H.boundIds p (H.members p hpG)
      have hm : X.isMember p = true := (X.isMember_iff).mpr hpG
      show X.flatRank rank (X.system.declOf 1 p) < X.flatRank rank (X.system.declOf 0 p)
      rw [flatRank_zero H rank hpW, flatRank_one H rank hpW, hm]
      simp

/-- **Theorem M.**  The flattened extraction is a structurally well-formed
    design. -/
theorem flat_WF (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound) (H : WF ev X) : X.flat.WF ev where
  global := flat_globalWF mono eq ps H
  concepts := flat_conceptsWF H
  clocked := flat_wellClocked mono eq ps H
  causal := flat_causal mono eq ps H
  drives := flat_driveWF mono eq ps H
  single := flat_singleDriver H


/-! ## Theorem R — extraction preserves behaviour (single-domain wiring fragment) -/

/-- The side of an original declaration: 1 for members, 0 for the rest. -/
def side (d : DeclId) : Nat := if X.isMember d then 1 else 0

def instOf (k : Nat) : Inst := if k = 1 then ⟨X.comp, fun c => c⟩ else ⟨X.resid, fun c => c⟩

def renOf (k : Nat) : Ren := X.system.ren k (X.instOf k)

theorem home_eq (d : DeclId) : X.home d = X.system.declOf (X.side d) d := by
  unfold home side
  cases X.isMember d <;> rfl

theorem renOf_d (k : Nat) (d : DeclId) : (X.renOf k).d d = X.system.declOf k d := rfl

theorem renOf_s (k : Nat) : (X.renOf k).s = fun s => s := by
  funext s; unfold renOf instOf; split <;> rfl

theorem _root_.BDL.Prim.rename_id : ∀ p : Prim, p.rename (fun s => s) = p
  | .lit _ _ | .add _ | .sub _ | .mul _ _ | .div _ _ | .lt _ | .eq _ | .not | .and | .or => rfl
  | .ite τ | .none τ | .some τ | .isSome τ | .getD τ => by simp [Prim.rename, Ty.rename_id]
  | .nil τ | .cons τ | .length τ | .take τ | .reverse τ | .head τ => by simp [Prim.rename, Ty.rename_id]

/-- `d` is visible on side `k`: it is declared on that side, either as its
    home copy or as a port copy. -/
def Visible (k : Nat) (d : DeclId) : Prop :=
  d ∈ X.ids ∧ (k = X.side d ∨ (k = 1 ∧ d ∈ crossIn X.D X.ids X.G) ∨ (k = 0 ∧ d ∈ crossOut X.D X.ids X.G))

/-- The flattened input: every copy of an original declaration reads the
    original input. -/
def liftInput (I : Reactive.Input) : Reactive.Input := fun id t =>
  match decode X.W id.n with
  | some (_, n) => I ⟨n⟩ t
  | none => I id t

theorem liftInput_declOf (H : WF ev X) (I : Reactive.Input) (k : Nat) {d : DeclId} (hd : d.n < X.W) (t : Nat) :
    X.liftInput I (X.system.declOf k d) t = I d t := by
  unfold liftInput
  show (match decode X.W (fresh X.W k d.n) with
    | some (_, n) => I ⟨n⟩ t
    | none => I (X.system.declOf k d) t) = _
  rw [decode_fresh H.widthPos hd]

theorem instAt_instOf (k : Nat) (hk : k = 0 ∨ k = 1) : X.system.instAt k = some (X.instOf k) := by
  rcases hk with rfl | rfl <;> rfl

/-- References of a realized original declaration are visible on its side. -/
theorem body_refs_visible (H : WF ev X) {d : DeclId} {b : Expr} (hb : X.D.Δ.realizationOf d = some b) :
    ∀ x ∈ b.refs, X.Visible (X.side d) x := by
  intro x hx
  have hdep : DependsOn X.D.Δ d x := DependsOn.iff.mpr ⟨b, hb, hx⟩
  have hxi := dep_declared H hdep
  have hdi : d ∈ X.ids := by
    simp only [DeclEnv.realizationOf, Option.bind_eq_some_iff] at hb
    obtain ⟨h, hh, -⟩ := hb
    exact (H.enum.2 d).mp ⟨h, hh⟩
  refine ⟨hxi, ?_⟩
  unfold side
  cases hm : X.isMember d with
  | true =>
    cases hmx : X.isMember x with
    | true => left; rfl
    | false =>
      right; left
      refine ⟨rfl, (mem_crossIn _ _ _).mpr ⟨hxi, by simpa [isMember] using hmx, d, (X.isMember_iff).mp hm, hdep⟩⟩
  | false =>
    cases hmx : X.isMember x with
    | false => left; rfl
    | true =>
      right; right
      refine ⟨rfl, (mem_crossOut _ _ _).mpr ⟨(X.isMember_iff).mp hmx, d, hdi, by simpa [isMember] using hm, hdep⟩⟩

theorem flat_realizationOf_home (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound) (H : WF ev X)
    {d : DeclId} (hd : d ∈ X.ids) :
    X.flat.Δ.realizationOf (X.home d) = (X.D.Δ.realizationOf d).map (Expr.rename (X.renOf (X.side d))) := by
  unfold DeclEnv.realizationOf
  rw [flat_home mono eq ps H hd]
  unfold renOf instOf side
  cases X.D.Δ d with
  | none => cases X.isMember d <;> simp
  | some h => cases X.isMember d <;> cases h.realization <;> simp [DesignDecl.rename]

/-- A port copy is realized by a reference to the home copy. -/
theorem flat_port_copy (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound) (H : WF ev X)
    {k : Nat} {d : DeclId} (hk : k = 0 ∨ k = 1) (hv : X.Visible k d) (hne : k ≠ X.side d) :
    X.flat.Δ.realizationOf (X.system.declOf k d) = some (.declRef (X.home d)) := by
  have c := system_composeWF H
  have inv := BehaviorSystem.flatten_inv c mono eq ps
  obtain ⟨-, hv⟩ := hv
  rcases hv with h | ⟨rfl, hin⟩ | ⟨rfl, hout⟩
  · exact absurd h hne
  · have hb : (⟨.port 0 d, 1, d, none⟩ : Binding) ∈ X.system.bindings := by
      simp only [system, bindings, List.mem_append, List.mem_map]; exact Or.inl ⟨d, hin, rfl⟩
    obtain ⟨Id, pd, -, -, -, hΔ⟩ := inv.bound _ hb
    show X.system.flattenΔ.realizationOf (X.system.declOf 1 d) = _
    rw [DeclEnv.realizationOf, hΔ]
    have : X.home d = X.system.declOf 0 d := by
      unfold home; rw [X.crossIn_not_member hin]; rfl
    rw [this]; rfl
  · have hb : (⟨.port 1 d, 0, d, none⟩ : Binding) ∈ X.system.bindings := by
      simp only [system, bindings, List.mem_append, List.mem_map]; exact Or.inr ⟨d, hout, rfl⟩
    obtain ⟨Id, pd, -, -, -, hΔ⟩ := inv.bound _ hb
    show X.system.flattenΔ.realizationOf (X.system.declOf 0 d) = _
    rw [DeclEnv.realizationOf, hΔ]
    have : X.home d = X.system.declOf 1 d := by
      unfold home; rw [(X.isMember_iff).mpr ((mem_crossOut _ _ _).mp hout).1]; rfl
    rw [this]; rfl

/-- **Theorem R, forward.**  Every evaluation in the original design is an
    evaluation in the flattened extraction, on either side, for terms whose
    references are visible on that side. -/
theorem eval_orig_to_flat (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound) (H : WF ev X)
    (hwir : DeclEnvWiring X.D.Δ) {I : Reactive.Input} (hI : ∀ d t, (I d t).NoClo) :
    ∀ {t : Nat} {ρ : List Value} {e : Expr} {v : Value}, Ev X.D.Δ I t ρ e v → e.Wiring →
      ∀ k, (k = 0 ∨ k = 1) → (∀ d ∈ e.refs, X.Visible k d) →
      Ev X.flat.Δ (X.liftInput I) t ρ (e.rename (X.renOf k)) v := by
  intro t ρ e v h
  induction h with
  | var _ => intro hw; exact hw.elim
  | boolLit => intro _ _ _ _; exact .boolLit
  | natLit => intro _ _ _ _; exact .natLit
  | lam => intro hw; exact hw.elim
  | appClo hf _ _ _ _ _ => intro hw; exact ((Ev.noClo hwir hI hf hw.1) (.clo _ _)).elim
  | appPrim _ _ ihf iha =>
    intro hw k hk hvis
    simp only [Expr.refs, List.mem_append] at hvis
    exact .appPrim (ihf hw.1 k hk fun d hd => hvis d (Or.inl hd)) (iha hw.2 k hk fun d hd => hvis d (Or.inr hd))
  | @refRealized t ρ d b v hs hb ih =>
    intro _ k hk hvis
    have hvd := hvis d (by simp [Expr.refs])
    have hdi : d ∈ X.ids := hvd.1
    have hdW := H.boundIds d hdi
    -- the home copy evaluates the renamed body
    have hhome : Ev X.flat.Δ (X.liftInput I) t [] (.declRef (X.home d)) v := by
      refine .refRealized ?_ (ih (hwir d b hs) (X.side d) (by unfold side; cases X.isMember d <;> simp) (body_refs_visible H hs))
      rw [flat_realizationOf_home mono eq ps H hdi, hs]; rfl
    show Ev X.flat.Δ (X.liftInput I) t ρ (.declRef (X.system.declOf k d)) v
    by_cases hks : k = X.side d
    · rw [hks, ← home_eq]
      exact hhome.declRef_env
    · exact .refRealized (flat_port_copy mono eq ps H hk hvd hks) hhome
  | @refInput t ρ d hn =>
    intro _ k hk hvis
    have hvd := hvis d (by simp [Expr.refs])
    have hdi : d ∈ X.ids := hvd.1
    have hdW := H.boundIds d hdi
    have hhome : Ev X.flat.Δ (X.liftInput I) t [] (.declRef (X.home d)) (I d t) := by
      have : X.liftInput I (X.home d) t = I d t := by rw [home_eq]; exact liftInput_declOf H I _ hdW t
      rw [← this]
      refine .refInput ?_
      rw [flat_realizationOf_home mono eq ps H hdi, hn]; rfl
    show Ev X.flat.Δ (X.liftInput I) t ρ (.declRef (X.system.declOf k d)) (I d t)
    by_cases hks : k = X.side d
    · rw [hks, ← home_eq]
      exact hhome.declRef_env
    · exact .refRealized (flat_port_copy mono eq ps H hk hvd hks) hhome
  | rep _ ih => intro hw k hk hvis; exact .rep (ih hw k hk hvis)
  | @mk t ρ e s w _ ih =>
    intro hw k hk hvis
    show Ev _ _ _ _ (.mk ((X.renOf k).s s) (e.rename (X.renOf k))) _
    rw [renOf_s]
    exact .mk (ih hw k hk hvis)
  | @prim t ρ p =>
    intro _ k _ _
    show Ev _ _ _ _ (.prim (p.rename (X.renOf k).s)) _
    rw [renOf_s, Prim.rename_id]
    exact .prim
  | delayZero _ ih =>
    intro hw k hk hvis
    simp only [Expr.refs, List.mem_append] at hvis
    exact .delayZero (ih hw.1 k hk fun d hd => hvis d (Or.inl hd))
  | delaySucc _ ih =>
    intro hw k hk hvis
    simp only [Expr.refs, List.mem_append] at hvis
    exact .delaySucc (ih hw.2 k hk fun d hd => hvis d (Or.inr hd))
  | syncZero _ ih =>
    intro hw k hk hvis
    simp only [Expr.refs, List.mem_append] at hvis
    exact .syncZero (ih hw.1 k hk fun d hd => hvis d (Or.inl hd))
  | syncSucc _ ih =>
    intro hw k hk hvis
    simp only [Expr.refs, List.mem_append] at hvis
    exact .syncSucc (ih hw.2 k hk fun d hd => hvis d (Or.inr hd))

/-- **Theorem R (observational equivalence on declarations).**  Under
    totality of the original design, an original declaration and its home
    copy in the flattened extraction have the same value at every tick. -/
theorem orig_iff_flat (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound) (H : WF ev X)
    (hwir : DeclEnvWiring X.D.Δ) {I : Reactive.Input} (hI : ∀ d t, (I d t).NoClo)
    (htot : ∀ d ∈ X.ids, ∀ t, ∃ v, Ev X.D.Δ I t [] (.declRef d) v)
    {d : DeclId} (hd : d ∈ X.ids) (t : Nat) (v : Value) :
    Ev X.D.Δ I t [] (.declRef d) v ↔ Ev X.flat.Δ (X.liftInput I) t [] (.declRef (X.home d)) v := by
  have fwd : ∀ v, Ev X.D.Δ I t [] (.declRef d) v → Ev X.flat.Δ (X.liftInput I) t [] (.declRef (X.home d)) v := by
    intro v h
    have := eval_orig_to_flat mono eq ps H hwir hI h (by simp [Expr.Wiring]) (X.side d)
      (by unfold side; cases X.isMember d <;> simp)
      (fun x hx => by simp only [Expr.refs, List.mem_singleton] at hx; subst hx; exact ⟨hd, Or.inl rfl⟩)
    rw [home_eq]; exact this
  refine ⟨fwd v, fun h => ?_⟩
  obtain ⟨v₀, hv₀⟩ := htot d hd t
  have := (fwd v₀ hv₀).det h
  subst this; exact hv₀

/-- Totality of the original design from Phase 4's `reactive_total`. -/
theorem orig_total (H : WF ev X) {I : Reactive.Input}
    (hRed : ∀ d τ t, X.D.Δ.tyView d = some τ → X.D.Δ.realizationOf d = none →
      Red X.D.Θ (Apply X.D.Δ I t) τ (I d t)) :
    ∀ d ∈ X.ids, ∀ t, ∃ v, Ev X.D.Δ I t [] (.declRef d) v := by
  intro d hd t
  obtain ⟨h, hh⟩ := (H.enum.2 d).mpr hd
  obtain ⟨v, hv, -⟩ := reactive_total H.wf.concepts H.wf.causal H.wf.global hRed
    (d := d) (τ := h.interface.expectedType) (by simp [DeclEnv.tyView, hh]) t
  exact ⟨v, hv⟩


/-! ## Theorem J (extraction level) — private members are unobservable through the interface -/

/-- A private member (no non-member consumer, no sink) is not a provided
    port, is the source of no binding, and is never referenced by the
    residual side of the flattened design. -/
theorem private_unobservable (H : WF ev X) {p : DeclId} (hp : p ∈ privateMembers X.D X.ids X.G) :
    (∀ port ∈ X.comp.iface.provided, port.id ≠ p) ∧
    (∀ b ∈ X.system.bindings, b.src ≠ .port 1 p) ∧
    (∀ d e, X.resid.design.Δ.realizationOf d = some e → X.system.declOf 1 p ∉ (e.rename (X.renOf 0)).refs) := by
  obtain ⟨hpG, hnot, -⟩ := (mem_privateMembers _ _ _).mp hp
  refine ⟨?_, ?_, ?_⟩
  · intro port hport heq
    simp only [comp, template, List.mem_map] at hport
    obtain ⟨q, hq, rfl⟩ := hport
    exact hnot (heq ▸ hq)
  · intro b hb heq
    simp only [system, bindings, List.mem_append, List.mem_map] at hb
    rcases hb with ⟨r, -, rfl⟩ | ⟨q, hq, rfl⟩
    · simp at heq
    · simp only [BindSrc.port.injEq, true_and] at heq
      exact hnot (heq ▸ hq)
  · intro d e he hmem
    rw [Expr.rename_refs, List.mem_map] at hmem
    obtain ⟨x, hx, heq⟩ := hmem
    obtain ⟨-, hre⟩ := restrictΔ_realizationOf (D := X.D) (keep := X.isOutside) (port := X.isCrossOut) he
    have hxW : x.n < X.W := H.boundIds x (dep_declared H (DependsOn.iff.mpr ⟨e, hre, hx⟩))
    have hpW : p.n < X.W := H.boundIds p (H.members p hpG)
    rw [renOf_d] at heq
    simp only [BehaviorSystem.declOf, DeclId.mk.injEq] at heq
    have := (fresh_inj H.widthPos hxW hpW heq).1
    omega

/-! ## Physical outputs stay with the member that drives them -/

/-- The drive edge of a member is carried by its home copy in the
    component instance, and the residual side does not drive the sink.  No
    semantic port is created for a sink. -/
theorem drive_stays_with_member (H : WF ev X) {m : DeclId} (hm : m ∈ X.G) {o : OutputId}
    (ho : X.D.β m = some o) :
    X.flat.β (X.home m) = some o ∧ X.flat.β (X.system.declOf 0 m) = none := by
  have c := system_composeWF H
  have hmW := H.boundIds m (H.members m hm)
  have hmem : X.isMember m = true := (X.isMember_iff).mpr hm
  constructor
  · show X.system.unionβ (X.home m) = _
    unfold home; rw [hmem]; simp only [if_true]
    rw [BehaviorSystem.unionβ_fresh c.width instAt_one hmW]
    show ((restrictβ X.D X.isMember) m).map _ = _
    simp [restrictβ, hmem, ho, BehaviorSystem.ren, Ren.inst, comp, template]
  · show X.system.unionβ (X.system.declOf 0 m) = _
    rw [BehaviorSystem.unionβ_fresh c.width instAt_zero hmW]
    have : X.isOutside m = false := by simp [isOutside, hm]
    simp [restrictβ, this, resid, template, restrict]

/-- Every crossing-out member is its own provided port (§29: several
    independent mappings yield several independent ports). -/
theorem provided_iff (port : Port) :
    port ∈ X.comp.iface.provided ↔ ∃ p ∈ crossOut X.D X.ids X.G, port = portOf X.D p := by
  simp [comp, template, List.mem_map, eq_comm]

end Input

end Extract
end BDL
