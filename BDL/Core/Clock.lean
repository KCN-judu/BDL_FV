import BDL.Core.Reactive

/-!
# Clock — clock domains and synchronization (Phase 5)

Time model: one global base tick; a **schedule** `S : ClockId → Nat → Bool`
says at which global ticks each domain activates.  No physical time and no
numeric rates in the kernel (a period *induces* a schedule).

Clock identity is nominal (`ClockId`), attached to declarations through the
projection `ClockEnv Κ : DeclId → Option ClockId` (`none` = domain-agnostic
pure mapping).  The **domain judgment** `Clocked` checks that references
stay in their domain unless they go through the one transport primitive

    sync src init e   -- e at the last activation of src strictly before now; init if none

`Ty`, `HasType` and `tyView` are unchanged.

Results
* `MEv.det`                  — multi-domain evaluation is deterministic (no scheduler order).
* `single_domain_embedding`  — under the always-active schedule `MEv` is `Ev`.
* `delay_is_sync_own`        — `delay` is `sync` at the declaration's own domain.
* `mfundamental`, `multi_domain_total` — causal + well formed ⇒ a value in every domain at every tick;
                                 causality is the *same* `Causal Δ` (transport is never instantaneous).
* `MEv.tag_provenance`, `sync_preserves_semantic_identity` — synchronization changes timing, not identity.
* `buffer_from_log_and_cursor` — exact event buffering is `sync` of a log + `delay` of a cursor.

Concrete designs and rejected alternatives: `Experiments/ClockAlternatives.lean`.
-/

namespace BDL.Clock
open BDL BDL.Reactive

/-! ## §1 Schedules -/

/-- Which domains activate at which global ticks. -/
abbrev Sched := ClockId → Nat → Bool

/-- The last activation of `c` strictly before `t`. -/
def prevAct (S : Sched) (c : ClockId) : Nat → Option Nat
  | 0 => Option.none
  | t + 1 => if S c t then Option.some t else prevAct S c t

theorem prevAct_lt {S : Sched} {c : ClockId} : ∀ {t t' : Nat}, prevAct S c t = Option.some t' → t' < t
  | 0, _, h => by simp [prevAct] at h
  | t + 1, t', h => by
    simp only [prevAct] at h
    split at h
    · cases h; exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (prevAct_lt h)

theorem prevAct_active {S : Sched} {c : ClockId} : ∀ {t t' : Nat}, prevAct S c t = Option.some t' → S c t' = true
  | 0, _, h => by simp [prevAct] at h
  | t + 1, t', h => by
    simp only [prevAct] at h
    split at h
    · cases h; assumption
    · exact prevAct_active h

/-- A period per domain induces a schedule.  Rates never enter the kernel
    except through this induced activation relation. -/
def Sched.periodic (period : ClockId → Nat) : Sched := fun c t => t % period c = 0

/-- Every domain active at every tick: the single-domain schedule. -/
def Sched.always : Sched := fun _ _ => true

theorem prevAct_always (c : ClockId) : ∀ t, prevAct Sched.always c t = (match t with | 0 => Option.none | t' + 1 => Option.some t')
  | 0 => rfl
  | _ + 1 => by simp [prevAct, Sched.always]

/-! ## §2 Clock environment and the domain judgment (Model D) -/

/-- The domain of each declaration; `none` = domain-agnostic (a pure mapping
    usable in any domain).  Interface-level data: clients' validity depends
    on it (§6, Counterexample E). -/
abbrev ClockEnv := DeclId → Option ClockId

/-- `Clocked Κ c e`: `e` may be evaluated in domain `c` (`none` = in any
    domain).  A reference stays in its domain or is agnostic; `delay` needs a
    domain; `sync src` switches the domain for its operand. -/
def clockedB (Κ : ClockEnv) : Option ClockId → Expr → Bool
  | c, .lam _ b => clockedB Κ c b
  | c, .app f a => clockedB Κ c f && clockedB Κ c a
  | c, .declRef d => decide (Κ d = Option.none ∨ Κ d = c)
  | c, .rep e => clockedB Κ c e
  | c, .mk _ e => clockedB Κ c e
  | Option.some c, .delay i e => clockedB Κ (Option.some c) i && clockedB Κ (Option.some c) e
  | Option.none, .delay _ _ => false
  | Option.some c, .sync c' i e => clockedB Κ (Option.some c) i && clockedB Κ (Option.some c') e
  | Option.none, .sync _ _ _ => false
  | _, _ => true

def Clocked (Κ : ClockEnv) (c : Option ClockId) (e : Expr) : Prop := clockedB Κ c e = true

instance (Κ : ClockEnv) (c : Option ClockId) (e : Expr) : Decidable (Clocked Κ c e) :=
  inferInstanceAs (Decidable (clockedB Κ c e = true))

/-- Every realization is well-clocked in its own declaration's domain. -/
def WellClocked (Κ : ClockEnv) (Δ : DeclEnv) : Prop :=
  ∀ d b, Δ.realizationOf d = some b → Clocked Κ (Κ d) b

def wellClockedCheck (Κ : ClockEnv) (l : List DesignDecl) : Bool :=
  l.all fun dh => match dh.realization with
    | some b => clockedB Κ (Κ dh.id) b
    | none => true

theorem WellClocked.ofList {Κ : ClockEnv} {l : List DesignDecl} (h : wellClockedCheck Κ l = true) :
    WellClocked Κ (.ofList l) := by
  intro d b hb
  simp only [DeclEnv.realizationOf, Option.bind_eq_some_iff] at hb
  obtain ⟨dh, hdh, hre⟩ := hb
  obtain ⟨hmem, hid⟩ := DeclEnv.ofList_some hdh
  subst hid
  have := (List.all_eq_true.mp h) dh hmem
  rw [hre] at this
  exact this

/-! ## §3 Multi-domain semantics -/

/-- `MEv S Δ I c t ρ e v`: in domain `c` at global tick `t`, `e` has value `v`.
    Identical to `Ev` except that `delay` reads the previous activation *of
    the current domain* and `sync src` reads the previous activation of
    `src`, evaluating its operand there. -/
inductive MEv (S : Sched) (Δ : DeclEnv) (I : Input) : ClockId → Nat → List Value → Expr → Value → Prop where
  | var {c t ρ i v} : ρ[i]? = some v → MEv S Δ I c t ρ (.var i) v
  | boolLit {c t ρ b} : MEv S Δ I c t ρ (.boolLit b) (.bool b)
  | natLit {c t ρ n} : MEv S Δ I c t ρ (.natLit n) (.nat n)
  | lam {c t ρ dom body} : MEv S Δ I c t ρ (.lam dom body) (.clo ρ body)
  | appClo {c t ρ f a ρ' body va v} :
      MEv S Δ I c t ρ f (.clo ρ' body) → MEv S Δ I c t ρ a va → MEv S Δ I c t (va :: ρ') body v →
      MEv S Δ I c t ρ (.app f a) v
  | appPrim {c t ρ f a p args va} :
      MEv S Δ I c t ρ f (.prim p args) → MEv S Δ I c t ρ a va →
      MEv S Δ I c t ρ (.app f a) (applyPrim p (args ++ [va]))
  | refRealized {c t ρ d b v} : Δ.realizationOf d = some b → MEv S Δ I c t [] b v → MEv S Δ I c t ρ (.declRef d) v
  | refInput {c t ρ d} : Δ.realizationOf d = none → MEv S Δ I c t ρ (.declRef d) (I d t)
  | rep {c t ρ e s w} : MEv S Δ I c t ρ e (.sem s w) → MEv S Δ I c t ρ (.rep e) w
  | mk {c t ρ e s w} : MEv S Δ I c t ρ e w → MEv S Δ I c t ρ (.mk s e) (.sem s w)
  | prim {c t ρ p} : MEv S Δ I c t ρ (.prim p) (applyPrim p [])
  | delayNone {c t ρ i e v} : prevAct S c t = Option.none → MEv S Δ I c t ρ i v → MEv S Δ I c t ρ (.delay i e) v
  | delaySome {c t t' ρ i e v} : prevAct S c t = Option.some t' → MEv S Δ I c t' ρ e v → MEv S Δ I c t ρ (.delay i e) v
  | syncNone {c c' t ρ i e v} : prevAct S c' t = Option.none → MEv S Δ I c t ρ i v → MEv S Δ I c t ρ (.sync c' i e) v
  | syncSome {c c' t t' ρ i e v} : prevAct S c' t = Option.some t' → MEv S Δ I c' t' ρ e v → MEv S Δ I c t ρ (.sync c' i e) v

/-- **`multi_domain_step_deterministic`.**  No scheduler order appears in
    the semantics: cross-domain reads are strictly-before, so simultaneous
    activations never observe each other's current values. -/
theorem MEv.det {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat} {ρ : List Value} {e : Expr} {v₁ v₂ : Value}
    (h₁ : MEv S Δ I c t ρ e v₁) (h₂ : MEv S Δ I c t ρ e v₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | var h => cases h₂ with | var h' => rw [h] at h'; exact Option.some.inj h'
  | boolLit => cases h₂; rfl
  | natLit => cases h₂; rfl
  | lam => cases h₂; rfl
  | appClo _ _ _ ihf iha ihb =>
    cases h₂ with
    | appClo hf' ha' hb' => cases ihf hf'; cases iha ha'; exact ihb hb'
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
  | delayNone hp _ ih =>
    cases h₂ with
    | delayNone _ h' => exact ih h'
    | delaySome hp' _ => rw [hp] at hp'; exact nomatch hp'
  | delaySome hp _ ih =>
    cases h₂ with
    | delayNone hp' _ => rw [hp] at hp'; exact nomatch hp'
    | delaySome hp' h' => rw [hp] at hp'; cases hp'; exact ih h'
  | syncNone hp _ ih =>
    cases h₂ with
    | syncNone _ h' => exact ih h'
    | syncSome hp' _ => rw [hp] at hp'; exact nomatch hp'
  | syncSome hp _ ih =>
    cases h₂ with
    | syncNone hp' _ => rw [hp] at hp'; exact nomatch hp'
    | syncSome hp' h' => rw [hp] at hp'; cases hp'; exact ih h'

/-- Executable interpreter, sound for `MEv`. -/
def mevalF (S : Sched) (Δ : DeclEnv) (I : Input) : Nat → ClockId → Nat → List Value → Expr → Option Value
  | 0, _, _, _, _ => Option.none
  | fuel + 1, c, t, ρ, e =>
    match e with
    | .var i => ρ[i]?
    | .boolLit b => Option.some (.bool b)
    | .natLit n => Option.some (.nat n)
    | .lam _ body => Option.some (.clo ρ body)
    | .app f a =>
      (mevalF S Δ I fuel c t ρ f).bind fun vf =>
      (mevalF S Δ I fuel c t ρ a).bind fun va =>
      match vf with
      | .clo ρ' body => mevalF S Δ I fuel c t (va :: ρ') body
      | .prim p args => Option.some (applyPrim p (args ++ [va]))
      | _ => Option.none
    | .declRef d =>
      match Δ.realizationOf d with
      | Option.some b => mevalF S Δ I fuel c t [] b
      | Option.none => Option.some (I d t)
    | .rep e =>
      (mevalF S Δ I fuel c t ρ e).bind fun ve =>
      match ve with
      | .sem _ w => Option.some w
      | _ => Option.none
    | .mk s e => (mevalF S Δ I fuel c t ρ e).map (.sem s)
    | .prim p => Option.some (applyPrim p [])
    | .delay i e =>
      match prevAct S c t with
      | Option.none => mevalF S Δ I fuel c t ρ i
      | Option.some t' => mevalF S Δ I fuel c t' ρ e
    | .sync c' i e =>
      match prevAct S c' t with
      | Option.none => mevalF S Δ I fuel c t ρ i
      | Option.some t' => mevalF S Δ I fuel c' t' ρ e

theorem mevalF_sound {S : Sched} {Δ : DeclEnv} {I : Input} :
    ∀ {fuel : Nat} {c : ClockId} {t : Nat} {ρ : List Value} {e : Expr} {v : Value},
      mevalF S Δ I fuel c t ρ e = Option.some v → MEv S Δ I c t ρ e v
  | 0, _, _, _, _, _, h => by simp [mevalF] at h
  | fuel + 1, c, t, ρ, e, v, h => by
    cases e with
    | var i => exact .var h
    | boolLit b => exact (Option.some.inj h) ▸ MEv.boolLit
    | natLit n => exact (Option.some.inj h) ▸ MEv.natLit
    | lam dom body => exact (Option.some.inj h) ▸ MEv.lam
    | prim p => exact (Option.some.inj h) ▸ MEv.prim
    | app f a =>
      simp only [mevalF, Option.bind_eq_some_iff] at h
      obtain ⟨vf, hf, va, ha, hm⟩ := h
      cases vf with
      | clo ρ' body => exact .appClo (mevalF_sound hf) (mevalF_sound ha) (mevalF_sound hm)
      | prim p args =>
        simp only [Option.some.injEq] at hm
        subst hm
        exact .appPrim (mevalF_sound hf) (mevalF_sound ha)
      | bool _ | nat _ | sem _ _ | none | some _ | list _ => simp at hm
    | declRef d =>
      simp only [mevalF] at h
      cases hr : Δ.realizationOf d with
      | none => rw [hr] at h; exact (Option.some.inj h) ▸ MEv.refInput hr
      | some b => rw [hr] at h; exact .refRealized hr (mevalF_sound h)
    | rep e =>
      simp only [mevalF, Option.bind_eq_some_iff] at h
      obtain ⟨ve, he, hm⟩ := h
      cases ve with
      | sem s w => simp only [Option.some.injEq] at hm; subst hm; exact .rep (mevalF_sound he)
      | bool _ | nat _ | none | some _ | clo _ _ | prim _ _ | list _ => simp at hm
    | mk s e =>
      simp only [mevalF, Option.map_eq_some_iff] at h
      obtain ⟨w, hw, rfl⟩ := h
      exact .mk (mevalF_sound hw)
    | delay i e =>
      simp only [mevalF] at h
      cases hp : prevAct S c t with
      | none => rw [hp] at h; exact .delayNone hp (mevalF_sound h)
      | some t' => rw [hp] at h; exact .delaySome hp (mevalF_sound h)
    | sync c' i e =>
      simp only [mevalF] at h
      cases hp : prevAct S c' t with
      | none => rw [hp] at h; exact .syncNone hp (mevalF_sound h)
      | some t' => rw [hp] at h; exact .syncSome hp (mevalF_sound h)

/-! ## §4 Single-domain embedding -/

/-- **`single_domain_embedding`.**  Under the always-active schedule the
    multi-domain semantics *is* the Phase-4 semantics, in every domain. -/
theorem single_domain_embedding {Δ : DeclEnv} {I : Input} (c : ClockId) {t : Nat} {ρ : List Value} {e : Expr} {v : Value} :
    MEv Sched.always Δ I c t ρ e v ↔ Ev Δ I t ρ e v := by
  constructor
  · intro h
    induction h with
    | var h => exact .var h
    | boolLit => exact .boolLit
    | natLit => exact .natLit
    | lam => exact .lam
    | appClo _ _ _ ihf iha ihb => exact .appClo ihf iha ihb
    | appPrim _ _ ihf iha => exact .appPrim ihf iha
    | refRealized hs _ ih => exact .refRealized hs ih
    | refInput hn => exact .refInput hn
    | rep _ ih => exact .rep ih
    | mk _ ih => exact .mk ih
    | prim => exact .prim
    | @delayNone c t _ _ _ _ hp _ ih =>
      cases t with
      | zero => exact .delayZero ih
      | succ t => rw [prevAct_always] at hp; exact nomatch hp
    | @delaySome c t t' _ _ _ _ hp _ ih =>
      cases t with
      | zero => rw [prevAct_always] at hp; exact nomatch hp
      | succ t => rw [prevAct_always] at hp; cases hp; exact .delaySucc ih
    | @syncNone c c' t _ _ _ _ hp _ ih =>
      cases t with
      | zero => exact .syncZero ih
      | succ t => rw [prevAct_always] at hp; exact nomatch hp
    | @syncSome c c' t t' _ _ _ _ hp _ ih =>
      cases t with
      | zero => rw [prevAct_always] at hp; exact nomatch hp
      | succ t => rw [prevAct_always] at hp; cases hp; exact .syncSucc ih
  · intro h
    induction h generalizing c with
    | var h => exact .var h
    | boolLit => exact .boolLit
    | natLit => exact .natLit
    | lam => exact .lam
    | appClo _ _ _ ihf iha ihb => exact .appClo (ihf c) (iha c) (ihb c)
    | appPrim _ _ ihf iha => exact .appPrim (ihf c) (iha c)
    | refRealized hs _ ih => exact .refRealized hs (ih c)
    | refInput hn => exact .refInput hn
    | rep _ ih => exact .rep (ih c)
    | mk _ ih => exact .mk (ih c)
    | prim => exact .prim
    | delayZero _ ih => exact .delayNone (by simp [prevAct_always]) (ih c)
    | delaySucc _ ih => exact .delaySome (by simp [prevAct_always]) (ih c)
    | @syncZero _ c' _ _ _ _ ih => exact .syncNone (by simp [prevAct_always]) (ih c)
    | @syncSucc _ _ c' _ _ _ _ ih => exact .syncSome (by simp [prevAct_always]) (ih c')

/-! ## §5 `delay` is `sync` at the declaration's own domain -/

/-- **`delay_is_sync_own`.**  One primitive suffices: `delay init e` in
    domain `c` means exactly `sync c init e`.  Cross-domain transport is not
    a new state mechanism; it is the state basis with its domain made
    explicit. -/
theorem delay_is_sync_own {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat} {ρ : List Value}
    {i e : Expr} {v : Value} :
    MEv S Δ I c t ρ (.delay i e) v ↔ MEv S Δ I c t ρ (.sync c i e) v := by
  constructor
  · intro h
    cases h with
    | delayNone hp hi => exact .syncNone hp hi
    | delaySome hp he => exact .syncSome hp he
  · intro h
    cases h with
    | syncNone hp hi => exact .delayNone hp hi
    | syncSome hp he => exact .delaySome hp he

/-- And the domain judgment agrees: `delay` is well-clocked in `c` iff the
    corresponding `sync c` is. -/
theorem clocked_delay_iff_sync_own (Κ : ClockEnv) (c : ClockId) (i e : Expr) :
    Clocked Κ (Option.some c) (.delay i e) ↔ Clocked Κ (Option.some c) (.sync c i e) := by
  simp [Clocked, clockedB]

/-! ## §8 Tag provenance across domains

Synchronization changes timing, not semantic identity: `sync` moves a value
between domains without touching its tag. -/

theorem MEv.tag_provenance {S : Sched} {Δ : DeclEnv} {I : Input} (s : SemanticId)
    (hΔ : ∀ d b, Δ.realizationOf d = some b → ¬ b.constructs s)
    (hI : ∀ d t, ¬ (I d t).Taints s) :
    ∀ {c : ClockId} {t : Nat} {ρ : List Value} {e : Expr} {v : Value}, MEv S Δ I c t ρ e v →
      ¬ e.constructs s → (∀ w ∈ ρ, ¬ w.Taints s) → ¬ v.Taints s := by
  intro c t ρ e v h
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
  | rep _ ih => intro he hρ ht; exact ih he hρ (.semInner ht)
  | mk _ ih =>
    intro he hρ ht
    cases ht with
    | semHere _ => exact he (Or.inl rfl)
    | semInner ht => exact ih (fun h => he (Or.inr h)) hρ ht
  | prim =>
    intro _ _ ht
    obtain ⟨w, hw, _⟩ := applyPrim_taints _ _ ht
    simp at hw
  | delayNone _ _ ih => intro he hρ; exact ih (fun h => he (Or.inl h)) hρ
  | delaySome _ _ ih => intro he hρ; exact ih (fun h => he (Or.inr h)) hρ
  | syncNone _ _ ih => intro he hρ; exact ih (fun h => he (Or.inl h)) hρ
  | syncSome _ _ ih => intro he hρ; exact ih (fun h => he (Or.inr h)) hρ

/-- **`transport_preserves_semantic_identity`** (semantic form): with clock
    crossings present, a concept no signature announces never appears. -/
theorem sync_preserves_semantic_identity {S : Sched} {Θ : ConceptEnv} {Δ : DeclEnv} {I : Input}
    {ev : Evidence} (g : GlobalWF ev Θ Δ) (s : SemanticId)
    (hsig : ∀ d dh, Δ d = some dh → s ∉ dh.interface.expectedType.grant)
    (hI : ∀ d t, ¬ (I d t).Taints s)
    {c : ClockId} {t : Nat} {d : DeclId} {v : Value} (h : MEv S Δ I c t [] (.declRef d) v) : ¬ v.Taints s := by
  refine MEv.tag_provenance s ?_ hI h (by simp [Expr.constructs]) (fun _ h => by simp at h)
  intro d' b hb
  simp only [DeclEnv.realizationOf, Option.bind_eq_some_iff] at hb
  obtain ⟨dh, hdh, hre⟩ := hb
  have ht := ((g.wellFormed hdh) b hre).1
  intro hc
  exact hsig d' dh hdh (ht.constructs_granted s hc)

/-! ## §9 Totality across domains -/

/-- Application at an evaluation point `(c, t)`. -/
def MApply (S : Sched) (Δ : DeclEnv) (I : Input) (c : ClockId) (t : Nat) : App := fun vf w v =>
  (∃ ρ' body, vf = .clo ρ' body ∧ MEv S Δ I c t (w :: ρ') body v) ∨
  (∃ p args, vf = .prim p args ∧ v = applyPrim p (args ++ [w]))

theorem MApply.hasPrim (S : Sched) (Δ : DeclEnv) (I : Input) (c : ClockId) (t : Nat) : App.HasPrim (MApply S Δ I c t) :=
  fun p args _ => Or.inr ⟨p, args, rfl, rfl⟩

theorem MEv.app_of_apply {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat} {ρ : List Value}
    {f a : Expr} {vf w v : Value}
    (hf : MEv S Δ I c t ρ f vf) (ha : MEv S Δ I c t ρ a w) (hap : MApply S Δ I c t vf w v) :
    MEv S Δ I c t ρ (.app f a) v := by
  rcases hap with ⟨ρ', body, rfl, hb⟩ | ⟨p, args, rfl, rfl⟩
  · exact .appClo hf ha hb
  · exact .appPrim hf ha

/-- **Fundamental theorem, multi-domain.**  Same induction as Phase 4 — on
    (global tick, instantaneous rank, derivation) — because `delay` and
    `sync` both read strictly earlier global ticks (`prevAct_lt`).  Causality
    is the *same* `Causal Δ`: cross-domain transport is never instantaneous. -/
theorem mfundamental {S : Sched} {Θ : ConceptEnv} (hΘ : Θ.WF) {Δ : DeclEnv} {I : Input}
    {rank : DeclId → Nat} {R : Nat} (hR : ∀ d, rank d < R)
    (hc : ∀ a b, InstDependsOn Δ a b → rank b < rank a)
    {ev : Evidence} (g : GlobalWF ev Θ Δ)
    (hI : ∀ d τ c t, Δ.tyView d = some τ → Δ.realizationOf d = none → Red Θ (MApply S Δ I c t) τ (I d t)) :
    ∀ t r (c : ClockId) {G : Grant} {Γ : Ctx} {e : Expr} {τ : Ty}, HasType Θ Δ G Γ e τ →
      ∀ ρ, (∀ x ∈ e.instRefs, rank x < r) → RedEnv Θ (MApply S Δ I c t) Γ ρ →
      ∃ v, MEv S Δ I c t ρ e v ∧ Red Θ (MApply S Δ I c t) τ v := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t iht =>
  intro r
  induction r using Nat.strongRecOn with
  | ind r ihr =>
  intro c G Γ e τ h
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
    exact ⟨v, MEv.app_of_apply hvf hva hap, hr⟩
  | @declRef _ d τ htv =>
    intro ρ hb _
    have hd : rank d < r := hb d (by simp [Expr.instRefs])
    cases hre : Δ.realizationOf d with
    | none => exact ⟨_, .refInput hre, hI d τ c t htv hre⟩
    | some b =>
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
      obtain ⟨v, hv, hr⟩ := ihr (rank d) hd c hbody [] hbb (RedEnv.nil [])
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
  | prim => intro ρ _ _; exact ⟨_, .prim, Red_prim (MApply.hasPrim S Δ I c t) _⟩
  | @delay i e τ hdata hi he ihi _ =>
    intro ρ hb hρ
    cases hp : prevAct S c t with
    | none =>
      obtain ⟨v, hv, hr⟩ := ihi ρ hb hρ
      exact ⟨v, .delayNone hp hv, hr⟩
    | some t' =>
      obtain ⟨v, hv, hr⟩ := iht t' (prevAct_lt hp) R c he ρ (fun x _ => hR x) (RedEnv.nil ρ)
      exact ⟨v, .delaySome hp hv, Red_data hΘ hdata hr⟩
  | @sync c' i e τ hdata hi he ihi _ =>
    intro ρ hb hρ
    cases hp : prevAct S c' t with
    | none =>
      obtain ⟨v, hv, hr⟩ := ihi ρ hb hρ
      exact ⟨v, .syncNone hp hv, hr⟩
    | some t' =>
      obtain ⟨v, hv, hr⟩ := iht t' (prevAct_lt hp) R c' he ρ (fun x _ => hR x) (RedEnv.nil ρ)
      exact ⟨v, .syncSome hp hv, Red_data hΘ hdata hr⟩

/-- **`multi_domain_total`.**  Every declaration of a causal, globally
    well-formed design has a value in every domain at every global tick —
    in particular at its own domain's first activation, with the explicit
    initial values of its transports. -/
theorem multi_domain_total {S : Sched} {Θ : ConceptEnv} (hΘ : Θ.WF) {Δ : DeclEnv} (hc : Causal Δ) {I : Input}
    {ev : Evidence} (g : GlobalWF ev Θ Δ)
    (hI : ∀ d τ c t, Δ.tyView d = some τ → Δ.realizationOf d = none → Red Θ (MApply S Δ I c t) τ (I d t))
    {d : DeclId} {τ : Ty} (htv : Δ.tyView d = some τ) (c : ClockId) (t : Nat) :
    ∃ v, MEv S Δ I c t [] (.declRef d) v ∧ Red Θ (MApply S Δ I c t) τ v := by
  obtain ⟨rank, R, hR, hr⟩ := hc
  have h : HasType Θ Δ Grant.none [] (.declRef d) τ := .declRef htv
  exact mfundamental hΘ hR hr g hI t R c h [] (fun x hx => by simp [Expr.instRefs] at hx; subst hx; exact hR _)
    (RedEnv.nil [])

/-! ## The window model (event transport) -/

/-! ### The window model

What the slow side *should* be able to see is the source's occurrences at
the source activations since the slow side's previous activation.  Model it
on tick sets and compare policies. -/

/-- Source activations `u` with `lo ≤ u < hi`. -/
def srcTicks (S : Sched) (src : ClockId) (lo hi : Nat) : List Nat :=
  (List.range hi).filter fun u => decide (lo ≤ u) && S src u

/-- All source activations before `hi`: the *log* a source-side accumulator
    holds, as read by `sync` at `hi`. -/
def logTicks (S : Sched) (src : ClockId) (hi : Nat) : List Nat := srcTicks S src 0 hi

/-- The destination's window at `t`: source activations since its previous
    activation `t₀` (or all, at its first activation). -/
def windowTicks (S : Sched) (src dst : ClockId) (t : Nat) : List Nat :=
  srcTicks S src ((prevAct S dst t).getD 0) t

/-- **`buffer_from_log_and_cursor`.**  The window is the log read at `t`
    with the log length read at the previous destination activation dropped:
        window(t) = drop (|log(t₀)|) (log(t))
    Both `log(t)` and `|log(t₀)|` are single-instant reads — a `sync` of a
    source-side accumulator and a destination-side `delay` of its length.  So
    exact event buffering is a *structured use of the existing state basis*
    plus list data; no new state primitive.  (What is not derivable is a
    *bound* on the log: capacity is a validation obligation.) -/
theorem buffer_from_log_and_cursor (S : Sched) (src : ClockId) (t₀ t : Nat) (h : t₀ ≤ t) :
    srcTicks S src t₀ t = (logTicks S src t).drop (logTicks S src t₀).length := by
  obtain ⟨k, rfl⟩ : ∃ k, t = t₀ + k := ⟨t - t₀, (Nat.add_sub_cancel' h).symm⟩
  simp only [srcTicks, logTicks]
  -- the first block contributes nothing to the window (all `< t₀`); on the
  -- second block (all `≥ t₀`) the window predicate is the log predicate
  have h1 : (List.range t₀).filter (fun u => decide (t₀ ≤ u) && S src u) = [] := by
    -- constructively: every element of `range t₀` fails the predicate
    have key : ∀ n, n ≤ t₀ → (List.range n).filter (fun u => decide (t₀ ≤ u) && S src u) = [] := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ n ih =>
        intro hn
        rw [List.range_succ, List.filter_append, ih (Nat.le_of_succ_le hn)]
        simp [Nat.not_le.mpr (Nat.lt_of_succ_le hn)]
    exact key t₀ (Nat.le_refl _)
  have h2 : ((List.range k).map (t₀ + ·)).filter (fun u => decide (t₀ ≤ u) && S src u)
      = ((List.range k).map (t₀ + ·)).filter (fun u => decide (0 ≤ u) && S src u) := by
    apply List.filter_congr
    intro u hu
    simp only [List.mem_map] at hu
    obtain ⟨j, _, rfl⟩ := hu
    simp
  rw [List.range_add, List.filter_append, List.filter_append, List.drop_left, h1, List.nil_append, h2]


end BDL.Clock
