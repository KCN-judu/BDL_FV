import BDL.Surface.Provider
import BDL.Surface.OutputWindow

/-!
# Phase 18 — The Source-side boundary: provider state, the device clock, initialization, commitments, `computes`, out-of-type readings

What FVI-0020 still held after Phase 17, answered as deployment-side
constructions over the unchanged kernel:

* **Value congruence** (`MEv.congr_at`): two designs that agree on every
  realization except at one declaration `s`, where the *values* agree at
  every tick in every domain, evaluate every term alike.  One lemma
  behind every result below: the behaviour sees a Source through its
  value trace and through nothing else.
* **Provider state** (`Machine`, `run`, `machine_upstream`,
  `provider_state_movable`): a stateful transducer is a Mealy machine
  whose step is a pure BDL term.  Placed below the raw reading it is
  provider state; placed above it — one declaration with `delay` over the
  physical reading — it is behaviour state; the Source's trace is the
  same, so the behaviour is the same.  The placement is therefore not a
  semantic question but a *visibility* one, and the criterion is stated:
  state whose parameters, reset or reading the product must see belongs
  upstream, where the design and the simulation show it; state that only
  interprets a device's signal may sit in the provider.  Nothing can be
  hidden *by* the placement, because the trace is what the behaviour
  reads (`stateful_providers_same_behavior`).
* **The Source-side device clock** (`provisionSync`): the raw reading in
  the provider's domain `pc`, the Source in its own domain `c`, the
  crossing an explicit `sync` with an explicit initial raw value — the
  input dual of Phase 15's `lowerSync`.  The Source carries the transfer
  of the reading sampled at the last activation of `pc` strictly before,
  or of the initial value (`provisionSync_target`); transparent
  (`provisionSync_transparent`), well clocked, causal with no new
  instantaneous edge, globally well formed.  The occurrence-like crossing
  is Phase 9a's window over the raw reading (`provisionWindow`, one
  theorem over `buffer_window_correspondence`): no second crossing.
* **Initialization** is the explicit `InitRep` of the crossing: a
  profile-supplied initial raw value, or `none` at an optional raw type
  so the Source reads *unavailable* — never a fabricated reading;
  activation gated on the first sample is not a construction (a schedule
  does not depend on an input) and is the optional form instead.
* **Commitment discharge** (`RangeSoundUnder`, `discharge_under`): a
  Source's commitment is discharged by the provisioned realization when
  every value the target takes under readings satisfying an assumption
  `A` has the property; three evidence levels differ in who supplies
  `A`: the transducer alone (`discharge_static`, `A = TyVal raw`), a
  checking provider (`discharge_checked`, `A` established by
  construction), or a trusted range (`discharge_trusted`, `A` an explicit
  hypothesis — the trust boundary is visible in the theorem).
* **`computes`** is proof-carrying; it is *derivable* when the transfer
  function is the term's own evaluation (`Channel.ofTerm`), and
  *decidable* for a finite raw type (`computesBool`, `computes_of_bool`).
  A separately supplied transfer function is a claim checked against the
  term.
* **Out-of-type readings** (`checkedProvide`): the provider validates
  each delivery (`ok`), refuses the rest, and the reading is typed by
  construction (`checked_items_ok`, `checked_typed`); a refused reading is
  `none` at an optional Source or a flag beside it — a value the design
  reads, not an exception.
* **The richer profile** (`ProviderProfile`): the Phase-13 profile with a
  machine, an initial policy, a delivery contract and assumptions; the
  assignment reads the Phase-13 profile only (`assignSource_profile_only`).
-/

namespace BDL.SourceBoundary
open BDL BDL.Reactive BDL.Clock BDL.Output BDL.Provision BDL.OutputRealization BDL.Assignment BDL.Provider
open BDL.Buffer BDL.DeviceClock

/-! ## Value congruence -/

theorem _root_.BDL.Clock.MEv.declRef_env {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat} {d : DeclId} {v : Value}
    (h : MEv S Δ I c t [] (.declRef d) v) (ρ : List Value) : MEv S Δ I c t ρ (.declRef d) v := by
  cases h with
  | refRealized hs hb => exact .refRealized hs hb
  | refInput hn => exact .refInput hn

theorem _root_.BDL.Clock.MEv.declRef_nil {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat} {ρ : List Value} {d : DeclId}
    {v : Value} (h : MEv S Δ I c t ρ (.declRef d) v) : MEv S Δ I c t [] (.declRef d) v := by
  cases h with
  | refRealized hs hb => exact .refRealized hs hb
  | refInput hn => exact .refInput hn

/-- **`MEv.congr_at`**: evaluation in `Δ₁` under `I₁` transfers to `Δ₂`
    under `I₂` when every realization other than `s`'s is kept, every other
    input is read alike, and `s` takes the same values at every tick in every
    domain.  Nothing about `s`'s realizations — one may be an input, the
    other a transducer over a device, a machine, a transport. -/
theorem _root_.BDL.Clock.MEv.congr_at {S : Sched} {Δ₁ Δ₂ : DeclEnv} {I₁ I₂ : Input} (s : DeclId)
    (hΔ : ∀ d body, d ≠ s → Δ₁.realizationOf d = some body → Δ₂.realizationOf d = some body)
    (hI : ∀ d t, d ≠ s → Δ₁.realizationOf d = none → ∀ c, MEv S Δ₂ I₂ c t [] (.declRef d) (I₁ d t))
    (hs : ∀ c t v, MEv S Δ₁ I₁ c t [] (.declRef s) v → MEv S Δ₂ I₂ c t [] (.declRef s) v) :
    ∀ {c : ClockId} {t : Nat} {ρ : List Value} {e : Expr} {v : Value},
      MEv S Δ₁ I₁ c t ρ e v → MEv S Δ₂ I₂ c t ρ e v := by
  intro c t ρ e v h
  induction h with
  | var hv => exact .var hv
  | boolLit => exact .boolLit
  | natLit => exact .natLit
  | lam => exact .lam
  | appClo _ _ _ ihf iha ihb => exact .appClo ihf iha ihb
  | appPrim _ _ ihf iha => exact .appPrim ihf iha
  | @refRealized c t ρ d body v hr hb ih =>
    by_cases hd : d = s
    · subst hd; exact (hs c t v (.refRealized hr hb)).declRef_env ρ
    · exact .refRealized (hΔ d body hd hr) ih
  | @refInput c t ρ d hn =>
    by_cases hd : d = s
    · subst hd; exact (hs c t _ (.refInput hn)).declRef_env ρ
    · exact (hI d t hd hn c).declRef_env ρ
  | rep _ ih => exact .rep ih
  | mk _ ih => exact .mk ih
  | prim => exact .prim
  | delayNone hp _ ih => exact .delayNone hp ih
  | delaySome hp _ ih => exact .delaySome hp ih
  | syncNone hp _ ih => exact .syncNone hp ih
  | syncSome hp _ ih => exact .syncSome hp ih
  | foldNil _ _ _ ihf ihz ihl => exact .foldNil ihf ihz ihl
  | foldCons _ _ _ _ _ ihf ihz ihl ihr ihs => exact .foldCons ihf ihz ihl ihr ihs

/-! ## Part A — provider state: Mealy machines below or above the raw reading -/

/-- A stateful transducer: a Mealy machine over data.  `step` is a pure BDL
    term `σ × raw → σ × raw'`; `stepF` the same function on values; `init`
    the initial state as a pure closed term with its value. -/
structure Machine (σ raw raw' : Ty) where
  step : Expr
  stepF : Value → Value → Value × Value
  init : InitRep
  σ_data : σ.Data
  raw_data : raw.Data
  step_pure : step.Pure
  init_ty : TyVal σ init.value
  computes : ∀ s x, TyVal σ s → TyVal raw x → Transduces step (.pair s x) (.pair (stepF s x).1 (stepF s x).2)
  preserves : ∀ s x, TyVal σ s → TyVal raw x → TyVal σ (stepF s x).1 ∧ TyVal raw' (stepF s x).2

/-- The machine's run over a physical stream: the state and the output at
    every tick. -/
def Machine.run {σ raw raw' : Ty} (M : Machine σ raw raw') (x : Nat → Value) : Nat → Value × Value
  | 0 => M.stepF M.init.value (x 0)
  | t + 1 => M.stepF (M.run x t).1 (x (t + 1))

/-- The output stream: what a provider running the machine delivers. -/
def Machine.out {σ raw raw' : Ty} (M : Machine σ raw raw') (x : Nat → Value) (t : Nat) : Value := (M.run x t).2

theorem Machine.run_typed {σ raw raw' : Ty} (M : Machine σ raw raw') {x : Nat → Value} (hx : ∀ t, TyVal raw (x t)) :
    ∀ t, TyVal σ (M.run x t).1 ∧ TyVal raw' (M.run x t).2
  | 0 => M.preserves _ _ M.init_ty (hx 0)
  | t + 1 => M.preserves _ _ (M.run_typed hx t).1 (hx (t + 1))

/-- The machine **upstream**: one declaration with `delay` over the physical
    reading `r` — `m := step (pair (delay init (fst m)) r)`. -/
def machineBody {σ raw raw' : Ty} (M : Machine σ raw raw') (m r : DeclId) : Expr :=
  .app M.step (.app (.app (.prim (.pair σ raw)) (.delay M.init.term (.app (.prim (.fst σ raw')) (.declRef m)))) (.declRef r))

theorem mev_pair {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat} {ρ : List Value} (a b : Ty)
    {x y : Expr} {vx vy : Value} (hx : MEv S Δ I c t ρ x vx) (hy : MEv S Δ I c t ρ y vy) :
    MEv S Δ I c t ρ (.app (.app (.prim (.pair a b)) x) y) (.pair vx vy) := by
  have := MEv.appPrim (MEv.appPrim (MEv.prim (p := .pair a b)) hx) hy
  simpa [applyPrim, Prim.arity, Prim.compute] using this

theorem mev_fst {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat} {ρ : List Value} (a b : Ty)
    {p : Expr} {vx vy : Value} (hp : MEv S Δ I c t ρ p (.pair vx vy)) :
    MEv S Δ I c t ρ (.app (.prim (.fst a b)) p) vx := by
  have := MEv.appPrim (MEv.prim (p := .fst a b)) hp
  simpa [applyPrim, Prim.arity, Prim.compute] using this

/-- **`machine_upstream`**: in a single domain, the upstream declaration
    computes the machine's run — at every tick the pair of the state and
    the output. -/
theorem machine_upstream {σ raw raw' : Ty} (M : Machine σ raw raw') {Δ : DeclEnv} {I : Input} {m r : DeclId}
    (hm : Δ.realizationOf m = some (machineBody M m r)) (hr : Δ.realizationOf r = none)
    (hx : ∀ t, TyVal raw (I r t)) (c : ClockId) :
    ∀ t, MEv Sched.always Δ I c t [] (.declRef m) (.pair (M.run (I r) t).1 (M.run (I r) t).2) := by
  intro t
  induction t with
  | zero =>
    refine .refRealized hm ?_
    unfold machineBody
    have harg : MEv Sched.always Δ I c 0 [] (.app (.app (.prim (.pair σ raw))
        (.delay M.init.term (.app (.prim (.fst σ raw')) (.declRef m)))) (.declRef r)) (.pair M.init.value (I r 0)) :=
      mev_pair σ raw (.delayNone (by simp [prevAct]) M.init.mev) (.refInput hr)
    have hnc : (Value.pair M.init.value (I r 0)).NoClo :=
      TyVal.noClo (τ := .prod σ raw) ⟨M.σ_data, M.raw_data⟩ ⟨_, _, rfl, M.init_ty, hx 0⟩
    exact (M.computes _ _ M.init_ty (hx 0)).mev M.step_pure hnc harg
  | succ t ih =>
    refine .refRealized hm ?_
    unfold machineBody
    have hprev : prevAct Sched.always c (t + 1) = some t := by simp [prevAct, Sched.always]
    have hstate : MEv Sched.always Δ I c (t + 1) [] (.delay M.init.term (.app (.prim (.fst σ raw')) (.declRef m)))
        (M.run (I r) t).1 :=
      .delaySome hprev (mev_fst σ raw' ih)
    have harg := mev_pair (S := Sched.always) (Δ := Δ) (I := I) (c := c) (t := t + 1) σ raw hstate (.refInput hr)
    have hty := M.run_typed hx t
    have hnc : (Value.pair (M.run (I r) t).1 (I r (t + 1))).NoClo :=
      TyVal.noClo (τ := .prod σ raw) ⟨M.σ_data, M.raw_data⟩ ⟨_, _, rfl, hty.1, hx (t + 1)⟩
    exact (M.computes _ _ hty.1 (hx (t + 1))).mev M.step_pure hnc harg

theorem mev_snd {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat} {ρ : List Value} (a b : Ty)
    {p : Expr} {vx vy : Value} (hp : MEv S Δ I c t ρ p (.pair vx vy)) :
    MEv S Δ I c t ρ (.app (.prim (.snd a b)) p) vy := by
  have := MEv.appPrim (MEv.prim (p := .snd a b)) hp
  simpa [applyPrim, Prim.arity, Prim.compute] using this

/-- A realization through a channel over an arbitrary term (Phase 13's
    `realizeAt` reads a declaration). -/
def realizeWith (τ : Ty) (tr : Expr) (e : Expr) : Expr :=
  match τ with
  | .sem c => .mk c (.app tr e)
  | _ => .app tr e

theorem realizeWith_value {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat} {raw' : Ty}
    (ch : Channel raw') (hd : raw'.Data) (τ : Ty) {e : Expr} {v : Value} (hv : TyVal raw' v)
    (he : MEv S Δ I c t [] e v) :
    MEv S Δ I c t [] (realizeWith τ ch.tr e) (wrapAt τ (ch.transfer v)) := by
  have happ := (ch.computes _ hv).mev ch.tr_pure (TyVal.noClo hd hv) he
  cases τ with
  | sem c => exact .mk happ
  | bool | nat | arr _ _ | q _ | opt _ | list _ | prod _ _ => exact happ

/-- The abstract design with the physical reading `r'` and the machine `m`
    present — unused by the design, whose Source `s` is still unresolved. -/
def withMachine {σ raw raw' : Ty} (Δ : DeclEnv) (M : Machine σ raw raw') (r' m : DeclId) : DeclEnv :=
  (Δ.update ⟨r', ⟨raw, []⟩, none⟩).update ⟨m, ⟨.prod σ raw', []⟩, some (machineBody M m r')⟩

/-- The upstream placement: `s` realized from the machine's output through
    the channel, in the design with the machine. -/
def upstreamΔ {σ raw raw' : Ty} (Δ : DeclEnv) (M : Machine σ raw raw') (ch : Channel raw') (r' m s : DeclId) : DeclEnv :=
  fun d =>
    if d = s then (withMachine Δ M r' m s).map fun h =>
      ⟨h.id, h.interface, some (realizeWith h.interface.expectedType ch.tr (.app (.prim (.snd σ raw')) (.declRef m)))⟩
    else withMachine Δ M r' m d

section Movable
variable {σ raw raw' : Ty} {Θ : ConceptEnv} {Δ : DeclEnv} (M : Machine σ raw raw') (ch : Channel raw')
  {r r' m s : DeclId} {clock : Option ClockId}

/-- The provider that runs the machine below the raw reading: the raw input
    at `r` is the machine's output over the physical stream, which the base
    input carries at `r'`. -/
def belowInput (M : Machine σ raw raw') (r r' : DeclId) (base : Input) : Input :=
  fun d t => if d = r then M.out (base r') t else base d t

/-- The Source's trace under the provider below: `wrap (transfer (M.out x t))`. -/
theorem below_source_trace (wf : WF Θ (withMachine Δ M r' m) (Provision.one r s clock ch)) {base : Input}
    (hb : ∀ d t, (base d t).NoClo) (hout : ∀ t, TyVal raw' (M.out (base r') t))
    {h : DesignDecl} (hs : withMachine Δ M r' m s = some h) (c : ClockId) (t : Nat) :
    MEv Sched.always (provision (withMachine Δ M r' m) (Provision.one r s clock ch)) (belowInput M r r' base) c t []
      (.declRef s) (wrapAt h.interface.expectedType (ch.transfer (M.out (base r') t))) := by
  have hIA : RawInput (Provision.one r s clock ch) (belowInput M r r' base) := by
    refine ⟨fun t => by simp [Provision.one, belowInput, hout t], fun d t => ?_⟩
    simp only [belowInput]
    split
    · exact TyVal.noClo wf.raw_data (hout t)
    · exact hb d t
  have hsr : s ≠ r := wf.target_ne_r (Provision.one_chan_self r s clock ch)
  have := target_value (S := Sched.always) wf hIA (Provision.one_chan_self r s clock ch) hs c t
  simp only [Provision.one, belowInput, if_true] at this
  exact .refRealized (provision_realizationOf_target hsr hs (Provision.one_chan_self r s clock ch)) this

/-- The Source's trace with the machine upstream: the same value. -/
theorem upstream_source_trace (hrr : r ≠ r') (hr'm : r' ≠ m) (hsr' : s ≠ r') (hsm : s ≠ m) (hd' : raw'.Data)
    {base : Input} (hx : ∀ t, TyVal raw (base r' t))
    {h : DesignDecl} (hs : withMachine Δ M r' m s = some h) (c : ClockId) (t : Nat) :
    MEv Sched.always (upstreamΔ Δ M ch r' m s) (belowInput M r r' base) c t []
      (.declRef s) (wrapAt h.interface.expectedType (ch.transfer (M.out (base r') t))) := by
  have hmB : (upstreamΔ Δ M ch r' m s).realizationOf m = some (machineBody M m r') := by
    simp [DeclEnv.realizationOf, upstreamΔ, withMachine, DeclEnv.update, hsm.symm]
  have hrB : (upstreamΔ Δ M ch r' m s).realizationOf r' = none := by
    simp [DeclEnv.realizationOf, upstreamΔ, withMachine, DeclEnv.update, hsr'.symm, hr'm]
  have hI : (belowInput M r r' base) r' = base r' := by
    funext t; simp [belowInput, hrr.symm]
  have hrun := machine_upstream M hmB hrB (I := belowInput M r r' base) (by rw [hI]; exact hx) c t
  · have hsB : (upstreamΔ Δ M ch r' m s).realizationOf s =
        some (realizeWith h.interface.expectedType ch.tr (.app (.prim (.snd σ raw')) (.declRef m))) := by
      simp [DeclEnv.realizationOf, upstreamΔ, hs]
    refine .refRealized hsB ?_
    rw [hI] at hrun
    exact realizeWith_value ch hd' _ (M.run_typed hx t).2 (mev_snd σ raw' hrun)

/-- **`provider_state_movable`**: every evaluation of the provisioned design
    (the provider runs the machine below the raw reading) holds in the
    upstream design (the machine as a declaration over the physical
    reading, the Source realized from its output) — in the single domain,
    under one input, for every term.  The provider's state is not
    observable except through the trace it produces, and the same trace is
    available upstream; evaluation being deterministic, the values agree
    wherever both evaluate. -/
theorem provider_state_movable (wf : WF Θ (withMachine Δ M r' m) (Provision.one r s clock ch))
    (hrr : r ≠ r') (hr'm : r' ≠ m) (hsr' : s ≠ r') (hsm : s ≠ m) (hd' : raw'.Data)
    {base : Input} (hb : ∀ d t, (base d t).NoClo) (hx : ∀ t, TyVal raw (base r' t))
    (hout : ∀ t, TyVal raw' (M.out (base r') t))
    {c : ClockId} {t : Nat} {ρ : List Value} {e : Expr} {v : Value} :
    MEv Sched.always (provision (withMachine Δ M r' m) (Provision.one r s clock ch)) (belowInput M r r' base) c t ρ e v →
    MEv Sched.always (upstreamΔ Δ M ch r' m s) (belowInput M r r' base) c t ρ e v := by
  have hsr : s ≠ r := wf.target_ne_r (Provision.one_chan_self r s clock ch)
  obtain ⟨h, hs, _, _, _⟩ := wf.targets s ch (Provision.one_chan_self r s clock ch)
  have h0 : (provision (withMachine Δ M r' m) (Provision.one r s clock ch)).realizationOf r = none :=
    provision_realizationOf_r (P := Provision.one r s clock ch)
  refine MEv.congr_at s ?_ ?_ ?_
  · intro d body hd hb'
    have hdr : d ≠ r := by intro e; rw [e, h0] at hb'; exact nomatch hb'
    rw [provision_realizationOf_other hdr (Provision.one_chan_other r s clock ch hd)] at hb'
    simp only [DeclEnv.realizationOf, upstreamΔ, hd, if_false]
    exact hb'
  · intro d t hd hn c
    by_cases hdr : d = r
    · rw [hdr]
      refine .refInput ?_
      have hf : withMachine Δ M r' m r = none := wf.fresh
      simp [DeclEnv.realizationOf, upstreamΔ, hsr.symm, hf]
    · rw [provision_realizationOf_other hdr (Provision.one_chan_other r s clock ch hd)] at hn
      refine .refInput ?_
      simp only [DeclEnv.realizationOf, upstreamΔ, hd, if_false]
      exact hn
  · intro c t v hv
    rw [MEv.det hv (below_source_trace M ch wf hb hout hs c t)]
    exact upstream_source_trace M ch hrr hr'm hsr' hsm hd' hx hs c t

end Movable

/-- **`stateful_providers_same_behavior`**: two providers running different
    machines over different physical streams whose output streams coincide
    induce Phase 16's same trace for one provision — every term that does
    not mention the raw reading evaluates alike (`two_providers_same_behavior`).
    The provider's state, whatever it is, is unobservable except through
    the output stream. -/
theorem stateful_providers_same_trace {σ₁ raw₁ σ₂ raw₂ raw' : Ty} (M₁ : Machine σ₁ raw₁ raw') (M₂ : Machine σ₂ raw₂ raw')
    {Δ : DeclEnv} {r s : DeclId} {clock : Option ClockId} {ch : Channel raw'} {x₁ x₂ : Nat → Value} {base : Input}
    (hsame : ∀ t, M₁.out x₁ t = M₂.out x₂ t) :
    SameTrace Δ (Provision.one r s clock ch) (Provision.one r s clock ch)
      (fun d t => if d = r then M₁.out x₁ t else base d t) (fun d t => if d = r then M₂.out x₂ t else base d t) := by
  intro d t h₁ _
  simp only [Provision.one] at h₁
  simp only [induced, Provision.one]
  by_cases hd : d = s
  · subst hd; simp [hsame t]
  · simp [hd, h₁]

/-! ## Part B — the Source-side device clock -/

/-- The sampled realization of a Source from a raw reading in another
    domain: `mk c (tr (sync pc init r))` — the input dual of Phase 15's
    `syncBody`. -/
def syncRealizeAt (τ : Ty) (tr : Expr) (pc : ClockId) (init : Expr) (r : DeclId) : Expr :=
  realizeWith τ tr (.sync pc init (.declRef r))

/-- **`provisionSync`**: the raw reading `r` added unresolved (read in the
    provider's domain `pc`), the Source `s` realized by the sampled
    transducer; everything else untouched. -/
def provisionSync {raw : Ty} (Δ : DeclEnv) (r s : DeclId) (pc : ClockId) (i : InitRep) (ch : Channel raw) : DeclEnv :=
  fun d =>
    if d = r then some ⟨r, ⟨raw, []⟩, none⟩
    else if d = s then (Δ s).map fun h =>
      ⟨h.id, h.interface, some (syncRealizeAt h.interface.expectedType ch.tr pc i.term r)⟩
    else Δ d

def provisionSyncΚ (Κ : ClockEnv) (r : DeclId) (pc : ClockId) : ClockEnv :=
  fun d => if d = r then some pc else Κ d

/-- The reading the Source samples at global tick `t`: the raw value at the
    last activation of `pc` strictly before `t`, or the initial value. -/
def sampled (S : Sched) (pc : ClockId) (i : InitRep) (I' : Input) (r : DeclId) (t : Nat) : Value :=
  match prevAct S pc t with
  | some t' => I' r t'
  | none => i.value

/-- **The induced input** of the sampled provision: at `s`, the wrapped
    transfer of the sampled reading; elsewhere the raw input. -/
def inducedSync {raw : Ty} (Δ : DeclEnv) (S : Sched) (r s : DeclId) (pc : ClockId) (i : InitRep) (ch : Channel raw)
    (I' : Input) : Input :=
  fun d t => if d = s then
    (match Δ.tyView s with | some τ => wrapAt τ (ch.transfer (sampled S pc i I' r t)) | none => I' d t)
  else I' d t

section Sync
variable {raw : Ty} {Θ : ConceptEnv} {Δ : DeclEnv} {S : Sched} {r s : DeclId} {pc : ClockId} {i : InitRep}
  {ch : Channel raw} {I' : Input}

theorem provisionSync_r : provisionSync Δ r s pc i ch r = some ⟨r, ⟨raw, []⟩, none⟩ := by simp [provisionSync]
theorem provisionSync_other {d : DeclId} (hr : d ≠ r) (hs : d ≠ s) : provisionSync Δ r s pc i ch d = Δ d := by
  simp [provisionSync, hr, hs]
theorem provisionSync_s (hsr : s ≠ r) {h : DesignDecl} (hs : Δ s = some h) :
    provisionSync Δ r s pc i ch s =
      some ⟨h.id, h.interface, some (syncRealizeAt h.interface.expectedType ch.tr pc i.term r)⟩ := by
  simp [provisionSync, hsr, hs]
theorem provisionSync_realizationOf_other {d : DeclId} (hr : d ≠ r) (hs : d ≠ s) :
    (provisionSync Δ r s pc i ch).realizationOf d = Δ.realizationOf d := by
  simp [DeclEnv.realizationOf, provisionSync_other hr hs]
theorem provisionSync_realizationOf_r : (provisionSync Δ r s pc i ch).realizationOf r = none := by
  simp [DeclEnv.realizationOf, provisionSync_r]

/-- The sampled reading, as `sync` evaluates it in the Source's domain. -/
theorem sampled_mev (hr : (provisionSync Δ r s pc i ch).realizationOf r = none) (c : ClockId) (t : Nat) :
    MEv S (provisionSync Δ r s pc i ch) I' c t [] (.sync pc i.term (.declRef r)) (sampled S pc i I' r t) := by
  unfold sampled
  cases hp : prevAct S pc t with
  | none => exact .syncNone hp i.mev
  | some t' => exact .syncSome hp (.refInput hr)

theorem sampled_tyVal (hI : ∀ t, TyVal raw (I' r t)) (hi : TyVal raw i.value) (t : Nat) :
    TyVal raw (sampled S pc i I' r t) := by
  unfold sampled; cases prevAct S pc t <;> simp [hI, hi]

/-- **`provisionSync_target`**: the Source carries, in every domain and at
    every tick, the wrapped transfer of the reading sampled at the last
    activation of the provider's domain strictly before — or of the initial
    value when there was none.  The sampling is explicit; the initial value
    is explicit. -/
theorem provisionSync_target (hsr : s ≠ r) {h : DesignDecl} (hs : Δ s = some h) (hd : raw.Data)
    (hI : ∀ t, TyVal raw (I' r t)) (hi : TyVal raw i.value) (c : ClockId) (t : Nat) :
    MEv S (provisionSync Δ r s pc i ch) I' c t [] (.declRef s)
      (wrapAt h.interface.expectedType (ch.transfer (sampled S pc i I' r t))) := by
  have hsn : (provisionSync Δ r s pc i ch).realizationOf s =
      some (syncRealizeAt h.interface.expectedType ch.tr pc i.term r) := by
    simp [DeclEnv.realizationOf, provisionSync_s hsr hs]
  exact .refRealized hsn (realizeWith_value ch hd _ (sampled_tyVal hI hi t) (sampled_mev provisionSync_realizationOf_r c t))

/-- **`provisionSync_transparent`**: the abstract design under the induced
    input and the sampled provision under the raw input evaluate every term
    alike — `MEv.congr_at` at `s`, with the target's value from
    `provisionSync_target`. -/
theorem provisionSync_transparent (hsr : s ≠ r) (hfresh : Δ r = none) {h : DesignDecl} (hs : Δ s = some h)
    (hun : h.realization = none) (hd : raw.Data) (hI : ∀ t, TyVal raw (I' r t)) (hi : TyVal raw i.value)
    {c : ClockId} {t : Nat} {ρ : List Value} {e : Expr} {v : Value} :
    MEv S Δ (inducedSync Δ S r s pc i ch I') c t ρ e v → MEv S (provisionSync Δ r s pc i ch) I' c t ρ e v := by
  refine MEv.congr_at s ?_ ?_ ?_
  · intro d body hd' hb
    have hdr : d ≠ r := by intro e; rw [e] at hb; simp [DeclEnv.realizationOf, hfresh] at hb
    rw [provisionSync_realizationOf_other hdr hd']; exact hb
  · intro d t hd' hn c
    simp only [inducedSync, hd', if_false]
    by_cases hdr : d = r
    · rw [hdr]; exact .refInput provisionSync_realizationOf_r
    · exact .refInput (by rw [provisionSync_realizationOf_other hdr hd']; exact hn)
  · intro c t v hv
    have hsn : Δ.realizationOf s = none := by simp [DeclEnv.realizationOf, hs, hun]
    have hval : v = inducedSync Δ S r s pc i ch I' s t := by
      cases hv with
      | refRealized hr _ => rw [hsn] at hr; exact nomatch hr
      | refInput _ => rfl
    rw [hval]
    simp only [inducedSync, if_true, DeclEnv.tyView, hs, Option.map_some]
    exact provisionSync_target hsr hs hd hI hi c t

/-- No new instantaneous edge: the transport reads strictly before, the
    initial value is pure. -/
theorem syncRealizeAt_instRefs (τ : Ty) {tr init : Expr} (htr : tr.Pure) (hi : init.Pure) (pc : ClockId) (r : DeclId) :
    (syncRealizeAt τ tr pc init r).instRefs = [] := by
  cases τ <;> simp [syncRealizeAt, realizeWith, Expr.instRefs, Expr.Pure.instRefs_nil htr, Expr.Pure.instRefs_nil hi]

theorem provisionSync_causal (hsr : s ≠ r) (htr : ch.tr.Pure) (hc : Causal Δ) :
    Causal (provisionSync Δ r s pc i ch) := by
  obtain ⟨rank, Rk, hR, hedge⟩ := hc
  refine ⟨rank, Rk, hR, ?_⟩
  intro a b hab
  obtain ⟨body, hb, hmem⟩ := InstDependsOn.iff.mp hab
  by_cases has : a = s
  · rw [has] at hb
    cases hΔs : Δ s with
    | none => simp [DeclEnv.realizationOf, provisionSync, hsr, hΔs] at hb
    | some h =>
      simp [DeclEnv.realizationOf, provisionSync_s hsr hΔs] at hb
      rw [← hb, syncRealizeAt_instRefs _ htr i.pure] at hmem
      simp at hmem
  · have har : a ≠ r := by intro e; rw [e, provisionSync_realizationOf_r] at hb; exact nomatch hb
    rw [provisionSync_realizationOf_other har has] at hb
    exact hedge a b (InstDependsOn.iff.mpr ⟨body, hb, hmem⟩)

/-- Well clocked: the raw reading in the provider's domain, the Source's
    body clocked in the Source's own domain (the transport's operand is
    read in `pc`, the transducer and the initial value are pure). -/
theorem provisionSync_wellClocked {Κ : ClockEnv} {cs : ClockId} (hsK : Κ s = some cs) (hsr : s ≠ r)
    (htr : ch.tr.Pure) (nm : NoMention Δ r) (hK : WellClocked Κ Δ) :
    WellClocked (provisionSyncΚ Κ r pc) (provisionSync Δ r s pc i ch) := by
  intro d body hb
  by_cases hds : d = s
  · rw [hds] at hb ⊢
    cases hΔs : Δ s with
    | none => simp [DeclEnv.realizationOf, provisionSync, hsr, hΔs] at hb
    | some h =>
      simp [DeclEnv.realizationOf, provisionSync_s hsr hΔs] at hb
      rw [← hb]
      unfold Clocked
      have hrK : provisionSyncΚ Κ r pc r = some pc := by simp [provisionSyncΚ]
      simp only [provisionSyncΚ, hsr, if_false, hsK]
      cases h.interface.expectedType <;>
        simp [syncRealizeAt, realizeWith, clockedB, Expr.Pure.clocked (provisionSyncΚ Κ r pc) _ htr,
          Expr.Pure.clocked (provisionSyncΚ Κ r pc) _ i.pure, hrK]
  · have hdr : d ≠ r := by intro e; rw [e, provisionSync_realizationOf_r] at hb; exact nomatch hb
    rw [provisionSync_realizationOf_other hdr hds] at hb
    have := hK d body hb
    unfold Clocked at this ⊢
    simp only [provisionSyncΚ, hdr, if_false]
    rw [← clockedB_congr (fun y hy => ?_)]
    · exact this
    · have hyr : y ≠ r := fun e => nm d body hb (e ▸ hy)
      simp [provisionSyncΚ, hyr]

/-- The Source's realization is typed at its expected type under its own
    grant: the transducer typed `raw -> rep` in the empty design, the
    transport at the data type `raw` with the initial value typed at `raw`. -/
theorem syncRealizeAt_typed (hd : raw.Data) (htr : ch.WF Θ) (hi : HasType Θ DeclEnv.empty Grant.none [] i.term raw)
    {τ : Ty} (hfit : Fits Θ τ ch) (hrK : (provisionSync Δ r s pc i ch).tyView r = some raw) :
    HasType Θ (provisionSync Δ r s pc i ch) (Grant.of τ) [] (syncRealizeAt τ ch.tr pc i.term r) τ := by
  have htr' : HasType Θ (provisionSync Δ r s pc i ch) (Grant.of τ) [] ch.tr (.arr raw ch.rep) :=
    (htr.refFree_env_irrelevant (refFree_of_empty_typed htr)).mono_grant (fun _ hf => hf.elim)
  have hi' : HasType Θ (provisionSync Δ r s pc i ch) (Grant.of τ) [] i.term raw :=
    (hi.refFree_env_irrelevant (refFree_of_empty_typed hi)).mono_grant (fun _ hf => hf.elim)
  have hsy : HasType Θ (provisionSync Δ r s pc i ch) (Grant.of τ) [] (.sync pc i.term (.declRef r)) raw :=
    .sync hd hi' (.declRef hrK)
  unfold Fits at hfit
  cases τ with
  | sem c =>
    simp only [syncRealizeAt, realizeWith]
    exact .mk (by simp [Grant.of, Ty.grant]) hfit (.app htr' hsy)
  | bool | nat | arr _ _ | q _ | opt _ | list _ | prod _ _ =>
    simp only at hfit
    simp only [syncRealizeAt, realizeWith]
    rw [hfit] at htr' hsy ⊢
    exact .app htr' hsy


theorem provisionSync_envRefines (hsr : s ≠ r) (hfresh : Δ r = none) {h : DesignDecl} (hs : Δ s = some h)
    (hun : h.realization = none) : EnvRefines Δ (provisionSync Δ r s pc i ch) := by
  intro d hd hds
  by_cases hdr : d = r
  · rw [hdr, hfresh] at hds; exact nomatch hds
  by_cases hd' : d = s
  · rw [hd'] at hds ⊢
    rw [hs] at hds; cases hds
    refine ⟨_, provisionSync_s hsr hs, rfl, InterfaceRefines.refl _, fun e he => ?_⟩
    rw [hun] at he; exact nomatch he
  · exact ⟨hd, by rw [provisionSync_other hdr hd']; exact hds, DeclLeq.refl hd⟩

/-- **`provisionSync_wf`**: globally well formed from the abstract design
    well formed, monotone evidence, the transducer's contract, the initial
    value typed at `raw`, and the target's commitments discharged on its
    new realization (FVD-0128's obligation, unchanged). -/
theorem provisionSync_wf {ev : Evidence} (mono : ev.Monotone) (g : GlobalWF ev Θ Δ) (hsr : s ≠ r) (hfresh : Δ r = none)
    {h : DesignDecl} (hs : Δ s = some h) (hun : h.realization = none) (hd : raw.Data)
    (htr : ch.WF Θ) (hi : HasType Θ DeclEnv.empty Grant.none [] i.term raw) (hfit : Fits Θ h.interface.expectedType ch)
    (hcomm : ∀ p ∈ h.interface.commitments,
      ev (provisionSync Δ r s pc i ch) (syncRealizeAt h.interface.expectedType ch.tr pc i.term r) p) :
    GlobalWF ev Θ (provisionSync Δ r s pc i ch) := by
  have er := provisionSync_envRefines (i := i) (ch := ch) (pc := pc) hsr hfresh hs hun
  intro d hd' hds
  by_cases hdr : d = r
  · rw [hdr] at hds ⊢
    rw [provisionSync_r] at hds; cases hds
    exact ⟨rfl, WellFormedDecl.unresolved _ _ _ _ _ _⟩
  by_cases hd'' : d = s
  · rw [hd''] at hds ⊢
    rw [provisionSync_s hsr hs] at hds
    rw [← Option.some.inj hds]
    have hid : h.id = s := g.stored_id hs
    refine ⟨hid, fun e he => ?_⟩
    simp only at he; rw [← Option.some.inj he]
    refine ⟨syncRealizeAt_typed hd htr hi hfit ?_, hcomm⟩
    simp [DeclEnv.tyView, provisionSync_r]
  · rw [provisionSync_other hdr hd''] at hds
    exact ⟨g.stored_id hds, (g.wellFormed hds).of_envRefines mono er⟩

end Sync

/-! ### The occurrence-like crossing: the window over the raw reading -/

/-- **`provisionWindow`**: the raw reading `r` (in `pc`, an input) is the
    source of Phase 9a's five declarations; the Source `s` is realized by
    the transducer over `window` in its own domain.  No second crossing:
    `buffer_window_correspondence` is used as it stands. -/
def provisionWindow {raw : Ty} (Δ : DeclEnv) (r s : DeclId) (pc : ClockId) (ids : Buffer.Ids)
    (ch : Channel (.list raw)) : DeclEnv :=
  let Δ' := (((((Δ.update ⟨r, ⟨raw, []⟩, none⟩).update (logDecl raw ids)).update (logDDecl raw pc ids)).update
    (seenDecl raw ids)).update (cursorDecl ids)).update (windowDecl raw ids)
  fun d => if d = s then (Δ' s).map fun h =>
      ⟨h.id, h.interface, some (realizeWith h.interface.expectedType ch.tr (.declRef ids.window))⟩
    else Δ' d

/-- **`provisionWindow_target`**: the Source carries the transfer of the
    batches read at the provider's activations since the Source's domain's
    previous activation — in order and with multiplicity. -/
theorem provisionWindow_target {raw : Ty} {Δ : DeclEnv} {S : Sched} {I' : Input} {r s : DeclId} {pc : ClockId}
    {ids : Buffer.Ids} {ch : Channel (.list raw)} (hids : ids.src = r)
    (R : Realized raw pc ids (provisionWindow Δ r s pc ids ch)) (hd : raw.Data)
    (hI : ∀ t, TyVal raw (I' r t)) {h : DesignDecl}
    (hs : provisionWindow Δ r s pc ids ch s =
      some ⟨h.id, h.interface, some (realizeWith h.interface.expectedType ch.tr (.declRef ids.window))⟩)
    (c : ClockId) (t : Nat) :
    MEv S (provisionWindow Δ r s pc ids ch) I' c t [] (.declRef s)
      (wrapAt h.interface.expectedType (ch.transfer (.list ((windowTicks S pc c t).map (I' r))))) := by
  have hsn : (provisionWindow Δ r s pc ids ch).realizationOf s =
      some (realizeWith h.interface.expectedType ch.tr (.declRef ids.window)) := by
    simp [DeclEnv.realizationOf, hs]
  refine .refRealized hsn ?_
  have hw := buffer_window_correspondence (S := S) (I := I') R c t
  rw [hids] at hw
  refine realizeWith_value ch hd _ ⟨_, rfl, fun w hw' => ?_⟩ hw
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp hw'
  exact hI u

/-! ## Part C — commitment discharge -/

/-- Evidence that accepts value-range facts *under an assumption on the raw
    reading*: `ev Δ e p` holds whenever every value `e` takes, under every
    input whose reading at `r` satisfies `A` at every tick, has the property
    `R p`.  Who establishes `A` is the evidence level. -/
def RangeSoundUnder (ev : Evidence) (R : PropertyId → Value → Prop) (r : DeclId) (A : Value → Prop) : Prop :=
  ∀ Δ e p, (∀ (S : Sched) (I : Input) c t v, (∀ t, A (I r t)) → MEv S Δ I c t [] e v → R p v) → ev Δ e p

/-- The target's realization takes only the transferred readings. -/
theorem realizeAt_only_transfers {raw : Ty} {Δ : DeclEnv} {S : Sched} {I : Input} {r : DeclId} {ch : Channel raw}
    (hd : raw.Data) (hr : Δ.realizationOf r = none) (hI : ∀ t, TyVal raw (I r t)) (τ : Ty) {c : ClockId} {t : Nat}
    {v : Value} (h : MEv S Δ I c t [] (realizeAt τ ch.tr r) v) : v = wrapAt τ (ch.transfer (I r t)) := by
  have hv := realizeWith_value (S := S) (Δ := Δ) (I := I) (c := c) (t := t) ch hd τ (hI t) (.refInput hr)
  have e : realizeAt τ ch.tr r = realizeWith τ ch.tr (.declRef r) := by cases τ <;> rfl
  rw [e] at h
  exact MEv.det h hv

/-- **`discharge_under`**: the commitment `p` on the provisioned target is
    discharged when the transfer of every reading satisfying `A` has the
    property — for evidence sound under `A`. -/
theorem discharge_under {raw : Ty} {Θ : ConceptEnv} {Δ : DeclEnv} {P : Provision raw} (wf : WF Θ Δ P)
    {ev : Evidence} {R : PropertyId → Value → Prop} {A : Value → Prop}
    (sound : RangeSoundUnder ev R P.r A) (hA : ∀ v, A v → TyVal raw v)
    (ch : Channel raw) (τ : Ty) {p : PropertyId}
    (hR : ∀ v, A v → R p (wrapAt τ (ch.transfer v))) :
    ev (provision Δ P) (realizeAt τ ch.tr P.r) p := by
  refine sound _ _ _ (fun S I c t v hI hv => ?_)
  have := realizeAt_only_transfers (S := S) wf.raw_data provision_realizationOf_r (fun t => hA _ (hI t)) _ hv
  rw [this]; exact hR _ (hI t)

/-- **Static**: the transducer alone — `A` is typing at the raw type; nothing
    is assumed of the world beyond the reading being a `raw`. -/
theorem discharge_static {raw : Ty} {Θ : ConceptEnv} {Δ : DeclEnv} {P : Provision raw} (wf : WF Θ Δ P)
    {ev : Evidence} {R : PropertyId → Value → Prop} (sound : RangeSoundUnder ev R P.r (TyVal raw))
    (ch : Channel raw) (τ : Ty) {p : PropertyId}
    (hR : ∀ v, TyVal raw v → R p (wrapAt τ (ch.transfer v))) :
    ev (provision Δ P) (realizeAt τ ch.tr P.r) p :=
  discharge_under wf sound (fun _ h => h) ch τ hR

/-- **Trusted**: `A` is a range the profile asserts of the device; the
    assumption is the hypothesis `sound` carries — visible, never
    discharged here. -/
theorem discharge_trusted {raw : Ty} {Θ : ConceptEnv} {Δ : DeclEnv} {P : Provision raw} (wf : WF Θ Δ P)
    {ev : Evidence} {R : PropertyId → Value → Prop} {range : Value → Prop}
    (sound : RangeSoundUnder ev R P.r (fun v => TyVal raw v ∧ range v))
    (ch : Channel raw) (τ : Ty) {p : PropertyId}
    (hR : ∀ v, TyVal raw v → range v → R p (wrapAt τ (ch.transfer v))) :
    ev (provision Δ P) (realizeAt τ ch.tr P.r) p :=
  discharge_under wf sound (fun _ h => h.1) ch τ (fun v hv => hR v hv.1 hv.2)

/-! ## Part E — out-of-type readings: the checking provider -/

/-- A checking provider: a delivery whose payload fails `ok` is refused
    before deduplication; the refused count is the second flag. -/
def checkedProvide (C : Contract) (ok : Value → Bool) (seen : Seen) (ds : List Delivery) : Batch × Bool × Seen :=
  let good := ds.filter fun d => ok d.payload
  let r := provide C seen good
  (r.1, decide (good.length < ds.length), r.2)

theorem checked_items_ok (C : Contract) (ok : Value → Bool) (seen : Seen) (ds : List Delivery) :
    ∀ w ∈ (checkedProvide C ok seen ds).1.items, ok w = true := by
  intro w hw
  have hsub := provide_items_sublist C seen (ds.filter fun d => ok d.payload)
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (hsub.subset hw)
  exact (List.mem_filter.mp hd).2

/-- **`checked_typed`**: when `ok` implies typing, every item of the
    checked batch is a `raw` — a malformed reading cannot enter. -/
theorem checked_typed {raw : Ty} (C : Contract) {ok : Value → Bool} (hok : ∀ v, ok v = true → TyVal raw v)
    (seen : Seen) (ds : List Delivery) : ∀ w ∈ (checkedProvide C ok seen ds).1.items, TyVal raw w :=
  fun w hw => hok w (checked_items_ok C ok seen ds w hw)

theorem filter_length_lt_iff {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length < l.length ↔ ∃ a ∈ l, p a = false
  | [] => by simp
  | a :: l => by
    have hle := List.length_filter_le p l
    cases hp : p a
    · rw [List.filter_cons_of_neg (by simp [hp])]
      simp only [List.length_cons, List.mem_cons]
      constructor
      · intro _; exact ⟨a, Or.inl rfl, hp⟩
      · intro _; omega
    · rw [List.filter_cons_of_pos (by simp [hp])]
      simp only [List.length_cons, List.mem_cons, Nat.add_lt_add_iff_right]
      rw [filter_length_lt_iff p l]
      constructor
      · rintro ⟨b, hb, hpb⟩; exact ⟨b, Or.inr hb, hpb⟩
      · rintro ⟨b, (rfl | hb), hpb⟩
        · rw [hp] at hpb; exact nomatch hpb
        · exact ⟨b, hb, hpb⟩

/-- The refused flag is exact. -/
theorem checked_refused_iff (C : Contract) (ok : Value → Bool) (seen : Seen) (ds : List Delivery) :
    (checkedProvide C ok seen ds).2.1 = true ↔ ∃ d ∈ ds, ok d.payload = false := by
  simp only [checkedProvide, decide_eq_true_eq]
  exact filter_length_lt_iff _ ds

/-- **Checked**: `A` is `ok`, established by the checking provider; the
    reading is `TyVal` by construction and the discharge follows. -/
theorem discharge_checked {raw : Ty} {Θ : ConceptEnv} {Δ : DeclEnv} {P : Provision raw} (wf : WF Θ Δ P)
    {ev : Evidence} {R : PropertyId → Value → Prop} {ok : Value → Bool} (hok : ∀ v, ok v = true → TyVal raw v)
    (sound : RangeSoundUnder ev R P.r (fun v => ok v = true))
    (ch : Channel raw) (τ : Ty) {p : PropertyId}
    (hR : ∀ v, ok v = true → R p (wrapAt τ (ch.transfer v))) :
    ev (provision Δ P) (realizeAt τ ch.tr P.r) p :=
  discharge_under wf sound hok ch τ hR

/-! ## Part D — `computes` -/

/-- A channel whose transfer function *is* the term's evaluation: `computes`
    is derived, not supplied.  `total` says the interpreter yields a value on
    every raw-typed input within the fuel. -/
def Channel.ofTerm (raw rep : Ty) (tr : Expr) (fuel : Nat) (hs : rep.SemFree) (hd : rep.Data) (hp : tr.Pure)
    (total : ∀ v, TyVal raw v → ∃ w, evalF DeclEnv.empty (fun _ _ => v) fuel 0 [] (.app tr (.declRef ⟨0⟩)) = some w) :
    Channel raw where
  rep := rep
  tr := tr
  transfer := fun v => (evalF DeclEnv.empty (fun _ _ => v) fuel 0 [] (.app tr (.declRef ⟨0⟩))).getD v
  rep_semFree := hs
  rep_data := hd
  tr_pure := hp
  computes := by
    intro v hv
    obtain ⟨w, hw⟩ := total v hv
    unfold Transduces
    rw [hw]
    exact Ev.of_evalF hw

/-- For a finite raw type the coherence of a supplied transfer function with
    the term is decided by evaluating both raw values. -/
def computesBool (tr : Expr) (fuel : Nat) (transfer : Value → Value) : Bool :=
  [true, false].all fun b =>
    match evalF DeclEnv.empty (fun _ _ => .bool b) fuel 0 [] (.app tr (.declRef ⟨0⟩)) with
    | some w => Value.beq w (transfer (.bool b))
    | none => false

mutual
theorem Value.beq_sound : ∀ {v w : Value}, Value.beq v w = true → v = w
  | .bool a, .bool b, h => by simp [Value.beq] at h; rw [h]
  | .nat a, .nat b, h => by simp [Value.beq] at h; rw [h]
  | .sem s v, .sem s' w, h => by
    simp only [Value.beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, Value.beq_sound h.2]
  | .none, .none, _ => rfl
  | .some v, .some w, h => by
    simp only [Value.beq] at h; rw [Value.beq_sound h]
  | .pair a b, .pair c d, h => by
    simp only [Value.beq, Bool.and_eq_true] at h
    rw [Value.beq_sound h.1, Value.beq_sound h.2]
  | .list vs, .list ws, h => by
    simp only [Value.beq] at h; rw [Value.beqList_sound h]
  | .bool _, .nat _, h | .bool _, .sem _ _, h | .bool _, .none, h | .bool _, .some _, h | .bool _, .clo _ _, h
  | .bool _, .prim _ _, h | .bool _, .list _, h | .bool _, .pair _ _, h => by simp [Value.beq] at h
  | .nat _, .bool _, h | .nat _, .sem _ _, h | .nat _, .none, h | .nat _, .some _, h | .nat _, .clo _ _, h
  | .nat _, .prim _ _, h | .nat _, .list _, h | .nat _, .pair _ _, h => by simp [Value.beq] at h
  | .sem _ _, .bool _, h | .sem _ _, .nat _, h | .sem _ _, .none, h | .sem _ _, .some _, h | .sem _ _, .clo _ _, h
  | .sem _ _, .prim _ _, h | .sem _ _, .list _, h | .sem _ _, .pair _ _, h => by simp [Value.beq] at h
  | .none, .bool _, h | .none, .nat _, h | .none, .sem _ _, h | .none, .some _, h | .none, .clo _ _, h
  | .none, .prim _ _, h | .none, .list _, h | .none, .pair _ _, h => by simp [Value.beq] at h
  | .some _, .bool _, h | .some _, .nat _, h | .some _, .sem _ _, h | .some _, .none, h | .some _, .clo _ _, h
  | .some _, .prim _ _, h | .some _, .list _, h | .some _, .pair _ _, h => by simp [Value.beq] at h
  | .clo _ _, _, h => by simp [Value.beq] at h
  | .prim _ _, _, h => by simp [Value.beq] at h
  | .list _, .bool _, h | .list _, .nat _, h | .list _, .sem _ _, h | .list _, .none, h | .list _, .some _, h
  | .list _, .clo _ _, h | .list _, .prim _ _, h | .list _, .pair _ _, h => by simp [Value.beq] at h
  | .pair _ _, .bool _, h | .pair _ _, .nat _, h | .pair _ _, .sem _ _, h | .pair _ _, .none, h | .pair _ _, .some _, h
  | .pair _ _, .clo _ _, h | .pair _ _, .prim _ _, h | .pair _ _, .list _, h => by simp [Value.beq] at h
theorem Value.beqList_sound : ∀ {vs ws : List Value}, Value.beqList vs ws = true → vs = ws
  | [], [], _ => rfl
  | v :: vs, w :: ws, h => by
    simp only [Value.beqList, Bool.and_eq_true] at h
    rw [Value.beq_sound h.1, Value.beqList_sound h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [Value.beqList] at h
end

/-- **`computes_of_bool`**: a passed check *is* the coherence obligation at
    the raw type `bool`. -/
theorem computes_of_bool {tr : Expr} {fuel : Nat} {transfer : Value → Value} (h : computesBool tr fuel transfer = true) :
    ∀ v, TyVal .bool v → Transduces tr v (transfer v) := by
  rintro v ⟨b, rfl⟩
  simp only [computesBool, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  have hb : (match evalF DeclEnv.empty (fun _ _ => Value.bool b) fuel 0 [] (.app tr (.declRef ⟨0⟩)) with
      | some w => Value.beq w (transfer (.bool b)) | none => false) = true := by
    cases b
    · exact h.2
    · exact h.1
  unfold Transduces
  cases he : evalF DeclEnv.empty (fun _ _ => Value.bool b) fuel 0 [] (.app tr (.declRef ⟨0⟩)) with
  | none => rw [he] at hb; exact nomatch hb
  | some w =>
    rw [he] at hb
    rw [← Value.beq_sound hb]
    exact Ev.of_evalF he

/-! ## Part F — the richer profile -/

/-- What a Source's initial value is before the provider has produced one:
    a profile-supplied raw value, or the optional form (`none` at an
    optional raw type, which the design reads as *unavailable*).  Both are
    an `InitRep`; the constructor records which was chosen. -/
inductive InitPolicy where
  | supplied (i : InitRep)
  | unavailable (i : InitRep)

def InitPolicy.rep : InitPolicy → InitRep
  | .supplied i => i
  | .unavailable i => i

/-- A package-provided Source profile: Phase 13's profile with what this
    phase adds — the optional machine, the initial policy, the delivery
    contract, a range assumed of the device (the trusted part, named).  A
    catalogue entry with an origin (Phase 16). -/
structure ProviderProfile where
  entry : InputEntry
  init : InitPolicy
  contract : Contract
  assumedRange : Option (Value → Prop)

/-- **`assignSource_profile_only`**: the assignment reads Phase 13's profile
    and nothing the richer profile adds — the machine, the policy, the
    contract, the assumption select provider constructions below the
    reading and never enter the design. -/
theorem assignSource_profile_only {Δ : DeclEnv} {pp₁ pp₂ : ProviderProfile} (h : pp₁.entry.profile = pp₂.entry.profile)
    (i : Nat) (r s : DeclId) (clock : Option ClockId) :
    assignSource Δ pp₁.entry i r s clock = assignSource Δ pp₂.entry i r s clock :=
  assignSource_origin_irrelevant h i r s clock

/-! ## A machine from its term -/

/-- A machine whose step function *is* its term's evaluation: `computes` is
    derived; what is supplied is the term, the initial state, the totality
    of the interpreter on typed inputs and the typing of the results. -/
def Machine.ofTerm (σ raw raw' : Ty) (step : Expr) (init : InitRep) (fuel : Nat) (hσ : σ.Data) (hr : raw.Data)
    (hp : step.Pure) (hi : TyVal σ init.value)
    (total : ∀ s x, TyVal σ s → TyVal raw x →
      ∃ s' y, evalF DeclEnv.empty (fun _ _ => .pair s x) fuel 0 [] (.app step (.declRef ⟨0⟩)) = some (.pair s' y) ∧
        TyVal σ s' ∧ TyVal raw' y) : Machine σ raw raw' where
  step := step
  stepF := fun s x => match evalF DeclEnv.empty (fun _ _ => .pair s x) fuel 0 [] (.app step (.declRef ⟨0⟩)) with
    | some (.pair s' y) => (s', y)
    | _ => (s, x)
  init := init
  σ_data := hσ
  raw_data := hr
  step_pure := hp
  init_ty := hi
  computes := by
    intro s x hs hx
    obtain ⟨s', y, he, _, _⟩ := total s x hs hx
    unfold Transduces
    simp only [he]
    exact Ev.of_evalF he
  preserves := by
    intro s x hs hx
    obtain ⟨s', y, he, hs', hy⟩ := total s x hs hx
    simp only [he]
    exact ⟨hs', hy⟩

end BDL.SourceBoundary
