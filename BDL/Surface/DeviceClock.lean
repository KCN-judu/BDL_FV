import BDL.Surface.Adapter

/-!
# Phase 15 — The explicit device clock: realization through a `sync`

Phase 14 realizes an output in the output's own clock and refuses an
implicit crossing (`exI`).  A device that consumes commands at another
rate — a bus schedule, a display refresh — needs the crossing to be
*explicit*.  This module tests the explicit variant: the encoder
declaration lives in the device domain `dc` and reads the driver's
representation through Phase 5's transport,

    e := encode (sync c initRep (rep d))        e, p in domain dc

with `c` the output's clock and `initRep` a pure closed representation
value for the ticks before `c`'s first activation.  Nothing new enters the
kernel: `sync` is the Phase-5 primitive, `rep` needs no grant, and the
transport reads strictly before.

What must be explicit in the *lowering*: the device domain `dc` and the
initial representation `initRep`.  What belongs to *deployment*: the choice
of both — the design still says nothing about a device.  What survives: the
behaviour is literally unchanged off `e` (`lowerSync_transparent`), the
lowered design is well formed, causal (no new instantaneous edge at all —
the transport is never instantaneous), well clocked and single-driver; the
correspondence samples strictly before: at a device tick `t` the sink
carries `transfer` of the command the output specified at the last
activation of `c` before `t`, or of `initRep` if there was none
(`lowerSync_correspondence`).

Not modelled, still: a carrier frequency (configuration, FVD-0138), a bus
schedule with acknowledgement, anything below the raw command.
-/

namespace BDL.DeviceClock
open BDL BDL.Reactive BDL.Clock BDL.Output BDL.Provision BDL.OutputRealization BDL.Adapter

/-- A pure closed representation value: the term and the value it has in
    every context (`MEv.of_ev_pure`). -/
structure InitRep where
  term : Expr
  value : Value
  pure : term.Pure
  evaluates : Ev DeclEnv.empty (fun _ _ => .nat 0) 0 [] term value

theorem InitRep.mev (i : InitRep) {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat} :
    MEv S Δ I c t [] i.term i.value :=
  MEv.of_ev_pure i.evaluates i.pure (fun _ h => by simp at h)

theorem InitRep.value_pure (i : InitRep) : i.value.Pure :=
  (Ev.pure i.evaluates i.pure (fun _ h => by simp at h)).1

/-- The encoder body through the transport: at a semantic output the
    driver's representation is transported, at a data output the value. -/
def syncBody (accepts : Ty) (encode : Expr) (c : ClockId) (init : Expr) (d : DeclId) : Expr :=
  match accepts with
  | .sem _ => .app encode (.sync c init (.rep (.declRef d)))
  | _ => .app encode (.sync c init (.declRef d))

def lowerSyncΔ (Δ : DeclEnv) (R : Realization) (spec : OutputSpec) (i : InitRep) : DeclEnv :=
  Δ.update ⟨R.e, ⟨R.E.raw, []⟩, some (syncBody spec.accepts R.E.encode spec.clock i.term R.d)⟩

def lowerSyncΩ (Ω : OutputEnv) (R : Realization) (dc : ClockId) : OutputEnv :=
  fun q => if q = R.p then some ⟨R.E.raw, dc⟩ else Ω q

def lowerSyncΚ (Κ : ClockEnv) (R : Realization) (dc : ClockId) : ClockEnv :=
  fun x => if x = R.e then some dc else Κ x

/-- The initial representation is typed at the encoder's `rep`. -/
def InitRep.WF (Θ : ConceptEnv) (i : InitRep) (rep : Ty) : Prop :=
  HasType Θ DeclEnv.empty Grant.none [] i.term rep

section Sync
variable {Θ : ConceptEnv} {Δ : DeclEnv} {Ω : OutputEnv} {β : DriveEnv} {Κ : ClockEnv}
  {R : Realization} {spec : OutputSpec} {i : InitRep} {dc : ClockId}

theorem syncBody_refs (accepts : Ty) {encode init : Expr} (he : encode.Pure) (hi : init.Pure) (c : ClockId) (d : DeclId) :
    (syncBody accepts encode c init d).refs = [d] := by
  cases accepts <;> simp [syncBody, Expr.refs, Expr.Pure.refs_nil he, Expr.Pure.refs_nil hi]

/-- No instantaneous reference: the transport reads strictly before. -/
theorem syncBody_instRefs (accepts : Ty) {encode init : Expr} (he : encode.Pure) (hi : init.Pure) (c : ClockId) (d : DeclId) :
    (syncBody accepts encode c init d).instRefs = [] := by
  cases accepts <;> simp [syncBody, Expr.instRefs, Expr.Pure.instRefs_nil he, Expr.Pure.instRefs_nil hi]

theorem lowerSyncΔ_other {x : DeclId} (hx : x ≠ R.e) : lowerSyncΔ Δ R spec i x = Δ x := Δ.update_other _ hx
theorem lowerSyncΔ_e :
    lowerSyncΔ Δ R spec i R.e = some ⟨R.e, ⟨R.E.raw, []⟩, some (syncBody spec.accepts R.E.encode spec.clock i.term R.d)⟩ :=
  Δ.update_self _
theorem lowerSyncΔ_tyView {x : DeclId} (hx : x ≠ R.e) : (lowerSyncΔ Δ R spec i).tyView x = Δ.tyView x := by
  simp [DeclEnv.tyView, lowerSyncΔ_other hx]
theorem lowerSyncΔ_tyView_e : (lowerSyncΔ Δ R spec i).tyView R.e = some R.E.raw := by
  simp [DeclEnv.tyView, lowerSyncΔ_e]
theorem lowerSyncΔ_realizationOf {x : DeclId} (hx : x ≠ R.e) :
    (lowerSyncΔ Δ R spec i).realizationOf x = Δ.realizationOf x := by
  simp [DeclEnv.realizationOf, lowerSyncΔ_other hx]
theorem lowerSyncΔ_realizationOf_e :
    (lowerSyncΔ Δ R spec i).realizationOf R.e = some (syncBody spec.accepts R.E.encode spec.clock i.term R.d) := by
  simp [DeclEnv.realizationOf, lowerSyncΔ_e]
theorem lowerSyncΩ_p : lowerSyncΩ Ω R dc R.p = some ⟨R.E.raw, dc⟩ := by simp [lowerSyncΩ]
theorem lowerSyncΩ_other {q : OutputId} (hq : q ≠ R.p) : lowerSyncΩ Ω R dc q = Ω q := by simp [lowerSyncΩ, hq]
theorem lowerSyncΚ_e : lowerSyncΚ Κ R dc R.e = some dc := by simp [lowerSyncΚ]
theorem lowerSyncΚ_other {x : DeclId} (hx : x ≠ R.e) : lowerSyncΚ Κ R dc x = Κ x := by simp [lowerSyncΚ, hx]

/-- **Behaviour unchanged**: same argument as Phase 14 — the environment is
    the original off `e`, and every pre-existing term evaluates alike. -/
theorem lowerSync_transparent {S : Sched} {I : Input} (nm : NoMention Δ R.e) (hI : ∀ d t, Avoids R.e (I d t))
    {c : ClockId} {t : Nat} {ρ : List Value} {ex : Expr} {v : Value}
    (he : R.e ∉ ex.refs) (hρ : ∀ w ∈ ρ, Avoids R.e w) :
    MEv S Δ I c t ρ ex v ↔ MEv S (lowerSyncΔ Δ R spec i) I c t ρ ex v := by
  constructor
  · intro h
    refine (simulate R.e ?_ ?_ h he hρ).1
    · intro x hx body hb; exact Or.inl ⟨by rw [lowerSyncΔ_realizationOf hx]; exact hb, nm x body hb⟩
    · intro x hx hn c t; exact ⟨.refInput (by rw [lowerSyncΔ_realizationOf hx]; exact hn), hI x t⟩
  · intro h
    refine (simulate R.e ?_ ?_ h he hρ).1
    · intro x hx body hb; rw [lowerSyncΔ_realizationOf hx] at hb; exact Or.inl ⟨hb, nm x body hb⟩
    · intro x hx hn c t; rw [lowerSyncΔ_realizationOf hx] at hn; exact ⟨.refInput hn, hI x t⟩

theorem lowerSync_decl_transparent {S : Sched} {I : Input} (nm : NoMention Δ R.e) (hI : ∀ d t, Avoids R.e (I d t))
    {x : DeclId} (hx : x ≠ R.e) {c : ClockId} {t : Nat} {v : Value} :
    MEv S Δ I c t [] (.declRef x) v ↔ MEv S (lowerSyncΔ Δ R spec i) I c t [] (.declRef x) v :=
  lowerSync_transparent nm hI (by simp [Expr.refs]; exact fun h => hx h.symm) (fun _ h => by simp at h)

theorem lowerSync_envRefines (wf : WF Θ Δ Ω β Κ R spec) : EnvRefines Δ (lowerSyncΔ Δ R spec i) := by
  intro x h hx
  have hxe : x ≠ R.e := by intro e; rw [e, wf.e_fresh] at hx; exact nomatch hx
  exact ⟨h, by rw [lowerSyncΔ_other hxe]; exact hx, DeclLeq.refl h⟩

theorem lowerSync_singleDriver (wf : WF Θ Δ Ω β Κ R spec) (hw : DriveWF Ω Κ Δ β) (hs : SingleDriver β) :
    DriveRefines β (lowerβ β R) ∧ SingleDriver (lowerβ β R) :=
  first_output_binding_is_monotone hs (wf.e_unbound hw) (wf.p_undriven hw)

/-- The new edge is well formed in the *device* domain; every old edge
    keeps its own. -/
theorem lowerSync_driveWF (wf : WF Θ Δ Ω β Κ R spec) (hw : DriveWF Ω Κ Δ β) :
    DriveWF (lowerSyncΩ Ω R dc) (lowerSyncΚ Κ R dc) (lowerSyncΔ Δ R spec i) (lowerβ β R) := by
  intro x o hb
  by_cases hx : x = R.e
  · subst hx; rw [lowerβ_e] at hb; cases hb
    exact ⟨⟨R.E.raw, dc⟩, lowerSyncΩ_p, lowerSyncΔ_tyView_e, lowerSyncΚ_e⟩
  · rw [lowerβ_other hx] at hb
    obtain ⟨sp, hΩ, hty, hck⟩ := hw x o hb
    exact ⟨sp, by rw [lowerSyncΩ_other (wf.o_ne_p' hΩ)]; exact hΩ, by rw [lowerSyncΔ_tyView hx]; exact hty,
      by rw [lowerSyncΚ_other hx]; exact hck⟩

/-- The encoder body is typed at `raw` under the empty grant: the transport
    carries data (`rep` is data), the initial value is typed at `rep`. -/
theorem syncBody_typed (wf : WF Θ Δ Ω β Κ R spec) (hi : i.WF Θ R.E.rep) :
    HasType Θ (lowerSyncΔ Δ R spec i) (Grant.of R.E.raw) []
      (syncBody spec.accepts R.E.encode spec.clock i.term R.d) R.E.raw := by
  have htr : HasType Θ (lowerSyncΔ Δ R spec i) (Grant.of R.E.raw) [] R.E.encode (.arr R.E.rep R.E.raw) :=
    (wf.enc_wf.refFree_env_irrelevant (Encoder.WF_refFree wf.enc_wf)).mono_grant (fun _ hf => hf.elim)
  have hinit : HasType Θ (lowerSyncΔ Δ R spec i) (Grant.of R.E.raw) [] i.term R.E.rep :=
    (hi.refFree_env_irrelevant (refFree_of_empty_typed hi)).mono_grant (fun _ hf => hf.elim)
  have hd : HasType Θ (lowerSyncΔ Δ R spec i) (Grant.of R.E.raw) [] (.declRef R.d) spec.accepts :=
    .declRef (by rw [lowerSyncΔ_tyView wf.d_ne_e]; exact wf.driver_ty)
  have hfit := wf.fits
  unfold EFits at hfit
  generalize hτ : spec.accepts = τ at *
  cases τ with
  | sem c =>
    simp only [syncBody]
    exact .app htr (.sync R.E.rep_data hinit (.rep hfit hd))
  | bool | nat | arr _ _ | q _ | opt _ | list _ | prod _ _ =>
    simp only at hfit
    rw [hfit] at hd
    simp only [syncBody]
    exact .app htr (.sync R.E.rep_data hinit hd)

theorem lowerSync_wf {ev : Evidence} (mono : ev.Monotone) (g : GlobalWF ev Θ Δ) (wf : WF Θ Δ Ω β Κ R spec)
    (hi : i.WF Θ R.E.rep) : GlobalWF ev Θ (lowerSyncΔ Δ R spec i) := by
  have er := lowerSync_envRefines (i := i) wf
  intro x h hx
  by_cases hxe : x = R.e
  · subst hxe
    rw [lowerSyncΔ_e] at hx
    rw [← Option.some.inj hx]
    refine ⟨rfl, fun b hb => ?_⟩
    simp only at hb
    rw [← Option.some.inj hb]
    exact ⟨syncBody_typed wf hi, fun _ hp => by simp at hp⟩
  · rw [lowerSyncΔ_other hxe] at hx
    exact ⟨g.stored_id hx, (g.wellFormed hx).of_envRefines mono er⟩

/-- **No new instantaneous edge**: the transport is never instantaneous, so
    the causal rank of the abstract design serves unchanged (with `e`
    anywhere). -/
theorem lowerSync_causal (hc : Causal Δ) : Causal (lowerSyncΔ Δ R spec i) := by
  obtain ⟨rank, Rk, hR, hedge⟩ := hc
  refine ⟨rank, Rk, hR, ?_⟩
  intro a b hab
  obtain ⟨body, hb, hmem⟩ := InstDependsOn.iff.mp hab
  by_cases hae : a = R.e
  · subst hae
    rw [lowerSyncΔ_realizationOf_e] at hb; cases hb
    rw [syncBody_instRefs _ R.E.encode_pure i.pure] at hmem
    simp at hmem
  · rw [lowerSyncΔ_realizationOf hae] at hb
    exact hedge a b (InstDependsOn.iff.mpr ⟨body, hb, hmem⟩)

/-- **Well clocked in the device domain**: the encoder and the initial
    value are clocked in `dc`, the transported operand in the output's
    clock `c` (its driver's), and no other realization mentions `e`. -/
theorem lowerSync_wellClocked (wf : WF Θ Δ Ω β Κ R spec) (nm : NoMention Δ R.e) (hw : WellClocked Κ Δ) :
    WellClocked (lowerSyncΚ Κ R dc) (lowerSyncΔ Δ R spec i) := by
  intro x body hb
  by_cases hxe : x = R.e
  · subst hxe
    rw [lowerSyncΔ_realizationOf_e] at hb; cases hb
    rw [lowerSyncΚ_e]
    have hd : lowerSyncΚ Κ R dc R.d = some spec.clock := by rw [lowerSyncΚ_other wf.d_ne_e]; exact wf.driver_clock
    unfold Clocked
    cases spec.accepts <;>
      simp [syncBody, clockedB, Expr.Pure.clocked (lowerSyncΚ Κ R dc) (some dc) R.E.encode_pure,
        Expr.Pure.clocked (lowerSyncΚ Κ R dc) (some dc) i.pure, hd]
  · rw [lowerSyncΔ_realizationOf hxe] at hb
    rw [lowerSyncΚ_other hxe]
    have := hw x body hb
    unfold Clocked at *
    rw [← clockedB_congr (Κ := Κ) (Κ' := lowerSyncΚ Κ R dc)]
    · exact this
    · intro y hy
      have hye : y ≠ R.e := fun e => nm x body hb (e ▸ hy)
      simp [lowerSyncΚ, hye]

/-! ## Correspondence: sampled strictly before -/

/-- The command a device-clocked realization delivers at global tick `t`:
    the transfer of the initial representation while the output's clock has
    not yet activated, and thereafter the command the output specified at
    the last activation of its clock strictly before `t`. -/
def SampledCommand (S : Sched) (Δ : DeclEnv) (I : Input) (Ω : OutputEnv) (β : DriveEnv) (R : Realization)
    (spec : OutputSpec) (i : InitRep) (t : Nat) (w : Value) : Prop :=
  (prevAct S spec.clock t = none ∧ w = R.E.transfer i.value) ∨
  (∃ t', prevAct S spec.clock t = some t' ∧ RawCommand S Δ I Ω β R t' w)

/-- **`lowerSync_correspondence`**: the device-clocked sink carries exactly
    the sampled command — the Phase-14 correspondence with the strictly-
    before rule of Phase 5 inside it.  Same hypotheses as Phase 14 plus the
    initial value typed at `rep`. -/
theorem lowerSync_correspondence {S : Sched} {I : Input} (wf : WF Θ Δ Ω β Κ R spec) (hw : DriveWF Ω Κ Δ β)
    (hs : SingleDriver β) (nm : NoMention Δ R.e) (hI : ∀ d t, Avoids R.e (I d t))
    (hty : OutputTyped S Δ I Ω β R spec) (hi : TyVal R.E.rep i.value) {t : Nat} {w : Value} :
    PhysicalOutput S (lowerSyncΔ Δ R spec i) I (lowerSyncΩ Ω R dc) (lowerβ β R) R.p t w ↔
      SampledCommand S Δ I Ω β R spec i t w := by
  have hinc : i.value.NoClo := TyVal.noClo R.E.rep_data hi
  constructor
  · rintro ⟨d', sp, hb, hΩ, he⟩
    have hd' : d' = R.e := by
      cases hne : decide (d' = R.e) with
      | true => exact of_decide_eq_true hne
      | false =>
        have hne' : d' ≠ R.e := of_decide_eq_false hne
        rw [lowerβ_other hne'] at hb
        exact (wf.p_undriven hw ⟨d', hb⟩).elim
    subst hd'
    rw [lowerSyncΩ_p] at hΩ; cases hΩ
    cases he with
    | refInput hn => rw [lowerSyncΔ_realizationOf_e] at hn; exact nomatch hn
    | refRealized hr hbody =>
      rw [lowerSyncΔ_realizationOf_e] at hr; cases hr
      -- the transported operand: `initRep` at `dc`, or the driver's representation at `c`, `t'`
      have key : ∀ (arg : Expr) (unwrap : Value → Value),
          (∀ u, MEv S (lowerSyncΔ Δ R spec i) I dc t [] (.sync spec.clock i.term arg) u →
            (prevAct S spec.clock t = none ∧ u = i.value) ∨
            (∃ t' v, prevAct S spec.clock t = some t' ∧ MEv S Δ I spec.clock t' [] (.declRef R.d) v ∧ u = unwrap v)) →
          MEv S (lowerSyncΔ Δ R spec i) I dc t [] (.app R.E.encode (.sync spec.clock i.term arg)) w →
          (∀ t v, PhysicalOutput S Δ I Ω β R.o t v → unwrap v = unwrapAt spec.accepts v) →
          SampledCommand S Δ I Ω β R spec i t w := by
        intro arg unwrap hinv happ hun
        -- extract the operand's value from the application
        have hu : ∃ u, MEv S (lowerSyncΔ Δ R spec i) I dc t [] (.sync spec.clock i.term arg) u ∧
            MEv S (lowerSyncΔ Δ R spec i) I dc t [] (.app R.E.encode (.sync spec.clock i.term arg)) w := by
          cases happ with
          | appClo hf ha hb => exact ⟨_, ha, .appClo hf ha hb⟩
          | appPrim hf ha => exact ⟨_, ha, .appPrim hf ha⟩
        obtain ⟨u, husync, _⟩ := hu
        rcases hinv u husync with ⟨hp, rfl⟩ | ⟨t', v, hp, hv, rfl⟩
        · left
          refine ⟨hp, ?_⟩
          have hcanon := (R.E.computes _ hi).mev R.E.encode_pure hinc husync
          exact happ.det hcanon
        · right
          have hpo : PhysicalOutput S Δ I Ω β R.o t' v := ⟨R.d, spec, wf.drives, wf.spec_of, hv⟩
          obtain ⟨w', hvw, hw'⟩ := hty t' v hpo
          have hun' := hun t' v hpo
          rw [hun', hvw, unwrapAt_wrapAt] at husync
          have hnc' : w'.NoClo := TyVal.noClo R.E.rep_data hw'
          have hcanon := (R.E.computes _ hw').mev R.E.encode_pure hnc' husync
          refine ⟨t', hp, spec, v, wf.spec_of, hpo, ?_⟩
          rw [happ.det hcanon, hvw, unwrapAt_wrapAt]
      generalize hτ : spec.accepts = τ at *
      cases τ with
      | sem c =>
        simp only [syncBody] at hbody
        refine key (.rep (.declRef R.d)) (unwrapAt (.sem c)) ?_ hbody (fun _ _ _ => rfl)
        intro u hu
        cases hu with
        | syncNone hp hiv =>
          left; exact ⟨hp, hiv.det (i.mev)⟩
        | syncSome hp hrep =>
          cases hrep with
          | rep hv =>
            right
            refine ⟨_, _, hp, (lowerSync_decl_transparent (spec := spec) (i := i) nm hI wf.d_ne_e).mpr hv, ?_⟩
            simp [unwrapAt]
      | bool | nat | arr _ _ | q _ | opt _ | list _ | prod _ _ =>
        all_goals
          simp only [syncBody] at hbody
          refine key (.declRef R.d) id ?_ hbody ?_
          · intro u hu
            cases hu with
            | syncNone hp hiv => left; exact ⟨hp, hiv.det (i.mev)⟩
            | syncSome hp hv =>
              right
              exact ⟨_, _, hp, (lowerSync_decl_transparent (spec := spec) (i := i) nm hI wf.d_ne_e).mpr hv, rfl⟩
          · intro _ v _; simp [unwrapAt]
  · intro hsc
    refine ⟨R.e, ⟨R.E.raw, dc⟩, lowerβ_e, lowerSyncΩ_p, .refRealized lowerSyncΔ_realizationOf_e ?_⟩
    rcases hsc with ⟨hp, rfl⟩ | ⟨t', hp, sp, v, hΩ, hpo, rfl⟩
    · -- before the first activation: the initial representation
      have hsync : ∀ arg, MEv S (lowerSyncΔ Δ R spec i) I dc t [] (.sync spec.clock i.term arg) i.value :=
        fun _ => .syncNone hp i.mev
      have hcanon := fun arg => (R.E.computes _ hi).mev R.E.encode_pure hinc (hsync arg)
      generalize hτ : spec.accepts = τ at *
      cases τ <;> simp only [syncBody] <;> exact hcanon _
    · rw [wf.spec_of] at hΩ; cases hΩ
      obtain ⟨d', sp', hb, hΩ', he⟩ := hpo
      have hd' : d' = R.d := hs d' R.d R.o hb wf.drives
      subst hd'
      rw [wf.spec_of] at hΩ'; cases hΩ'
      obtain ⟨w', hvw, hw'⟩ := hty t' v ⟨R.d, spec, wf.drives, wf.spec_of, he⟩
      have hv' := (lowerSync_decl_transparent (spec := spec) (i := i) nm hI wf.d_ne_e).mp he
      have hnc' : w'.NoClo := TyVal.noClo R.E.rep_data hw'
      rw [hvw, unwrapAt_wrapAt]
      generalize hτ : spec.accepts = τ at *
      cases τ with
      | sem c =>
        simp only [syncBody]
        rw [hvw] at hv'
        exact (R.E.computes _ hw').mev R.E.encode_pure hnc' (.syncSome hp (.rep hv'))
      | bool | nat | arr _ _ | q _ | opt _ | list _ | prod _ _ =>
        all_goals
          simp only [syncBody]
          simp only [wrapAt] at hvw
          rw [hvw] at hv'
          exact (R.E.computes _ hw').mev R.E.encode_pure hnc' (.syncSome hp hv')

end Sync

end BDL.DeviceClock
