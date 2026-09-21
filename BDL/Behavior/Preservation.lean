import BDL.Behavior.System

/-!
# Preservation — flattening a well-formed system yields a well-formed design

Theorems B–I of the behaviour-system milestone.  Every result is about the
*existing* kernel judgments applied to the flattened design; no second type
system, clock system, or causality notion is introduced for components.

Evidence assumptions (all three are properties of the validation layer, in
the spirit of `Evidence.Monotone` from Phase 1):

* `Evidence.Monotone`    — commitments survive environment refinement (Phase 1);
* `Evidence.Equivariant` — commitments survive renaming (component reuse);
* `Evidence.PortSound`   — a reference to a declaration inherits that
  declaration's public commitments, directly or through a transport (port
  binding).
-/

namespace BDL
open BDL.Output (OutputId OutputSpec OutputEnv DriveEnv DriveWF SingleDriver PartialOutputWF)
open BDL.Clock (ClockEnv Clocked WellClocked clockedB)

/-- Evidence that lets a port be bound by reference: whatever a declaration
    publicly commits to holds of a reference to it, and of a transport of
    it.  (`Experiments.compEv` of Phase 1 is of this kind.) -/
def Evidence.PortSound (ev : Evidence) : Prop :=
  ∀ (Δ : DeclEnv) (d : DeclId) (dh : DesignDecl) (p : PropertyId), Δ d = some dh → p ∈ dh.interface.commitments →
    ev Δ (.declRef d) p ∧ ∀ c i, ev Δ (.sync c i (.declRef d)) p

namespace BehaviorSystem

variable {ev : Evidence} {S : BehaviorSystem}

/-! ## Lookups in the union -/

theorem unionΔ_fresh (hW : 0 < S.W) {k : Nat} {I : Inst} (hI : S.instAt k = some I) {d : DeclId} (hd : d.n < S.W) :
    S.unionΔ (S.declOf k d) = (I.comp.design.Δ d).map (DesignDecl.rename (S.ren k I)) := by
  unfold unionΔ declOf
  simp only [decode_fresh hW hd, hI]

theorem unionΘ_fresh (hW : 0 < S.W) {k : Nat} {I : Inst} (hI : S.instAt k = some I) {s : ConceptId} (hs : s.n < S.W)
    (hi : I.comp.internalConcept s = true) :
    S.unionΘ ⟨fresh S.W k s.n⟩ = (I.comp.design.Θ s).map (Ty.rename (S.ren k I).s) := by
  unfold unionΘ
  simp only [decode_fresh hW hs, hI, hi, if_true]

theorem unionΘ_global {s : ConceptId} (hs : s.n < S.W) : S.unionΘ s = S.Θg s := by
  unfold unionΘ
  simp only [decode_global hs]

theorem unionΚ_fresh (hW : 0 < S.W) {k : Nat} {I : Inst} (hI : S.instAt k = some I) {d : DeclId} (hd : d.n < S.W) :
    S.unionΚ (S.declOf k d) = (I.comp.design.Κ d).map (S.ren k I).c := by
  unfold unionΚ declOf
  simp only [decode_fresh hW hd, hI]

theorem unionΩ_fresh (hW : 0 < S.W) {k : Nat} {I : Inst} (hI : S.instAt k = some I) {o : OutputId} (ho : o.n < S.W)
    (hi : I.comp.internalOut o = true) :
    S.unionΩ ⟨fresh S.W k o.n⟩ = (I.comp.design.Ω o).map (OutputSpec.rename (S.ren k I)) := by
  unfold unionΩ
  simp only [decode_fresh hW ho, hI, hi, if_true]

theorem unionΩ_global {o : OutputId} (ho : o.n < S.W) : S.unionΩ o = S.Ωg o := by
  unfold unionΩ
  simp only [decode_global ho]

theorem unionβ_fresh (hW : 0 < S.W) {k : Nat} {I : Inst} (hI : S.instAt k = some I) {d : DeclId} (hd : d.n < S.W) :
    S.unionβ (S.declOf k d) = (I.comp.design.β d).map (S.ren k I).o := by
  unfold unionβ declOf
  simp only [decode_fresh hW hd, hI]

/-- Every declaration of the union comes from exactly one instance. -/
theorem unionΔ_some {id : DeclId} {h' : DesignDecl} (h : S.unionΔ id = some h') :
    ∃ k I n h, S.instAt k = some I ∧ I.comp.design.Δ ⟨n⟩ = some h ∧ h' = h.rename (S.ren k I) ∧
      id = S.declOf k ⟨n⟩ ∧ n < S.W := by
  unfold unionΔ at h
  cases hdec : decode S.W id.n with
  | none => simp [hdec] at h
  | some kn =>
    obtain ⟨k, n⟩ := kn
    simp only [hdec] at h
    cases hI : S.instAt k with
    | none => simp [hI] at h
    | some I =>
      simp only [hI, Option.map_eq_some_iff] at h
      obtain ⟨hd, hΔ, rfl⟩ := h
      obtain ⟨hid, hn, _⟩ := decode_some hdec
      refine ⟨k, I, n, hd, hI, hΔ, rfl, ?_, hn⟩
      cases id; simp only at hid; simp [declOf, hid]

/-! ## Renaming agreements between a template and the union -/

theorem renamedBy_unionΔ (c : ComposeWF ev S) {k : Nat} {I : Inst} (hI : S.instAt k = some I) :
    DeclEnv.RenamedBy (S.ren k I) I.comp.design.Δ S.unionΔ := by
  intro d h hd
  obtain ⟨hr, hw, -⟩ := c.insts k I hI
  have hb : d.n < S.W := Nat.lt_of_lt_of_le (hr.declBound d h hd) hw
  show S.unionΔ (S.declOf k d) = _
  rw [unionΔ_fresh c.width hI hb, hd]; rfl

theorem renamedBy_unionΘ (c : ComposeWF ev S) {k : Nat} {I : Inst} (hI : S.instAt k = some I) :
    ConceptEnv.RenamedBy (S.ren k I).s I.comp.design.Θ S.unionΘ := by
  intro s R hs
  obtain ⟨hr, hw, -, hg, -⟩ := c.insts k I hI
  show S.unionΘ (if I.comp.internalConcept s then ⟨fresh S.W k s.n⟩ else s) = _
  cases hi : I.comp.internalConcept s with
  | true =>
    simp only [if_true]
    have hb : s.n < S.W := Nat.lt_of_lt_of_le (hr.conceptBound s R hs hi) hw
    rw [unionΘ_fresh c.width hI hb hi, hs]; rfl
  | false =>
    simp only [Bool.false_eq_true, if_false]
    obtain ⟨hb, hΘg⟩ := hg s R hs hi
    rw [unionΘ_global hb, hΘg]
    have hsf : R.SemFree := (hr.wf.concepts s R hs).1
    rw [Ty.rename_of_semFree _ _ hsf]

theorem renamedBy_unionΚ (c : ComposeWF ev S) {k : Nat} {I : Inst} (hI : S.instAt k = some I) :
    ClockEnv.RenamedBy (fun d => ∃ h, I.comp.design.Δ d = some h) (S.ren k I) I.comp.design.Κ S.unionΚ := by
  intro d hd
  obtain ⟨h, hh⟩ := hd
  obtain ⟨hr, hw, -⟩ := c.insts k I hI
  have hb : d.n < S.W := Nat.lt_of_lt_of_le (hr.declBound d h hh) hw
  show S.unionΚ (S.declOf k d) = _
  exact unionΚ_fresh c.width hI hb

/-! ## The union is well formed (Theorems B, E — instance level) -/

/-- **Every instance is well formed in the system** (the substantive form
    of "component validity does not depend on instance identity"): the
    union of the renamed instances is globally well formed. -/
theorem union_globalWF (c : ComposeWF ev S) (eq : ev.Equivariant) : GlobalWF ev S.unionΘ S.unionΔ := by
  intro id h' hh
  obtain ⟨k, I, n, h, hI, hΔ, rfl, rfl, hn⟩ := unionΔ_some hh
  obtain ⟨hr, -⟩ := c.insts k I hI
  have hid : h.id = ⟨n⟩ := hr.wf.global.stored_id hΔ
  refine ⟨?_, ?_⟩
  · simp [DesignDecl.rename, hid, ren, Ren.inst, declOf]
  · exact (hr.wf.global.wellFormed hΔ).rename eq (renamedBy_unionΘ c hI) (renamedBy_unionΔ c hI)

theorem unionΘ_WF (c : ComposeWF ev S) : S.unionΘ.WF := by
  intro s R hs
  unfold unionΘ at hs
  cases hdec : decode S.W s.n with
  | none =>
    simp only [hdec] at hs
    exact c.globalsWF s R hs
  | some kn =>
    obtain ⟨k, n⟩ := kn
    simp only [hdec] at hs
    cases hI : S.instAt k with
    | none => simp [hI] at hs
    | some I =>
      simp only [hI] at hs
      cases hi : I.comp.internalConcept ⟨n⟩ with
      | false => simp [hi] at hs
      | true =>
        simp only [hi, if_true, Option.map_eq_some_iff] at hs
        obtain ⟨R₀, hR₀, rfl⟩ := hs
        obtain ⟨hr, -⟩ := c.insts k I hI
        obtain ⟨hsf, hdata⟩ := hr.wf.concepts _ _ hR₀
        exact ⟨(Ty.rename_semFree _ _).mpr hsf, Ty.rename_data _ _ hdata⟩


/-! ## Ports in the union -/

theorem ren_d (k : Nat) (I : Inst) (d : DeclId) : (S.ren k I).d d = S.declOf k d := rfl

/-- A required port or parameter of an instance is an unresolved declaration
    of the union with the port's (renamed) interface. -/
theorem union_port (c : ComposeWF ev S) {k : Nat} {I : Inst} (hI : S.instAt k = some I) {p : Port}
    (hp : p ∈ I.comp.iface.required ++ I.comp.iface.params) :
    S.unionΔ (S.declOf k p.id) = some ⟨S.declOf k p.id, p.iface.rename (S.ren k I).s, none⟩ := by
  obtain ⟨hr, -⟩ := c.insts k I hI
  have hΔ : I.comp.design.Δ p.id = some ⟨p.id, p.iface, none⟩ := by
    rcases List.mem_append.mp hp with h | h
    · exact (hr.required p h).1
    · exact (hr.params p h).1
  rw [← ren_d, renamedBy_unionΔ c hI p.id _ hΔ]
  rfl

/-- A provided port of an instance is a declaration of the union with the
    port's (renamed) type and commitments. -/
theorem union_provided (c : ComposeWF ev S) {k : Nat} {I : Inst} (hI : S.instAt k = some I) {p : Port}
    (hp : p ∈ I.comp.iface.provided) :
    ∃ dh, S.unionΔ (S.declOf k p.id) = some dh ∧ dh.interface = p.iface.rename (S.ren k I).s := by
  obtain ⟨hr, -⟩ := c.insts k I hI
  obtain ⟨⟨h, hΔ, hif⟩, -⟩ := hr.provided p hp
  refine ⟨h.rename (S.ren k I), ?_, ?_⟩
  · rw [← ren_d]; exact renamedBy_unionΔ c hI p.id h hΔ
  · simp [DesignDecl.rename, hif]

theorem union_port_clock (c : ComposeWF ev S) {k : Nat} {I : Inst} (hI : S.instAt k = some I) {p : Port}
    (hp : p ∈ I.comp.iface.required ++ I.comp.iface.params ∨ p ∈ I.comp.iface.provided) :
    S.unionΚ (S.declOf k p.id) = p.clock.map (S.ren k I).c := by
  obtain ⟨hr, -⟩ := c.insts k I hI
  have hΔ : ∃ h, I.comp.design.Δ p.id = some h := by
    rcases hp with hp | hp
    · rcases List.mem_append.mp hp with h | h
      · exact ⟨_, (hr.required p h).1⟩
      · exact ⟨_, (hr.params p h).1⟩
    · obtain ⟨⟨h, hΔ, -⟩, -⟩ := hr.provided p hp; exact ⟨h, hΔ⟩
  have hK : I.comp.design.Κ p.id = p.clock := by
    rcases hp with hp | hp
    · rcases List.mem_append.mp hp with h | h
      · exact (hr.required p h).2
      · exact (hr.params p h).2.1
    · exact (hr.provided p hp).2
  rw [← ren_d, renamedBy_unionΚ c hI p.id hΔ, hK]


/-! ## Theorem C — a compatible binding is a satisfying realization -/

/-- The invariant carried through the binding fold: the current environment
    refines the union, agrees with it away from the destinations processed
    so far, realizes each processed destination with its binding body, and
    is globally well formed. -/
structure FoldInv (ev : Evidence) (S : BehaviorSystem) (done : List Binding) (Δ : DeclEnv) : Prop where
  er : EnvRefines S.unionΔ Δ
  untouched : ∀ id, (∀ b ∈ done, S.declOf b.dstInst b.dst ≠ id) → Δ id = S.unionΔ id
  bound : ∀ b ∈ done, ∃ Id pd, S.instAt b.dstInst = some Id ∧ pd ∈ Id.comp.iface.required ++ Id.comp.iface.params ∧
    pd.id = b.dst ∧
    Δ (S.declOf b.dstInst b.dst) = some ⟨S.declOf b.dstInst b.dst, pd.iface.rename (S.ren b.dstInst Id).s, some (S.bindingBody b)⟩
  wf : GlobalWF ev S.unionΘ Δ

/-- **Theorem C.**  In any environment refining the union, the body of a
    well-formed binding satisfies the destination port's interface. -/
theorem binding_satisfies (c : ComposeWF ev S) (ps : ev.PortSound) {Δ : DeclEnv} (er : EnvRefines S.unionΔ Δ)
    {b : Binding} (hb : BindingWF ev S b) :
    ∃ Id pd, S.instAt b.dstInst = some Id ∧ pd ∈ Id.comp.iface.required ++ Id.comp.iface.params ∧ pd.id = b.dst ∧
      Satisfies ev S.unionΘ Δ [] (S.bindingBody b) (pd.iface.rename (S.ren b.dstInst Id).s) := by
  obtain ⟨Id, hId, pd, hpd, hpid, hsrc⟩ := hb
  refine ⟨Id, pd, hId, hpd, hpid, ?_⟩
  cases hs : b.src with
  | const e =>
    rw [hs] at hsrc
    obtain ⟨-, hf, -, ht, hev⟩ := hsrc
    have hbody : S.bindingBody b = e := by simp [bindingBody, hs]
    rw [hbody]
    refine ⟨(ht.refFree_env_irrelevant hf).mono_grant (fun _ h => h.elim), fun p hp => hev p hp Δ⟩
  | port k id =>
    rw [hs] at hsrc
    obtain ⟨Is, hIs, psrc, hpsrc, rfl, hty, hcom, hclk⟩ := hsrc
    -- the source declaration in the union and in `Δ`
    obtain ⟨dh, hdh, hif⟩ := union_provided c hIs hpsrc
    obtain ⟨dh', hdh', le⟩ := er _ dh hdh
    have htv : Δ.tyView (S.declOf k psrc.id) = some (pd.iface.expectedType.rename (S.ren b.dstInst Id).s) := by
      rw [← hty]
      apply er.tyView
      simp [DeclEnv.tyView, hdh, hif, DeclInterface.rename]
    have hcom' : ∀ p ∈ pd.iface.commitments, p ∈ dh'.interface.commitments := by
      intro p hp
      apply le.interface_refines.commitments_subset
      rw [hif]; exact hcom hp
    cases ht : b.transport with
    | none =>
      have hbody : S.bindingBody b = .declRef (S.declOf k psrc.id) := by simp [bindingBody, hs, ht]
      rw [hbody]
      exact ⟨.declRef htv, fun p hp => (ps Δ _ dh' p hdh' (hcom' p hp)).1⟩
    | some init =>
      rw [ht] at hclk
      obtain ⟨-, -, hf, -, hti, hdata⟩ := hclk
      have hti' := (hti.refFree_env_irrelevant (Δ₂ := Δ) hf).mono_grant
        (G₂ := Grant.of (pd.iface.expectedType.rename (S.ren b.dstInst Id).s)) (fun _ h => h.elim)
      cases hK : S.unionΚ (S.declOf k psrc.id) with
      | none =>
        have hbody : S.bindingBody b = .declRef (S.declOf k psrc.id) := by simp [bindingBody, hs, ht, hK]
        rw [hbody]
        exact ⟨.declRef htv, fun p hp => (ps Δ _ dh' p hdh' (hcom' p hp)).1⟩
      | some cs =>
        have hbody : S.bindingBody b = .sync cs init (.declRef (S.declOf k psrc.id)) := by
          simp [bindingBody, hs, ht, hK]
        rw [hbody]
        exact ⟨.sync hdata hti' (.declRef htv), fun p hp => (ps Δ _ dh' p hdh' (hcom' p hp)).2 cs init⟩

/-- One binding step preserves the fold invariant. -/
theorem fold_step (c : ComposeWF ev S) (mono : ev.Monotone) (ps : ev.PortSound)
    {done : List Binding} {Δ : DeclEnv} (inv : FoldInv ev S done Δ) {b : Binding} (hb : BindingWF ev S b)
    (hnew : ∀ b' ∈ done, S.declOf b'.dstInst b'.dst ≠ S.declOf b.dstInst b.dst) :
    FoldInv ev S (done ++ [b]) (S.applyBinding Δ b) := by
  obtain ⟨Id, pd, hId, hpd, hpid, hsat⟩ := binding_satisfies c ps inv.er hb
  have hport : Δ (S.declOf b.dstInst b.dst) =
      some ⟨S.declOf b.dstInst b.dst, pd.iface.rename (S.ren b.dstInst Id).s, none⟩ := by
    rw [inv.untouched _ hnew, ← hpid]
    exact union_port c hId hpd
  have hstep : DeclRefines ev S.unionΘ Δ [] ⟨S.declOf b.dstInst b.dst, pd.iface.rename (S.ren b.dstInst Id).s, none⟩
      ⟨S.declOf b.dstInst b.dst, pd.iface.rename (S.ren b.dstInst Id).s, some (S.bindingBody b)⟩ := .realize hsat
  have happ : S.applyBinding Δ b =
      Δ.update ⟨S.declOf b.dstInst b.dst, pd.iface.rename (S.ren b.dstInst Id).s, some (S.bindingBody b)⟩ := by
    unfold applyBinding; rw [hport]
  rw [happ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact inv.er.trans (EnvRefines_update hport hstep.toLeq)
  · intro id hid
    have hne : id ≠ S.declOf b.dstInst b.dst :=
      fun h => hid b (List.mem_append_right _ (List.mem_singleton.mpr rfl)) (h ▸ rfl)
    rw [DeclEnv.update_other _ _ hne]
    exact inv.untouched id fun b' hb' => hid b' (List.mem_append_left _ hb')
  · intro b' hb'
    rcases List.mem_append.mp hb' with h | h
    · obtain ⟨Id', pd', hId', hpd', hpid', hΔ'⟩ := inv.bound b' h
      refine ⟨Id', pd', hId', hpd', hpid', ?_⟩
      rw [DeclEnv.update_other _ _ (hnew b' h), hΔ']
    · rw [List.mem_singleton.mp h]
      exact ⟨Id, pd, hId, hpd, hpid, DeclEnv.update_self _ _⟩
  · exact local_refinement_preserves_global_wf mono inv.wf hport hstep

theorem fold_inv (c : ComposeWF ev S) (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound) :
    ∀ (rest done : List Binding) (Δ : DeclEnv), S.bindings = done ++ rest → FoldInv ev S done Δ →
      FoldInv ev S (done ++ rest) (rest.foldl (S.applyBinding) Δ)
  | [], done, Δ, _, inv => by simpa using inv
  | b :: rest, done, Δ, hsplit, inv => by
    have hb : BindingWF ev S b := c.bindings b (by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_self))
    have hnew : ∀ b' ∈ done, S.declOf b'.dstInst b'.dst ≠ S.declOf b.dstInst b.dst := by
      intro b' hb' heq
      have hn := c.dstNodup
      rw [hsplit, List.map_append, List.map_cons, List.nodup_append] at hn
      exact hn.2.2 _ (List.mem_map_of_mem hb') _ (List.mem_cons.mpr (Or.inl rfl)) heq
    have inv' := fold_step c mono ps inv hb hnew
    have := fold_inv c mono eq ps rest (done ++ [b]) (S.applyBinding Δ b) (by rw [hsplit]; simp) inv'
    simpa [List.foldl_cons] using this

/-- The invariant at the end of the fold. -/
theorem flatten_inv (c : ComposeWF ev S) (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound) :
    FoldInv ev S S.bindings S.flattenΔ := by
  have := fold_inv c mono eq ps S.bindings [] S.unionΔ (by simp)
    ⟨EnvRefines.refl _, fun _ _ => rfl, fun _ h => by simp at h, union_globalWF c eq⟩
  simpa [flattenΔ] using this

/-- **Theorem D/E (typing and commitments).**  The flattened design is
    globally well formed: every instance's declarations and every binding
    satisfy their interfaces, in the flattened environment. -/
theorem flatten_globalWF (c : ComposeWF ev S) (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound) :
    GlobalWF ev S.flatten.Θ S.flatten.Δ :=
  (flatten_inv c mono eq ps).wf

theorem flatten_envRefines (c : ComposeWF ev S) (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound) :
    EnvRefines S.unionΔ S.flattenΔ :=
  (flatten_inv c mono eq ps).er


/-! ## Bodies in the flattened design -/

/-- Whether `d` is the destination of some binding is decidable. -/
instance (S : BehaviorSystem) (d : DeclId) : Decidable (∃ b ∈ S.bindings, S.declOf b.dstInst b.dst = d) :=
  inferInstanceAs (Decidable (∃ b, b ∈ S.bindings ∧ S.declOf b.dstInst b.dst = d))

/-- Every realized declaration of the flattened design is either a renamed
    template declaration (not a binding destination) or a bound port. -/
theorem flatten_body (c : ComposeWF ev S) (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound)
    {d : DeclId} {e : Expr} (hd : S.flattenΔ.realizationOf d = some e) :
    (∃ k I n h e₀, S.instAt k = some I ∧ I.comp.design.Δ ⟨n⟩ = some h ∧ h.realization = some e₀ ∧
        d = S.declOf k ⟨n⟩ ∧ n < S.W ∧ e = e₀.rename (S.ren k I) ∧
        ¬ ∃ b ∈ S.bindings, S.declOf b.dstInst b.dst = d) ∨
    (∃ b ∈ S.bindings, S.declOf b.dstInst b.dst = d ∧ e = S.bindingBody b ∧
        ∃ Id pd, S.instAt b.dstInst = some Id ∧ pd ∈ Id.comp.iface.required ++ Id.comp.iface.params ∧ pd.id = b.dst) := by
  have inv := flatten_inv c mono eq ps
  by_cases hb : ∃ b ∈ S.bindings, S.declOf b.dstInst b.dst = d
  · right
    obtain ⟨b, hbm, hbd⟩ := hb
    obtain ⟨Id, pd, hId, hpd, hpid, hΔ⟩ := inv.bound b hbm
    refine ⟨b, hbm, hbd, ?_, Id, pd, hId, hpd, hpid⟩
    rw [hbd] at hΔ
    simp only [DeclEnv.realizationOf, hΔ, Option.bind_some] at hd
    exact (Option.some.inj hd).symm
  · left
    have hu : S.flattenΔ d = S.unionΔ d := inv.untouched d (fun b hbm heq => hb ⟨b, hbm, heq⟩)
    simp only [DeclEnv.realizationOf, hu, Option.bind_eq_some_iff] at hd
    obtain ⟨h', hh', hre⟩ := hd
    obtain ⟨k, I, n, h, hI, hΔ, rfl, rfl, hn⟩ := unionΔ_some hh'
    simp only [DesignDecl.rename, Option.map_eq_some_iff] at hre
    obtain ⟨e₀, he₀, rfl⟩ := hre
    exact ⟨k, I, n, h, e₀, hI, hΔ, he₀, rfl, hn, rfl, hb⟩

/-- References of a template body are declared in the template, hence bounded. -/
theorem template_refs_bounded (c : ComposeWF ev S) {k : Nat} {I : Inst} (hI : S.instAt k = some I)
    {n : Nat} {h : DesignDecl} {e₀ : Expr} (hΔ : I.comp.design.Δ ⟨n⟩ = some h) (he : h.realization = some e₀) :
    ∀ x ∈ e₀.refs, (∃ h', I.comp.design.Δ x = some h') ∧ x.n < S.W := by
  obtain ⟨hr, hw, -⟩ := c.insts k I hI
  intro x hx
  have ht := ((hr.wf.global.wellFormed hΔ) e₀ he).1
  obtain ⟨τ, hτ⟩ := ht.refs_declared x hx
  simp only [DeclEnv.tyView, Option.map_eq_some_iff] at hτ
  obtain ⟨h', hh', -⟩ := hτ
  exact ⟨⟨h', hh'⟩, Nat.lt_of_lt_of_le (hr.declBound x h' hh') hw⟩

/-! ## Theorem G — clock validity of the flattened design -/

theorem flatten_wellClocked (c : ComposeWF ev S) (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound) :
    WellClocked S.flatten.Κ S.flatten.Δ := by
  intro d e hd
  rcases flatten_body c mono eq ps hd with
    ⟨k, I, n, h, e₀, hI, hΔ, he₀, rfl, hn, rfl, -⟩ | ⟨b, hbm, rfl, rfl, Id, pd, hId, hpd, hpid⟩
  · -- a renamed template body
    obtain ⟨hr, -⟩ := c.insts k I hI
    have hcl : Clocked I.comp.design.Κ (I.comp.design.Κ ⟨n⟩) e₀ :=
      hr.wf.clocked ⟨n⟩ e₀ (by simp [DeclEnv.realizationOf, hΔ, he₀])
    have := hcl.rename (renamedBy_unionΚ c hI) (fun x hx => (template_refs_bounded c hI hΔ he₀ x hx).1)
    show Clocked S.unionΚ (S.unionΚ (S.declOf k ⟨n⟩)) _
    rw [unionΚ_fresh c.width hI hn]
    exact this
  · -- a bound port
    obtain ⟨Id', hId', pd', hpd', hpid', hsrc⟩ := c.bindings b hbm
    rw [hId] at hId'; cases hId'
    have hKd : S.unionΚ (S.declOf b.dstInst pd'.id) = pd'.clock.map (S.ren b.dstInst Id).c :=
      union_port_clock c hId (Or.inl hpd')
    show Clocked S.unionΚ (S.unionΚ (S.declOf b.dstInst b.dst)) (S.bindingBody b)
    rw [← hpid', hKd]
    cases hs : b.src with
    | const e =>
      rw [hs] at hsrc
      obtain ⟨-, hf, hdf, -⟩ := hsrc
      have hbody : S.bindingBody b = e := by simp [bindingBody, hs]
      rw [hbody]
      exact Clock.clockedB_of_closed e hf hdf _
    | port k id =>
      rw [hs] at hsrc
      obtain ⟨Is, hIs, psrc, hpsrc, rfl, -, -, hclk⟩ := hsrc
      have hKs : S.unionΚ (S.declOf k psrc.id) = psrc.clock.map (S.ren k Is).c :=
        union_port_clock c hIs (Or.inr hpsrc)
      cases ht : b.transport with
      | none =>
        rw [ht] at hclk
        have hbody : S.bindingBody b = .declRef (S.declOf k psrc.id) := by simp [bindingBody, hs, ht]
        rw [hbody]
        show clockedB _ _ _ = true
        simp only [clockedB, decide_eq_true_eq, hKs]
        exact hclk
      | some init =>
        rw [ht] at hclk
        obtain ⟨⟨cd, hcd⟩, ⟨cs, hcs⟩, hf, hdf, -, -⟩ := hclk
        have hKs' : S.unionΚ (S.declOf k psrc.id) = some ((S.ren k Is).c cs) := by rw [hKs, hcs]; rfl
        have hbody : S.bindingBody b = .sync ((S.ren k Is).c cs) init (.declRef (S.declOf k psrc.id)) := by
          simp [bindingBody, hs, ht, hKs']
        rw [hbody, hcd]
        show clockedB _ _ _ = true
        simp only [clockedB, Option.map_some, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨Clock.clockedB_of_closed init hf hdf _, Or.inr hKs'⟩


/-! ## Theorem F — causality under an acyclic inter-instance graph -/

theorem Expr.instRefs_subset_refs : ∀ (e : Expr) (b : DeclId), b ∈ e.instRefs → b ∈ e.refs
  | .var _, _, h | .boolLit _, _, h | .natLit _, _, h | .prim _, _, h => h
  | .declRef _, _, h => h
  | .lam _ b, x, h => Expr.instRefs_subset_refs b x h
  | .app f a, x, h => by
    simp only [Expr.instRefs, Expr.refs, List.mem_append] at h ⊢
    exact h.elim (fun h => Or.inl (Expr.instRefs_subset_refs f x h)) (fun h => Or.inr (Expr.instRefs_subset_refs a x h))
  | .rep e, x, h => Expr.instRefs_subset_refs e x h
  | .mk _ e, x, h => Expr.instRefs_subset_refs e x h
  | .delay i _, x, h => by
    simp only [Expr.instRefs] at h
    simp only [Expr.refs, List.mem_append]
    exact Or.inl (Expr.instRefs_subset_refs i x h)
  | .sync _ i _, x, h => by
    simp only [Expr.instRefs] at h
    simp only [Expr.refs, List.mem_append]
    exact Or.inl (Expr.instRefs_subset_refs i x h)
  | .fold f z l, x, h => by
    simp only [Expr.instRefs, Expr.refs, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl (Expr.instRefs_subset_refs f x h))
    · exact Or.inl (Or.inr (Expr.instRefs_subset_refs z x h))
    · exact Or.inr (Expr.instRefs_subset_refs l x h)

/-- A family of rank witnesses, one per instance, from the causality of each
    template (constructive: by recursion on the instance list). -/
theorem ranks_of_list : ∀ (l : List Inst), (∀ I ∈ l, Causal I.comp.design.Δ) →
    ∃ (ranks : Nat → DeclId → Nat) (R : Nat), ∀ k I, l[k]? = some I →
      (∀ d, ranks k d < R) ∧ ∀ a b, InstDependsOn I.comp.design.Δ a b → ranks k b < ranks k a
  | [], _ => ⟨fun _ _ => 0, 1, fun k I h => by simp at h⟩
  | I :: l, hc => by
    obtain ⟨r₀, R₀, hR₀, hr₀⟩ := hc I (List.mem_cons_self)
    obtain ⟨ranks, R, hranks⟩ := ranks_of_list l (fun J hJ => hc J (List.mem_cons_of_mem _ hJ))
    refine ⟨fun k => if k = 0 then r₀ else ranks (k - 1), max R₀ R, ?_⟩
    intro k J hJ
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hJ
      subst hJ
      simp only [if_true]
      exact ⟨fun d => Nat.lt_of_lt_of_le (hR₀ d) (Nat.le_max_left _ _), hr₀⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hJ
      obtain ⟨h1, h2⟩ := hranks k J hJ
      simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      exact ⟨fun d => Nat.lt_of_lt_of_le (h1 d) (Nat.le_max_right _ _), h2⟩

/-- Ports are declared in their template, hence bounded by the width. -/
theorem port_bounded (c : ComposeWF ev S) {k : Nat} {I : Inst} (hI : S.instAt k = some I) {p : Port}
    (hp : p ∈ I.comp.iface.required ++ I.comp.iface.params ∨ p ∈ I.comp.iface.provided) : p.id.n < S.W := by
  obtain ⟨hr, hw, -⟩ := c.insts k I hI
  refine Nat.lt_of_lt_of_le ?_ hw
  rcases hp with hp | hp
  · rcases List.mem_append.mp hp with h | h
    · exact hr.declBound _ _ (hr.required p h).1
    · exact hr.declBound _ _ (hr.params p h).1
  · obtain ⟨⟨h, hΔ, -⟩, -⟩ := hr.provided p hp
    exact hr.declBound _ _ hΔ

/-- **Theorem F.**  Each instance internally causal and the inter-instance
    instantaneous graph acyclic ⇒ the flattened design is causal.  The
    condition is necessary: `Experiments.feedback_composition_not_causal`. -/
theorem flatten_causal (c : ComposeWF ev S) (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound)
    (hacyc : InstAcyclic S) : Causal S.flatten.Δ := by
  obtain ⟨irank, Ri, hRi, hdep⟩ := hacyc
  have hcaus : ∀ I ∈ S.insts, Causal I.comp.design.Δ := by
    intro I hI
    obtain ⟨k, hk⟩ := List.getElem_of_mem hI
    exact (c.insts k I (List.getElem?_eq_some_iff.mpr hk)).1.wf.causal
  obtain ⟨ranks, R, hranks⟩ := ranks_of_list S.insts hcaus
  -- the flattened rank: instance rank in the high digit, template rank in the low digit
  let rank' : DeclId → Nat := fun d =>
    match decode S.W d.n with
    | some (k, n) => match S.instAt k with
      | some _ => R * irank k + ranks k ⟨n⟩
      | none => 0
    | none => 0
  have hrank_fresh : ∀ k I (x : DeclId), S.instAt k = some I → x.n < S.W →
      rank' (S.declOf k x) = R * irank k + ranks k x := by
    intro k I x hI hx
    show (match decode S.W (fresh S.W k x.n) with
      | some (k, n) => match S.instAt k with
        | some _ => R * irank k + ranks k ⟨n⟩
        | none => 0
      | none => 0) = _
    rw [decode_fresh c.width hx]
    simp only [hI]
  have hbound : ∀ d, rank' d < R * Ri + 1 := by
    intro d
    show (match decode S.W d.n with
      | some (k, n) => match S.instAt k with
        | some _ => R * irank k + ranks k ⟨n⟩
        | none => 0
      | none => 0) < R * Ri + 1
    cases hdec : decode S.W d.n with
    | none => dsimp only; omega
    | some kn =>
      obtain ⟨k, n⟩ := kn
      dsimp only
      cases hI : S.instAt k with
      | none => dsimp only; omega
      | some I =>
        show R * irank k + ranks k ⟨n⟩ < R * Ri + 1
        have h1 := (hranks k I hI).1 ⟨n⟩
        have h2 : R * (irank k + 1) ≤ R * Ri := Nat.mul_le_mul_left R (hRi k)
        rw [Nat.mul_succ] at h2
        omega
  refine ⟨rank', R * Ri + 1, hbound, ?_⟩
  intro a b hab
  obtain ⟨e, he, hb⟩ := InstDependsOn.iff.mp hab
  rcases flatten_body c mono eq ps he with
    ⟨k, I, n, h, e₀, hI, hΔ, he₀, rfl, hn, rfl, -⟩ | ⟨b', hbm, rfl, rfl, Id, pd, hId, hpd, hpid⟩
  · -- an edge inside one instance
    rw [Expr.rename_instRefs, List.mem_map] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    have hxb := template_refs_bounded c hI hΔ he₀ x (Expr.instRefs_subset_refs e₀ x hx)
    have hlocal : InstDependsOn I.comp.design.Δ ⟨n⟩ x :=
      InstDependsOn.iff.mpr ⟨e₀, by simp [DeclEnv.realizationOf, hΔ, he₀], hx⟩
    have := (hranks k I hI).2 ⟨n⟩ x hlocal
    rw [ren_d, hrank_fresh k I x hI hxb.2, hrank_fresh k I ⟨n⟩ hI hn]
    omega
  · -- an edge created by a binding
    obtain ⟨Id', hId', pd', hpd', hpid', hsrc⟩ := c.bindings b' hbm
    rw [hId] at hId'; cases hId'
    have hdb : pd'.id.n < S.W := port_bounded c hId (Or.inl hpd')
    cases hs : b'.src with
    | const e =>
      rw [hs] at hsrc
      obtain ⟨-, hf, -⟩ := hsrc
      have hbody : S.bindingBody b' = e := by simp [bindingBody, hs]
      rw [hbody] at hb
      have := Expr.instRefs_subset_refs e b hb
      rw [hf] at this
      exact absurd this (by simp)
    | port ks id =>
      rw [hs] at hsrc
      obtain ⟨Is, hIs, psrc, hpsrc, rfl, -, -, hclk⟩ := hsrc
      have hsb : psrc.id.n < S.W := port_bounded c hIs (Or.inr hpsrc)
      cases ht : b'.transport with
      | none =>
        have hbody : S.bindingBody b' = .declRef (S.declOf ks psrc.id) := by simp [bindingBody, hs, ht]
        rw [hbody] at hb
        simp only [Expr.instRefs, List.mem_singleton] at hb
        subst hb
        have hinst : InstDep S b'.dstInst ks := ⟨b', hbm, rfl, ht, psrc.id, hs⟩
        have hlt := hdep _ _ hinst
        rw [← hpid', hrank_fresh ks Is psrc.id hIs hsb, hrank_fresh b'.dstInst Id pd'.id hId hdb]
        have h1 := (hranks ks Is hIs).1 psrc.id
        have h2 : R * (irank ks + 1) ≤ R * irank b'.dstInst := Nat.mul_le_mul_left R hlt
        rw [Nat.mul_succ] at h2
        omega
      | some init =>
        rw [ht] at hclk
        obtain ⟨-, ⟨cs, hcs⟩, hf, -⟩ := hclk
        have hKs : S.unionΚ (S.declOf ks psrc.id) = some ((S.ren ks Is).c cs) := by
          rw [union_port_clock c hIs (Or.inr hpsrc), hcs]; rfl
        have hbody : S.bindingBody b' = .sync ((S.ren ks Is).c cs) init (.declRef (S.declOf ks psrc.id)) := by
          simp [bindingBody, hs, ht, hKs]
        rw [hbody] at hb
        simp only [Expr.instRefs] at hb
        have := Expr.instRefs_subset_refs init b hb
        rw [hf] at this
        exact absurd this (by simp)


/-! ## Theorem I — physical outputs after flattening -/

/-- Every drive edge of the union comes from one instance. -/
theorem unionβ_some {d : DeclId} {o' : OutputId} (h : S.unionβ d = some o') :
    ∃ k I n o, S.instAt k = some I ∧ I.comp.design.β ⟨n⟩ = some o ∧ o' = (S.ren k I).o o ∧
      d = S.declOf k ⟨n⟩ ∧ n < S.W := by
  unfold unionβ at h
  cases hdec : decode S.W d.n with
  | none => simp [hdec] at h
  | some kn =>
    obtain ⟨k, n⟩ := kn
    simp only [hdec] at h
    cases hI : S.instAt k with
    | none => simp [hI] at h
    | some I =>
      simp only [hI, Option.map_eq_some_iff] at h
      obtain ⟨o, hβ, rfl⟩ := h
      obtain ⟨hid, hn, _⟩ := decode_some hdec
      refine ⟨k, I, n, o, hI, hβ, rfl, ?_, hn⟩
      cases d; simp only at hid; simp [declOf, hid]

/-- The sink an instance drives exists in the union, with the renamed spec. -/
theorem unionΩ_of_drive (c : ComposeWF ev S) {k : Nat} {I : Inst} (hI : S.instAt k = some I)
    {o : OutputId} {spec : OutputSpec} (hΩ : I.comp.design.Ω o = some spec) :
    S.unionΩ ((S.ren k I).o o) = some (OutputSpec.rename (S.ren k I) spec) := by
  obtain ⟨hr, hw, -, -, hext⟩ := c.insts k I hI
  show S.unionΩ (if I.comp.internalOut o then ⟨fresh S.W k o.n⟩ else o) = _
  cases hi : I.comp.internalOut o with
  | true =>
    simp only [if_true]
    have hb : o.n < S.W := Nat.lt_of_lt_of_le (hr.outBound o spec hΩ hi) hw
    rw [unionΩ_fresh c.width hI hb hi, hΩ]; rfl
  | false =>
    simp only [Bool.false_eq_true, if_false]
    obtain ⟨hb, hΩg⟩ := hext o spec hΩ hi
    rw [unionΩ_global hb, hΩg]

theorem flatten_driveWF (c : ComposeWF ev S) (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound) :
    DriveWF S.flatten.Ω S.flatten.Κ S.flatten.Δ S.flatten.β := by
  intro d o' hβ
  obtain ⟨k, I, n, o, hI, hβ₀, rfl, rfl, hn⟩ := unionβ_some hβ
  obtain ⟨hr, -⟩ := c.insts k I hI
  obtain ⟨spec, hΩ, htv, hK⟩ := hr.wf.drives ⟨n⟩ o hβ₀
  refine ⟨OutputSpec.rename (S.ren k I) spec, unionΩ_of_drive c hI hΩ, ?_, ?_⟩
  · show S.flattenΔ.tyView (S.declOf k ⟨n⟩) = some (spec.accepts.rename (S.ren k I).s)
    apply (flatten_envRefines c mono eq ps).tyView
    rw [← ren_d]
    exact (renamedBy_unionΔ c hI).tyView htv
  · show S.unionΚ (S.declOf k ⟨n⟩) = some ((S.ren k I).c spec.clock)
    rw [unionΚ_fresh c.width hI hn, hK]; rfl

/-- **Theorem I.**  Single-driver holds for the flattened design: internal
    sinks are fresh per instance, external sinks are covered by
    `ExternalSingleDriver`.  The kernel predicate is applied unchanged. -/
theorem flatten_singleDriver (c : ComposeWF ev S) : SingleDriver S.flatten.β := by
  intro d₁ d₂ o h₁ h₂
  obtain ⟨k₁, I₁, n₁, o₁, hI₁, hβ₁, rfl, rfl, hn₁⟩ := unionβ_some h₁
  obtain ⟨k₂, I₂, n₂, o₂, hI₂, hβ₂, ho, rfl, hn₂⟩ := unionβ_some h₂
  obtain ⟨hr₁, hw₁, -, -, hext₁⟩ := c.insts k₁ I₁ hI₁
  obtain ⟨hr₂, hw₂, -, -, hext₂⟩ := c.insts k₂ I₂ hI₂
  obtain ⟨spec₁, hΩ₁, -⟩ := hr₁.wf.drives ⟨n₁⟩ o₁ hβ₁
  obtain ⟨spec₂, hΩ₂, -⟩ := hr₂.wf.drives ⟨n₂⟩ o₂ hβ₂
  cases hi₁ : I₁.comp.internalOut o₁ with
  | true =>
    have hb₁ : o₁.n < S.W := Nat.lt_of_lt_of_le (hr₁.outBound o₁ spec₁ hΩ₁ hi₁) hw₁
    cases hi₂ : I₂.comp.internalOut o₂ with
    | true =>
      have hb₂ : o₂.n < S.W := Nat.lt_of_lt_of_le (hr₂.outBound o₂ spec₂ hΩ₂ hi₂) hw₂
      obtain ⟨rfl, rfl⟩ := inst_out_disjoint c.width hi₁ hi₂ hb₁ hb₂ ho
      rw [hI₁] at hI₂; cases hI₂
      have := hr₁.wf.single ⟨n₁⟩ ⟨n₂⟩ o₁ hβ₁ hβ₂
      rw [this]
    | false =>
      obtain ⟨hb₂, -⟩ := hext₂ o₂ spec₂ hΩ₂ hi₂
      have : (S.ren k₂ I₂).o o₂ = o₂ := by simp [ren, Ren.inst, hi₂]
      rw [this] at ho
      exact absurd ho (inst_out_not_global c.width hi₁ hb₂)
  | false =>
    obtain ⟨hb₁, -⟩ := hext₁ o₁ spec₁ hΩ₁ hi₁
    have e₁ : (S.ren k₁ I₁).o o₁ = o₁ := by simp [ren, Ren.inst, hi₁]
    cases hi₂ : I₂.comp.internalOut o₂ with
    | true =>
      rw [e₁] at ho
      exact absurd ho.symm (inst_out_not_global c.width hi₂ hb₁)
    | false =>
      have e₂ : (S.ren k₂ I₂).o o₂ = o₂ := by simp [ren, Ren.inst, hi₂]
      rw [e₁, e₂] at ho
      subst ho
      obtain ⟨rfl, hd⟩ := c.external k₁ I₁ ⟨n₁⟩ k₂ I₂ ⟨n₂⟩ o₁ hI₁ hI₂ hβ₁ hi₁ hβ₂ hi₂
      rw [hd]

/-! ## Theorem D — the flattened design is well formed -/

/-- **Theorem D.**  A structurally well-formed system with an acyclic
    inter-instance graph flattens to a structurally well-formed design, for
    every evidence relation that is monotone, equivariant, and port-sound. -/
theorem flatten_WF (c : ComposeWF ev S) (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound)
    (hacyc : InstAcyclic S) : S.flatten.WF ev where
  global := flatten_globalWF c mono eq ps
  concepts := unionΘ_WF c
  clocked := flatten_wellClocked c mono eq ps
  causal := flatten_causal c mono eq ps hacyc
  drives := flatten_driveWF c mono eq ps
  single := flatten_singleDriver c

/-- Partial-output well-formedness (Phase 6) of the flattened design. -/
theorem flatten_partialOutputWF (c : ComposeWF ev S) (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound) :
    PartialOutputWF S.flatten.Ω S.flatten.Κ S.flatten.Δ S.flatten.β :=
  ⟨flatten_driveWF c mono eq ps, flatten_singleDriver c⟩

/-! ## Theorem H — unresolved external ports remain open, not invalid -/

/-- **Theorem H.**  A required port or parameter that no binding targets is
    an unresolved declaration of the flattened design — an ordinary open
    declaration, not an error.  Its well-formedness needs nothing. -/
theorem open_port_stays_open (c : ComposeWF ev S) (mono : ev.Monotone) (eq : ev.Equivariant) (ps : ev.PortSound)
    {d : DeclId} (ho : OpenPorts S d) : S.flatten.Open d := by
  obtain ⟨⟨k, I, p, hI, hp, rfl⟩, hnb⟩ := ho
  have inv := flatten_inv c mono eq ps
  refine ⟨⟨S.declOf k p.id, p.iface.rename (S.ren k I).s, none⟩, ?_, rfl⟩
  show S.flattenΔ (S.declOf k p.id) = _
  rw [inv.untouched _ hnb]
  exact union_port c hI hp

end BehaviorSystem
end BDL
