import BDL.Surface.Assignment
import BDL.Surface.Buffer
import BDL.Validation.Capacity

/-!
# Phase 17 — Occurrence-preserving realization: the output window

Phase 15's device-clock lowering (`lowerSync`) samples: at a device
activation the sink carries the command specified at the last activation
of the output's clock strictly before.  For a *state-like* output that is
the meaning.  For an output whose every value is an occurrence a device
must not miss — a command the design issues at each of two output ticks
between two device activations — sampling collapses `[A], [B]` to `[B]`.
This module builds the occurrence-preserving crossing from what exists:
Phase 14's encoder declaration `e` in the output's clock is the *source*
of Phase 9a's five-declaration window, transported by `sync` into the
device domain `dc`, and the machine sink `p` accepts `list raw` in `dc`
and is driven by `window`:

    e      @c  := encode (rep d)                     (Phase 14)
    log    @c  := cons e (delay nil log)
    logD   @dc := sync c nil log
    seen   @dc := length logD
    cursor @dc := delay 0 seen
    window @dc := reverse (take (seen − cursor) logD) -> p : list raw @dc

Nothing enters the kernel.  What is proved: the behaviour is literally
unchanged off the fresh identities (`lowerWindow_transparent`); at every
device tick the sink carries exactly the raw commands specified at the
output-clock activations since the device's previous activation, in order
and with multiplicity (`lowerWindow_correspondence`, Theorem M through
Phase 14's correspondence); the batch is bounded by the Phase-9a capacity
obligation (`lowerWindow_bounded`); the lowered design refines the
abstract one and is drive-well-formed, single-driver, well clocked and
causal (`lowerWindow_envRefines`, `lowerWindow_driveWF`,
`lowerWindow_singleDriver`, `lowerWindow_wellClocked`,
`lowerWindow_causal`).  The **state / occurrence distinction** is the
sink's type: a device that consumes `raw` is lowered by `lowerSync`
(latest value), one that consumes `list raw` by `lowerWindow` (every
value); the output itself is one value stream in both cases and no flag is
added to it.

At the adapter, a batch is the list of the operations of its items
(`batchOps`) and the line after it the last accepted item
(`lineAfterBatch`) — `List Op`, no new primitive.  Two window realizations
of one output on two sinks carry batches that are pointwise the two
transfers of one value list (`paired_batches_of_one_window`): the
prepare/prepare/commit of a paired axis is the backend's order within one
batch.
-/

set_option linter.unusedSimpArgs false

namespace BDL.OutputWindow
open BDL BDL.Reactive BDL.Clock BDL.Output BDL.Provision BDL.OutputRealization BDL.Adapter BDL.Buffer
open BDL.Validation.Capacity

/-! ## A fresh realized declaration is invisible -/

/-- Updating an environment at an identity no realization mentions changes
    the evaluation of no term that avoids it — the single step behind every
    lowering's transparency, over `simulate`. -/
theorem update_transparent {S : Sched} {Δ : DeclEnv} {I : Input} {h : DesignDecl}
    (nm : NoMention Δ h.id) (hI : ∀ d t, Avoids h.id (I d t))
    {c : ClockId} {t : Nat} {ρ : List Value} {ex : Expr} {v : Value}
    (he : h.id ∉ ex.refs) (hρ : ∀ w ∈ ρ, Avoids h.id w) :
    MEv S Δ I c t ρ ex v ↔ MEv S (Δ.update h) I c t ρ ex v := by
  have hro : ∀ x, x ≠ h.id → (Δ.update h).realizationOf x = Δ.realizationOf x := by
    intro x hx; simp [DeclEnv.realizationOf, Δ.update_other h hx]
  constructor
  · intro hev
    refine (simulate h.id ?_ ?_ hev he hρ).1
    · intro x hx body hb; exact Or.inl ⟨by rw [hro x hx]; exact hb, nm x body hb⟩
    · intro x hx hn c t; exact ⟨.refInput (by rw [hro x hx]; exact hn), hI x t⟩
  · intro hev
    refine (simulate h.id ?_ ?_ hev he hρ).1
    · intro x hx body hb; rw [hro x hx] at hb; exact Or.inl ⟨hb, nm x body hb⟩
    · intro x hx hn c t; rw [hro x hx] at hn; exact ⟨.refInput hn, hI x t⟩

/-- `NoMention` survives an update whose body avoids the identity. -/
theorem NoMention.update {Δ : DeclEnv} {r : DeclId} (nm : NoMention Δ r) {h : DesignDecl}
    (hb : ∀ body, h.realization = some body → r ∉ body.refs) : NoMention (Δ.update h) r := by
  intro x body hx
  by_cases hxh : x = h.id
  · subst hxh
    simp [DeclEnv.realizationOf, Δ.update_self h] at hx
    exact hb body hx
  · simp [DeclEnv.realizationOf, Δ.update_other h hxh] at hx
    exact nm x body hx

/-! ## The construction -/

/-- The fresh identities of the window: the log in the output's clock; the
    transported log, the seen count, the cursor and the window in the
    device domain. -/
structure WIds where
  log : DeclId
  logD : DeclId
  seen : DeclId
  cursor : DeclId
  window : DeclId

def WIds.list (ids : WIds) : List DeclId := [ids.log, ids.logD, ids.seen, ids.cursor, ids.window]
/-- Phase 9a's identities with the encoder declaration as the source. -/
def WIds.bids (ids : WIds) (e : DeclId) : Buffer.Ids := ⟨e, ids.log, ids.logD, ids.seen, ids.cursor, ids.window⟩

def lowerWindowΔ (Δ : DeclEnv) (R : Realization) (spec : OutputSpec) (ids : WIds) : DeclEnv :=
  (((((lowerΔ Δ R spec).update (logDecl R.E.raw (ids.bids R.e))).update
    (logDDecl R.E.raw spec.clock (ids.bids R.e))).update (seenDecl R.E.raw (ids.bids R.e))).update
    (cursorDecl (ids.bids R.e))).update (windowDecl R.E.raw (ids.bids R.e))

/-- The sink accepts the batch type in the device domain. -/
def lowerWindowΩ (Ω : OutputEnv) (R : Realization) (dc : ClockId) : OutputEnv :=
  fun q => if q = R.p then some ⟨.list R.E.raw, dc⟩ else Ω q

/-- The window drives the sink; the encoder declaration drives nothing. -/
def lowerWindowβ (β : DriveEnv) (R : Realization) (ids : WIds) : DriveEnv := β.bind ids.window R.p

def lowerWindowΚ (Κ : ClockEnv) (R : Realization) (spec : OutputSpec) (dc : ClockId) (ids : WIds) : ClockEnv :=
  fun x => if x = R.e ∨ x = ids.log then some spec.clock
    else if x = ids.logD ∨ x = ids.seen ∨ x = ids.cursor ∨ x = ids.window then some dc else Κ x

/-- The identities are fresh and pairwise distinct. -/
structure Fresh (Δ : DeclEnv) (R : Realization) (ids : WIds) : Prop where
  nodup : (R.e :: ids.list).Nodup
  fresh : ∀ x ∈ ids.list, Δ x = none

section Lookup
variable {Δ : DeclEnv} {R : Realization} {spec : OutputSpec} {ids : WIds}

theorem Fresh.distinct (h : Fresh Δ R ids) :
    R.e ≠ ids.log ∧ R.e ≠ ids.logD ∧ R.e ≠ ids.seen ∧ R.e ≠ ids.cursor ∧ R.e ≠ ids.window ∧
    ids.log ≠ ids.logD ∧ ids.log ≠ ids.seen ∧ ids.log ≠ ids.cursor ∧ ids.log ≠ ids.window ∧
    ids.logD ≠ ids.seen ∧ ids.logD ≠ ids.cursor ∧ ids.logD ≠ ids.window ∧
    ids.seen ≠ ids.cursor ∧ ids.seen ≠ ids.window ∧ ids.cursor ≠ ids.window := by
  have := h.nodup
  simp only [WIds.list, List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at this
  exact ⟨this.1.1, this.1.2.1, this.1.2.2.1, this.1.2.2.2.1, this.1.2.2.2.2, this.2.1.1, this.2.1.2.1,
    this.2.1.2.2.1, this.2.1.2.2.2, this.2.2.1.1, this.2.2.1.2.1, this.2.2.1.2.2, this.2.2.2.1.1,
    this.2.2.2.1.2, this.2.2.2.2⟩

/-- A declaration of the abstract design is none of the fresh identities. -/
theorem Fresh.not_fresh (h : Fresh Δ R ids) {x : DeclId} (hx : Δ x ≠ none) : x ∉ ids.list :=
  fun hm => hx (h.fresh x hm)

theorem lowerWindowΔ_other {x : DeclId} (hx : x ∉ ids.list) : lowerWindowΔ Δ R spec ids x = lowerΔ Δ R spec x := by
  simp only [WIds.list, List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true] at hx
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  simp [lowerWindowΔ, DeclEnv.update, windowDecl, cursorDecl, seenDecl, logDDecl, logDecl, WIds.bids, h1, h2, h3, h4, h5]

theorem lowerWindowΔ_log (h : Fresh Δ R ids) :
    lowerWindowΔ Δ R spec ids ids.log = some (logDecl R.E.raw (ids.bids R.e)) := by
  obtain ⟨_, _, _, _, _, h6, h7, h8, h9, _⟩ := h.distinct
  simp [lowerWindowΔ, DeclEnv.update, windowDecl, cursorDecl, seenDecl, logDDecl, logDecl, WIds.bids, h6, h7, h8, h9]

theorem lowerWindowΔ_logD (h : Fresh Δ R ids) :
    lowerWindowΔ Δ R spec ids ids.logD = some (logDDecl R.E.raw spec.clock (ids.bids R.e)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, h10, h11, h12, _⟩ := h.distinct
  simp [lowerWindowΔ, DeclEnv.update, windowDecl, cursorDecl, seenDecl, logDDecl, logDecl, WIds.bids, h10, h11, h12]

theorem lowerWindowΔ_seen (h : Fresh Δ R ids) :
    lowerWindowΔ Δ R spec ids ids.seen = some (seenDecl R.E.raw (ids.bids R.e)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h13, h14, _⟩ := h.distinct
  simp [lowerWindowΔ, DeclEnv.update, windowDecl, cursorDecl, seenDecl, logDDecl, logDecl, WIds.bids, h13, h14]

theorem lowerWindowΔ_cursor (h : Fresh Δ R ids) :
    lowerWindowΔ Δ R spec ids ids.cursor = some (cursorDecl (ids.bids R.e)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h15⟩ := h.distinct
  simp [lowerWindowΔ, DeclEnv.update, windowDecl, cursorDecl, seenDecl, logDDecl, logDecl, WIds.bids, h15]

theorem lowerWindowΔ_window :
    lowerWindowΔ Δ R spec ids ids.window = some (windowDecl R.E.raw (ids.bids R.e)) := by
  simp [lowerWindowΔ, DeclEnv.update, windowDecl, WIds.bids]

theorem lowerWindowΔ_e (h : Fresh Δ R ids) :
    lowerWindowΔ Δ R spec ids R.e = some ⟨R.e, ⟨R.E.raw, []⟩, some (encoderBody spec.accepts R.E.encode R.d)⟩ := by
  have hx : R.e ∉ ids.list := by
    have := h.nodup; simp only [List.nodup_cons] at this; exact this.1
  rw [lowerWindowΔ_other hx, lowerΔ_e]

theorem lowerWindowΔ_realizationOf_e (h : Fresh Δ R ids) :
    (lowerWindowΔ Δ R spec ids).realizationOf R.e = some (encoderBody spec.accepts R.E.encode R.d) := by
  simp [DeclEnv.realizationOf, lowerWindowΔ_e h]

theorem lowerWindowΔ_tyView_e (h : Fresh Δ R ids) : (lowerWindowΔ Δ R spec ids).tyView R.e = some R.E.raw := by
  simp [DeclEnv.tyView, lowerWindowΔ_e h]

theorem lowerWindowΔ_realizationOf_other {x : DeclId} (hx : x ∉ ids.list) (hxe : x ≠ R.e) :
    (lowerWindowΔ Δ R spec ids).realizationOf x = Δ.realizationOf x := by
  rw [DeclEnv.realizationOf, lowerWindowΔ_other hx, behavior_unchanged hxe]; rfl

theorem lowerWindowΔ_tyView_other {x : DeclId} (hx : x ∉ ids.list) (hxe : x ≠ R.e) :
    (lowerWindowΔ Δ R spec ids).tyView x = Δ.tyView x := by
  rw [DeclEnv.tyView, lowerWindowΔ_other hx, behavior_unchanged hxe]; rfl

/-- The five declarations are realized as Phase 9a elaborates them. -/
theorem lowerWindow_realizedFrom (h : Fresh Δ R ids) :
    RealizedFrom R.E.raw spec.clock (ids.bids R.e) (lowerWindowΔ Δ R spec ids) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [DeclEnv.realizationOf, WIds.bids, lowerWindowΔ_log h, lowerWindowΔ_logD h, lowerWindowΔ_seen h,
      lowerWindowΔ_cursor h, lowerWindowΔ_window, logDecl, logDDecl, seenDecl, cursorDecl, windowDecl]

theorem lowerWindowΩ_p {Ω : OutputEnv} {dc : ClockId} : lowerWindowΩ Ω R dc R.p = some ⟨.list R.E.raw, dc⟩ := by
  simp [lowerWindowΩ]
theorem lowerWindowΩ_other {Ω : OutputEnv} {dc : ClockId} {q : OutputId} (hq : q ≠ R.p) :
    lowerWindowΩ Ω R dc q = Ω q := by simp [lowerWindowΩ, hq]
theorem lowerWindowβ_window {β : DriveEnv} : lowerWindowβ β R ids ids.window = some R.p := by
  simp [lowerWindowβ, DriveEnv.bind]
theorem lowerWindowβ_other {β : DriveEnv} {x : DeclId} (hx : x ≠ ids.window) : lowerWindowβ β R ids x = β x := by
  simp [lowerWindowβ, DriveEnv.bind, hx]

end Lookup

/-! ## Transparency -/

section Transparency
variable {Θ : ConceptEnv} {Δ : DeclEnv} {Ω : OutputEnv} {β : DriveEnv} {Κ : ClockEnv} {S : Sched} {I : Input}
  {R : Realization} {spec : OutputSpec} {ids : WIds}

/-- Every identity the abstract design mentions is a declaration of it. -/
theorem NoMention.of_fresh (nm : ∀ x, Δ x = none → NoMention Δ x) (h : Fresh Δ R ids) (wf : WF Θ Δ Ω β Κ R spec) :
    ∀ x ∈ R.e :: ids.list, NoMention Δ x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact nm _ wf.e_fresh
  · exact nm _ (h.fresh x hx)

/-- **`lowerWindow_transparent`**: every term that mentions none of the six
    fresh identities evaluates alike before and after — six applications
    of `update_transparent`, one per declaration added. -/
theorem lowerWindow_transparent (h : Fresh Δ R ids) (wf : WF Θ Δ Ω β Κ R spec)
    (nm : ∀ x ∈ R.e :: ids.list, NoMention Δ x) (hI : ∀ x ∈ R.e :: ids.list, ∀ d t, Avoids x (I d t))
    {c : ClockId} {t : Nat} {ρ : List Value} {ex : Expr} {v : Value}
    (he : ∀ x ∈ R.e :: ids.list, x ∉ ex.refs) (hρ : ∀ x ∈ R.e :: ids.list, ∀ w ∈ ρ, Avoids x w) :
    MEv S Δ I c t ρ ex v ↔ MEv S (lowerWindowΔ Δ R spec ids) I c t ρ ex v := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h.distinct
  have hs1 := h1.symm; have hs2 := h2.symm; have hs3 := h3.symm; have hs4 := h4.symm; have hs5 := h5.symm
  have hs6 := h6.symm; have hs7 := h7.symm; have hs8 := h8.symm; have hs9 := h9.symm; have hs10 := h10.symm
  have hs11 := h11.symm; have hs12 := h12.symm; have hs13 := h13.symm; have hs14 := h14.symm; have hs15 := h15.symm
  have hd : R.d ∉ ids.list := h.not_fresh (by
    intro e; have := wf.driver_ty; simp [DeclEnv.tyView, e] at this)
  simp only [WIds.list, List.mem_cons, List.mem_singleton, List.not_mem_nil, not_or, or_false] at hd
  have me : R.e ∈ R.e :: ids.list := List.mem_cons_self
  have ml : ids.log ∈ R.e :: ids.list := by simp [WIds.list]
  have mlD : ids.logD ∈ R.e :: ids.list := by simp [WIds.list]
  have ms : ids.seen ∈ R.e :: ids.list := by simp [WIds.list]
  have mc : ids.cursor ∈ R.e :: ids.list := by simp [WIds.list]
  have mw : ids.window ∈ R.e :: ids.list := by simp [WIds.list]
  -- the encoder: Phase 14
  have s0 := lower_transparent (S := S) (I := I) (spec := spec) (nm _ me) (hI _ me) (he _ me) (hρ _ me)
    (c := c) (t := t) (ρ := ρ) (ex := ex) (v := v)
  -- no realization of the growing environment mentions the next identity
  have nmL : NoMention (lowerΔ Δ R spec) ids.log := by
    intro x body hb
    by_cases hx : x = R.e
    · subst hx; rw [lowerΔ_realizationOf_e] at hb; cases hb
      rw [encoderBody_refs _ R.E.encode_pure]; simp; exact fun e => hd.1 e.symm
    · rw [lowerΔ_realizationOf hx] at hb; exact nm _ ml x body hb
  have nmLD : NoMention ((lowerΔ Δ R spec).update (logDecl R.E.raw (ids.bids R.e))) ids.logD := by
    refine NoMention.update ?_ ?_
    · intro x body hb
      by_cases hx : x = R.e
      · subst hx; rw [lowerΔ_realizationOf_e] at hb; cases hb
        rw [encoderBody_refs _ R.E.encode_pure]; simp; exact fun e => hd.2.1 e.symm
      · rw [lowerΔ_realizationOf hx] at hb; exact nm _ mlD x body hb
    · intro body hb; simp [logDecl] at hb; subst hb
      simp [logBody, consE, nilE, Expr.refs, WIds.bids, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15]
  have nmS : NoMention (((lowerΔ Δ R spec).update (logDecl R.E.raw (ids.bids R.e))).update
      (logDDecl R.E.raw spec.clock (ids.bids R.e))) ids.seen := by
    refine NoMention.update (NoMention.update ?_ ?_) ?_
    · intro x body hb
      by_cases hx : x = R.e
      · subst hx; rw [lowerΔ_realizationOf_e] at hb; cases hb
        rw [encoderBody_refs _ R.E.encode_pure]; simp; exact fun e => hd.2.2.1 e.symm
      · rw [lowerΔ_realizationOf hx] at hb; exact nm _ ms x body hb
    · intro body hb; simp [logDecl] at hb; subst hb
      simp [logBody, consE, nilE, Expr.refs, WIds.bids, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15]
    · intro body hb; simp [logDDecl] at hb; subst hb
      simp [logDBody, nilE, Expr.refs, WIds.bids, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15]
  have nmC : NoMention ((((lowerΔ Δ R spec).update (logDecl R.E.raw (ids.bids R.e))).update
      (logDDecl R.E.raw spec.clock (ids.bids R.e))).update (seenDecl R.E.raw (ids.bids R.e))) ids.cursor := by
    refine NoMention.update (NoMention.update (NoMention.update ?_ ?_) ?_) ?_
    · intro x body hb
      by_cases hx : x = R.e
      · subst hx; rw [lowerΔ_realizationOf_e] at hb; cases hb
        rw [encoderBody_refs _ R.E.encode_pure]; simp; exact fun e => hd.2.2.2.1 e.symm
      · rw [lowerΔ_realizationOf hx] at hb; exact nm _ mc x body hb
    · intro body hb; simp [logDecl] at hb; subst hb
      simp [logBody, consE, nilE, Expr.refs, WIds.bids, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15]
    · intro body hb; simp [logDDecl] at hb; subst hb
      simp [logDBody, nilE, Expr.refs, WIds.bids, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15]
    · intro body hb; simp [seenDecl] at hb; subst hb
      simp [seenBody, lenE, Expr.refs, WIds.bids, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15]
  have nmW : NoMention (((((lowerΔ Δ R spec).update (logDecl R.E.raw (ids.bids R.e))).update
      (logDDecl R.E.raw spec.clock (ids.bids R.e))).update (seenDecl R.E.raw (ids.bids R.e))).update
      (cursorDecl (ids.bids R.e))) ids.window := by
    refine NoMention.update (NoMention.update (NoMention.update (NoMention.update ?_ ?_) ?_) ?_) ?_
    · intro x body hb
      by_cases hx : x = R.e
      · subst hx; rw [lowerΔ_realizationOf_e] at hb; cases hb
        rw [encoderBody_refs _ R.E.encode_pure]; simp; exact fun e => hd.2.2.2.2 e.symm
      · rw [lowerΔ_realizationOf hx] at hb; exact nm _ mw x body hb
    · intro body hb; simp [logDecl] at hb; subst hb
      simp [logBody, consE, nilE, Expr.refs, WIds.bids, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15]
    · intro body hb; simp [logDDecl] at hb; subst hb
      simp [logDBody, nilE, Expr.refs, WIds.bids, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15]
    · intro body hb; simp [seenDecl] at hb; subst hb
      simp [seenBody, lenE, Expr.refs, WIds.bids, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15]
    · intro body hb; simp [cursorDecl] at hb; subst hb
      simp [cursorBody, zeroE, Expr.refs, WIds.bids, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15]
  rw [s0, update_transparent (h := logDecl R.E.raw (ids.bids R.e)) nmL (hI _ ml) (he _ ml) (hρ _ ml),
    update_transparent (h := logDDecl R.E.raw spec.clock (ids.bids R.e)) nmLD (hI _ mlD) (he _ mlD) (hρ _ mlD),
    update_transparent (h := seenDecl R.E.raw (ids.bids R.e)) nmS (hI _ ms) (he _ ms) (hρ _ ms),
    update_transparent (h := cursorDecl (ids.bids R.e)) nmC (hI _ mc) (he _ mc) (hρ _ mc),
    update_transparent (h := windowDecl R.E.raw (ids.bids R.e)) nmW (hI _ mw) (he _ mw) (hρ _ mw)]
  rfl

/-- Every declaration of the abstract design is observed identically. -/
theorem lowerWindow_decl_transparent (h : Fresh Δ R ids) (wf : WF Θ Δ Ω β Κ R spec)
    (nm : ∀ x ∈ R.e :: ids.list, NoMention Δ x) (hI : ∀ x ∈ R.e :: ids.list, ∀ d t, Avoids x (I d t))
    {x : DeclId} (hx : Δ x ≠ none) {c : ClockId} {t : Nat} {v : Value} :
    MEv S Δ I c t [] (.declRef x) v ↔ MEv S (lowerWindowΔ Δ R spec ids) I c t [] (.declRef x) v := by
  refine lowerWindow_transparent h wf nm hI ?_ (fun _ _ _ hw => by simp at hw)
  intro y hy
  simp only [Expr.refs, List.mem_singleton]
  intro e; subst e
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hx wf.e_fresh
  · exact hx (h.fresh _ hy)

end Transparency

/-! ## Correspondence -/

section Correspondence
variable {Θ : ConceptEnv} {Δ : DeclEnv} {Ω : OutputEnv} {β : DriveEnv} {Κ : ClockEnv} {S : Sched} {I : Input}
  {R : Realization} {spec : OutputSpec} {ids : WIds} {dc : ClockId}

/-- The encoder declaration's value from the driver's value, in any
    environment (Phase 14's `encoder_value`, freed from `lowerΔ`). -/
theorem encoder_value_in {Δ' : DeclEnv} (_wf : WF Θ Δ Ω β Κ R spec) {t : Nat} {w : Value} (hw : TyVal R.E.rep w)
    (hd : MEv S Δ' I spec.clock t [] (.declRef R.d) (wrapAt spec.accepts w)) :
    MEv S Δ' I spec.clock t [] (encoderBody spec.accepts R.E.encode R.d) (R.E.transfer w) := by
  have hnc : w.NoClo := TyVal.noClo R.E.rep_data hw
  generalize hτ : spec.accepts = τ at *
  cases τ with
  | sem c => exact (R.E.computes w hw).mev R.E.encode_pure hnc (.rep hd)
  | bool | nat | arr _ _ | q _ | opt _ | list _ | prod _ _ => exact (R.E.computes w hw).mev R.E.encode_pure hnc hd

/-- **A representation trace** of the logical output: `f u` is the typed
    representation the output carries at global tick `u` (wrapped at a
    semantic output).  Unique under `SingleDriver`
    (`single_driver_output_deterministic`); its existence in a causal,
    globally well-formed design is Phase 5's totality. -/
def RepTrace (S : Sched) (Δ : DeclEnv) (I : Input) (Ω : OutputEnv) (β : DriveEnv) (R : Realization)
    (spec : OutputSpec) (f : Nat → Value) : Prop :=
  ∀ u, TyVal R.E.rep (f u) ∧ PhysicalOutput S Δ I Ω β R.o u (wrapAt spec.accepts (f u))

/-- Each point of the trace is a raw command of Phase 14's specification. -/
theorem RepTrace.rawCommand (wf : WF Θ Δ Ω β Κ R spec) {f : Nat → Value} (hf : RepTrace S Δ I Ω β R spec f) (u : Nat) :
    RawCommand S Δ I Ω β R u (R.E.transfer (f u)) :=
  ⟨spec, wrapAt spec.accepts (f u), wf.spec_of, (hf u).2, by rw [unwrapAt_wrapAt]⟩

/-- The encoder declaration, in the window design, carries the transfer of
    the trace at every tick of the output's clock. -/
theorem lowerWindow_encoder_at (h : Fresh Δ R ids) (wf : WF Θ Δ Ω β Κ R spec) (hs : SingleDriver β)
    (nm : ∀ x ∈ R.e :: ids.list, NoMention Δ x) (hI : ∀ x ∈ R.e :: ids.list, ∀ d t, Avoids x (I d t))
    {f : Nat → Value} (hf : RepTrace S Δ I Ω β R spec f) (u : Nat) :
    MEv S (lowerWindowΔ Δ R spec ids) I spec.clock u [] (.declRef R.e) (R.E.transfer (f u)) := by
  obtain ⟨d', sp', hb, hΩ, he⟩ := (hf u).2
  have hd' : d' = R.d := hs d' R.d R.o hb wf.drives
  subst hd'
  rw [wf.spec_of] at hΩ; cases hΩ
  have hd : Δ R.d ≠ none := by
    intro e; have := wf.driver_ty; rw [DeclEnv.tyView, e] at this; exact nomatch this
  have he' := (lowerWindow_decl_transparent (ids := ids) h wf nm hI hd).mp he
  exact .refRealized (lowerWindowΔ_realizationOf_e h) (encoder_value_in wf (hf u).1 he')

/-- **`lowerWindow_correspondence`** (Theorem M through Phase 14): at every
    global tick `t`, in the device domain, the machine sink carries the
    list of the raw commands specified at the output-clock activations
    since the device's previous activation — in order and with
    multiplicity. -/
theorem lowerWindow_correspondence (h : Fresh Δ R ids) (wf : WF Θ Δ Ω β Κ R spec) (hs : SingleDriver β)
    (nm : ∀ x ∈ R.e :: ids.list, NoMention Δ x) (hI : ∀ x ∈ R.e :: ids.list, ∀ d t, Avoids x (I d t))
    {f : Nat → Value} (hf : RepTrace S Δ I Ω β R spec f) (t : Nat) :
    PhysicalOutput S (lowerWindowΔ Δ R spec ids) I (lowerWindowΩ Ω R dc) (lowerWindowβ β R ids) R.p t
      (.list ((windowTicks S spec.clock dc t).map (R.E.transfer ∘ f))) :=
  ⟨ids.window, ⟨.list R.E.raw, dc⟩, lowerWindowβ_window, lowerWindowΩ_p,
    buffer_window_correspondence_from (lowerWindow_realizedFrom h)
      (lowerWindow_encoder_at h wf hs nm hI hf) dc t⟩

/-- The batch, pointwise: it has one entry per window activation, and its
    `i`-th entry is the raw command Phase 14 specifies at the `i`-th
    activation. -/
theorem lowerWindow_batch_rawCommands (wf : WF Θ Δ Ω β Κ R spec) {f : Nat → Value}
    (hf : RepTrace S Δ I Ω β R spec f) (t : Nat) :
    ((windowTicks S spec.clock dc t).map (R.E.transfer ∘ f)).length = (windowTicks S spec.clock dc t).length ∧
    ∀ i (hi : i < (windowTicks S spec.clock dc t).length),
      RawCommand S Δ I Ω β R (windowTicks S spec.clock dc t)[i]
        (((windowTicks S spec.clock dc t).map (R.E.transfer ∘ f))[i]'(by simpa using hi)) := by
  refine ⟨List.length_map .., fun i hi => ?_⟩
  rw [List.getElem_map]
  exact hf.rawCommand wf _

/-- The sink is single-driver, so the batch is *the* value the sink carries. -/
theorem lowerWindow_batch_unique (h : Fresh Δ R ids) (wf : WF Θ Δ Ω β Κ R spec) (hw : DriveWF Ω Κ Δ β)
    (hs : SingleDriver β) (nm : ∀ x ∈ R.e :: ids.list, NoMention Δ x)
    (hI : ∀ x ∈ R.e :: ids.list, ∀ d t, Avoids x (I d t)) {f : Nat → Value} (hf : RepTrace S Δ I Ω β R spec f)
    {t : Nat} {w : Value}
    (hp : PhysicalOutput S (lowerWindowΔ Δ R spec ids) I (lowerWindowΩ Ω R dc) (lowerWindowβ β R ids) R.p t w) :
    w = .list ((windowTicks S spec.clock dc t).map (R.E.transfer ∘ f)) :=
  single_driver_output_deterministic (lowerWindow_singleDriver_aux h wf hw hs) hp (lowerWindow_correspondence h wf hs nm hI hf t)
where
  lowerWindow_singleDriver_aux (h : Fresh Δ R ids) (wf : WF Θ Δ Ω β Κ R spec) (hw : DriveWF Ω Κ Δ β)
      (hs : SingleDriver β) : SingleDriver (lowerWindowβ β R ids) := by
    have hwin : β ids.window = none := by
      cases hb : β ids.window with
      | none => rfl
      | some o =>
        obtain ⟨_, _, hty, _⟩ := hw _ _ hb
        have := h.fresh ids.window (by simp [WIds.list])
        rw [DeclEnv.tyView, this] at hty; exact nomatch hty
    exact (first_output_binding_is_monotone hs hwin (wf.p_undriven hw)).2

/-! ### Multiplicity, order, capacity -/

/-- **Order and multiplicity**: the batch is indexed by the window ticks in
    strictly increasing order, and for every property of a command the
    number of batch entries with it equals the number of window
    activations whose command has it — Phase 9a's theorems, at the sink. -/
theorem lowerWindow_order_multiplicity {f : Nat → Value} (t : Nat) (p : Value → Bool) :
    (windowTicks S spec.clock dc t).Pairwise (· < ·) ∧
    (((windowTicks S spec.clock dc t).map (R.E.transfer ∘ f)).filter p).length =
      ((windowTicks S spec.clock dc t).filter (p ∘ (R.E.transfer ∘ f))).length :=
  ⟨windowTicks_sorted S spec.clock dc t, by rw [List.filter_map, List.length_map]⟩

/-- **`lowerWindow_bounded`**: under Phase 9a's capacity obligation for the
    crossing `spec.clock → dc`, every batch up to the horizon has at most
    `cap` commands.  Capacity is a validation judgment on the schedules,
    never a type. -/
theorem lowerWindow_bounded {f : Nat → Value} {cap T : Nat} (hc : CapacitySufficient S spec.clock dc cap T)
    {t : Nat} (ht : t ≤ T) :
    ((windowTicks S spec.clock dc t).map (R.E.transfer ∘ f)).length ≤ cap := by
  rw [List.length_map]; exact hc t ht

end Correspondence

/-! ## Structure: refinement, drive edges, clocks, causality, typing -/

section Structure
variable {Θ : ConceptEnv} {Δ : DeclEnv} {Ω : OutputEnv} {β : DriveEnv} {Κ : ClockEnv}
  {R : Realization} {spec : OutputSpec} {ids : WIds} {dc : ClockId}

/-- A pre-existing declaration is not one of the fresh identities and is
    not the encoder. -/
theorem Fresh.old (h : Fresh Δ R ids) (wf : WF Θ Δ Ω β Κ R spec) {x : DeclId} {hx : DesignDecl}
    (hxs : Δ x = some hx) : x ∉ ids.list ∧ x ≠ R.e :=
  ⟨h.not_fresh (fun e => by rw [hxs] at e; exact nomatch e), fun e => by rw [e, wf.e_fresh] at hxs; exact nomatch hxs⟩

/-- **`lowerWindow_envRefines`**: six declarations are added; every
    pre-existing one is unchanged. -/
theorem lowerWindow_envRefines (h : Fresh Δ R ids) (wf : WF Θ Δ Ω β Κ R spec) :
    EnvRefines Δ (lowerWindowΔ Δ R spec ids) := by
  intro x hx hxs
  obtain ⟨h1, h2⟩ := h.old wf hxs
  exact ⟨hx, by rw [lowerWindowΔ_other h1, behavior_unchanged h2]; exact hxs, DeclLeq.refl hx⟩

theorem Fresh.window_unbound (h : Fresh Δ R ids) (hw : DriveWF Ω Κ Δ β) : β ids.window = none := by
  cases hb : β ids.window with
  | none => rfl
  | some o =>
    obtain ⟨_, _, hty, _⟩ := hw _ _ hb
    have := h.fresh ids.window (by simp [WIds.list])
    rw [DeclEnv.tyView, this] at hty; exact nomatch hty

/-- **`lowerWindow_singleDriver`**: binding the window to the fresh sink is
    Phase 6's first binding. -/
theorem lowerWindow_singleDriver (h : Fresh Δ R ids) (wf : WF Θ Δ Ω β Κ R spec) (hw : DriveWF Ω Κ Δ β)
    (hs : SingleDriver β) : DriveRefines β (lowerWindowβ β R ids) ∧ SingleDriver (lowerWindowβ β R ids) :=
  first_output_binding_is_monotone hs (h.window_unbound hw) (wf.p_undriven hw)

theorem lowerWindowΔ_tyView_window :
    (lowerWindowΔ Δ R spec ids).tyView ids.window = some (.list R.E.raw) := by
  simp [DeclEnv.tyView, lowerWindowΔ_window, windowDecl]
theorem lowerWindowΔ_tyView_log (h : Fresh Δ R ids) :
    (lowerWindowΔ Δ R spec ids).tyView ids.log = some (.list R.E.raw) := by
  simp [DeclEnv.tyView, lowerWindowΔ_log h, logDecl]
theorem lowerWindowΔ_tyView_logD (h : Fresh Δ R ids) :
    (lowerWindowΔ Δ R spec ids).tyView ids.logD = some (.list R.E.raw) := by
  simp [DeclEnv.tyView, lowerWindowΔ_logD h, logDDecl]
theorem lowerWindowΔ_tyView_seen (h : Fresh Δ R ids) :
    (lowerWindowΔ Δ R spec ids).tyView ids.seen = some Buffer.Q0 := by
  simp [DeclEnv.tyView, lowerWindowΔ_seen h, seenDecl]
theorem lowerWindowΔ_tyView_cursor (h : Fresh Δ R ids) :
    (lowerWindowΔ Δ R spec ids).tyView ids.cursor = some Buffer.Q0 := by
  simp [DeclEnv.tyView, lowerWindowΔ_cursor h, cursorDecl]

theorem lowerWindowΚ_window (h : Fresh Δ R ids) : lowerWindowΚ Κ R spec dc ids ids.window = some dc := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h.distinct
  simp [lowerWindowΚ, h5.symm, h9.symm]
theorem lowerWindowΚ_old {x : DeclId} (hx : x ∉ ids.list) (hxe : x ≠ R.e) :
    lowerWindowΚ Κ R spec dc ids x = Κ x := by
  simp only [WIds.list, List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true] at hx
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  simp [lowerWindowΚ, hxe, h1, h2, h3, h4, h5]

/-- **`lowerWindow_driveWF`**: the new edge `window → p` is well formed
    (`list raw`, the device domain); every old edge stays so. -/
theorem lowerWindow_driveWF (h : Fresh Δ R ids) (wf : WF Θ Δ Ω β Κ R spec) (hw : DriveWF Ω Κ Δ β) :
    DriveWF (lowerWindowΩ Ω R dc) (lowerWindowΚ Κ R spec dc ids) (lowerWindowΔ Δ R spec ids)
      (lowerWindowβ β R ids) := by
  intro x o hb
  by_cases hx : x = ids.window
  · subst hx
    rw [lowerWindowβ_window] at hb; cases hb
    exact ⟨⟨.list R.E.raw, dc⟩, lowerWindowΩ_p, lowerWindowΔ_tyView_window, lowerWindowΚ_window h⟩
  · rw [lowerWindowβ_other hx] at hb
    obtain ⟨sp, hΩ, hty, hck⟩ := hw x o hb
    have hxs : Δ x ≠ none := by intro e; rw [DeclEnv.tyView, e] at hty; exact nomatch hty
    have hold : x ∉ ids.list := h.not_fresh hxs
    have hxe : x ≠ R.e := fun e => hxs (e ▸ wf.e_fresh)
    refine ⟨sp, by rw [lowerWindowΩ_other (wf.o_ne_p' hΩ)]; exact hΩ, ?_, ?_⟩
    · rw [lowerWindowΔ_tyView_other hold hxe]; exact hty
    · rw [lowerWindowΚ_old hold hxe]; exact hck

/-- The clock projection on the six new declarations. -/
theorem lowerWindowΚ_fresh (h : Fresh Δ R ids) :
    lowerWindowΚ Κ R spec dc ids R.e = some spec.clock ∧ lowerWindowΚ Κ R spec dc ids ids.log = some spec.clock ∧
    lowerWindowΚ Κ R spec dc ids ids.logD = some dc ∧ lowerWindowΚ Κ R spec dc ids ids.seen = some dc ∧
    lowerWindowΚ Κ R spec dc ids ids.cursor = some dc := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h.distinct
  refine ⟨by simp [lowerWindowΚ], by simp [lowerWindowΚ], ?_, ?_, ?_⟩ <;>
    simp [lowerWindowΚ, h2.symm, h3.symm, h4.symm, h6.symm, h7.symm, h8.symm]

/-- **`lowerWindow_wellClocked`**: the encoder and the log in the output's
    clock, the transported log, seen, cursor and window in the device
    domain — Phase 9a's clocking of the five plus Phase 14's of the encoder;
    every old declaration keeps its own. -/
theorem lowerWindow_wellClocked (h : Fresh Δ R ids) (wf : WF Θ Δ Ω β Κ R spec)
    (nm : ∀ x ∈ R.e :: ids.list, NoMention Δ x) (hK : WellClocked Κ Δ) :
    WellClocked (lowerWindowΚ Κ R spec dc ids) (lowerWindowΔ Δ R spec ids) := by
  obtain ⟨he, hl, hlD, hsn, hcu⟩ := lowerWindowΚ_fresh (Κ := Κ) (dc := dc) h
  have hd : Δ R.d ≠ none := by
    intro e; have := wf.driver_ty; simp [DeclEnv.tyView, e] at this
  have hdK : lowerWindowΚ Κ R spec dc ids R.d = some spec.clock := by
    rw [lowerWindowΚ_old (h.not_fresh hd) wf.d_ne_e]; exact wf.driver_clock
  have hfive := buffer_elaboration_well_clocked R.E.raw spec.clock (ids.bids R.e) (lowerWindowΚ Κ R spec dc ids) dc
    (Or.inl he) hl hlD hsn hcu
  intro x body hb
  by_cases hx : x ∈ R.e :: ids.list
  · simp only [WIds.list, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [lowerWindowΔ_realizationOf_e h] at hb; cases hb
      rw [he]
      unfold Clocked
      cases spec.accepts <;>
        simp [encoderBody, clockedB, Expr.Pure.clocked (lowerWindowΚ Κ R spec dc ids) (some spec.clock) R.E.encode_pure, hdK]
    · simp [DeclEnv.realizationOf, lowerWindowΔ_log h, logDecl] at hb; subst hb; rw [hl]; exact hfive.1
    · simp [DeclEnv.realizationOf, lowerWindowΔ_logD h, logDDecl] at hb; subst hb; rw [hlD]; exact hfive.2.1
    · simp [DeclEnv.realizationOf, lowerWindowΔ_seen h, seenDecl] at hb; subst hb; rw [hsn]; exact hfive.2.2.1
    · simp [DeclEnv.realizationOf, lowerWindowΔ_cursor h, cursorDecl] at hb; subst hb; rw [hcu]; exact hfive.2.2.2.1
    · simp [DeclEnv.realizationOf, lowerWindowΔ_window, windowDecl] at hb; subst hb; rw [lowerWindowΚ_window h]
      exact hfive.2.2.2.2
  · simp only [List.mem_cons, not_or] at hx
    rw [lowerWindowΔ_realizationOf_other hx.2 hx.1] at hb
    rw [lowerWindowΚ_old hx.2 hx.1]
    have := hK x body hb
    unfold Clocked at this ⊢
    rw [← clockedB_congr (fun y hy => ?_)]
    · exact this
    · -- every reference of an old body is an old identity
      have hy : y ∉ R.e :: ids.list := by
        intro hm; exact nm y hm x body hb hy
      simp only [List.mem_cons, not_or] at hy
      rw [lowerWindowΚ_old hy.2 hy.1]

/-- **`lowerWindow_causal`**: the instantaneous edges added are
    `e → d`, `log → e`, `seen → logD`, `window → seen/cursor/logD`; the
    transports (`logD`, `cursor`) add none.  The abstract rank serves
    below `e`; the six sit above it. -/
theorem lowerWindow_causal (h : Fresh Δ R ids) (wf : WF Θ Δ Ω β Κ R spec)
    (nm : ∀ x ∈ R.e :: ids.list, NoMention Δ x) (hc : Causal Δ) : Causal (lowerWindowΔ Δ R spec ids) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h.distinct
  have hs1 := h1.symm; have hs2 := h2.symm; have hs3 := h3.symm; have hs4 := h4.symm; have hs5 := h5.symm
  have hs6 := h6.symm; have hs7 := h7.symm; have hs8 := h8.symm; have hs9 := h9.symm; have hs10 := h10.symm
  have hs11 := h11.symm; have hs12 := h12.symm; have hs13 := h13.symm; have hs14 := h14.symm; have hs15 := h15.symm
  obtain ⟨rank, Rk, hR, hedge⟩ := hc
  -- ranks: e ↦ Rk, logD ↦ Rk, cursor ↦ Rk, log ↦ Rk + 1, seen ↦ Rk + 1, window ↦ Rk + 2
  refine ⟨fun x => if x = R.e ∨ x = ids.logD ∨ x = ids.cursor then Rk
      else if x = ids.log ∨ x = ids.seen then Rk + 1 else if x = ids.window then Rk + 2 else rank x, Rk + 3, ?_, ?_⟩
  · intro x
    have := hR x
    dsimp only
    (repeat' split) <;> omega
  · intro a b hab
    obtain ⟨body, hb, hmem⟩ := InstDependsOn.iff.mp hab
    have hd : Δ R.d ≠ none := by
      intro e; have := wf.driver_ty; simp [DeclEnv.tyView, e] at this
    have hdl := h.not_fresh hd
    simp only [WIds.list, List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true] at hdl
    have hd1 : R.d ≠ ids.log := hdl.1
    have hd2 : R.d ≠ ids.logD := hdl.2.1
    have hd3 : R.d ≠ ids.seen := hdl.2.2.1
    have hd4 : R.d ≠ ids.cursor := hdl.2.2.2.1
    have hd5 : R.d ≠ ids.window := hdl.2.2.2.2
    have hde := wf.d_ne_e
    by_cases ha : a ∈ R.e :: ids.list
    · simp only [WIds.list, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [lowerWindowΔ_realizationOf_e h] at hb; cases hb
        rw [encoderBody_instRefs _ R.E.encode_pure] at hmem
        simp at hmem; subst hmem
        simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hd1, hd2, hd3, hd4, hd5, hde]
        exact hR R.d
      · simp [DeclEnv.realizationOf, lowerWindowΔ_log h, logDecl] at hb; subst hb
        simp [logBody, consE, nilE, Expr.instRefs, WIds.bids] at hmem; subst hmem
        simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15]
      · simp [DeclEnv.realizationOf, lowerWindowΔ_logD h, logDDecl] at hb; subst hb
        simp [logDBody, nilE, Expr.instRefs] at hmem
      · simp [DeclEnv.realizationOf, lowerWindowΔ_seen h, seenDecl] at hb; subst hb
        simp [seenBody, lenE, Expr.instRefs, WIds.bids] at hmem; subst hmem
        simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15]
      · simp [DeclEnv.realizationOf, lowerWindowΔ_cursor h, cursorDecl] at hb; subst hb
        simp [cursorBody, zeroE, Expr.instRefs] at hmem
      · simp [DeclEnv.realizationOf, lowerWindowΔ_window, windowDecl] at hb; subst hb
        simp [windowBody, revE, takeE, subE, Expr.instRefs, WIds.bids] at hmem
        rcases hmem with rfl | rfl | rfl <;> simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15]
    · simp only [List.mem_cons, not_or] at ha
      rw [lowerWindowΔ_realizationOf_other ha.2 ha.1] at hb
      have hbo : b ∉ R.e :: ids.list := fun hm => nm b hm a body hb (InstDependsOn.toDependsOn.instRefs_sub hmem)
      simp only [List.mem_cons, not_or, WIds.list, List.not_mem_nil, not_false_eq_true, and_true] at ha hbo
      obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6⟩ := ha
      obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ := hbo
      simp [ha1, ha2, ha3, ha4, ha5, ha6, hb1, hb2, hb3, hb4, hb5, hb6]
      exact hedge a b (InstDependsOn.iff.mpr ⟨body, hb, hmem⟩)

/-- The encoder declaration is typed at `raw` in the window design
    (Phase 14's `encoderBody_typed`, at the extended environment). -/
theorem encoderBody_typed_in (h : Fresh Δ R ids) (wf : WF Θ Δ Ω β Κ R spec) :
    HasType Θ (lowerWindowΔ Δ R spec ids) (Grant.of R.E.raw) [] (encoderBody spec.accepts R.E.encode R.d) R.E.raw := by
  have htr : HasType Θ (lowerWindowΔ Δ R spec ids) (Grant.of R.E.raw) [] R.E.encode (.arr R.E.rep R.E.raw) :=
    (wf.enc_wf.refFree_env_irrelevant (Encoder.WF_refFree wf.enc_wf)).mono_grant (fun _ hf => hf.elim)
  have hdn : Δ R.d ≠ none := by
    intro e; have := wf.driver_ty; simp [DeclEnv.tyView, e] at this
  have hd : HasType Θ (lowerWindowΔ Δ R spec ids) (Grant.of R.E.raw) [] (.declRef R.d) spec.accepts :=
    .declRef (by rw [lowerWindowΔ_tyView_other (h.not_fresh hdn) wf.d_ne_e]; exact wf.driver_ty)
  have hfit := wf.fits
  unfold EFits at hfit
  generalize hτ : spec.accepts = τ at *
  cases τ with
  | sem c => simp only [encoderBody]; exact .app htr (.rep hfit hd)
  | bool | nat | arr _ _ | q _ | opt _ | list _ | prod _ _ =>
    simp only at hfit; rw [hfit] at hd; simp only [encoderBody]; exact .app htr hd

/-- **`lowerWindow_wf`**: the window design is globally well formed — the
    six new declarations carry no commitments and are typed by Phase 14
    (the encoder) and Phase 9a (the five); every old declaration's
    evidence survives the refinement. -/
theorem lowerWindow_wf {ev : Evidence} (mono : ev.Monotone) (h : Fresh Δ R ids) (g : GlobalWF ev Θ Δ)
    (wf : WF Θ Δ Ω β Κ R spec) : GlobalWF ev Θ (lowerWindowΔ Δ R spec ids) := by
  have er := lowerWindow_envRefines h wf
  have hfive := buffer_elaboration_well_typed (τ := R.E.raw) (cs := spec.clock) (ids := ids.bids R.e) Θ
    (lowerWindowΔ Δ R spec ids)
  intro x hx hxs
  by_cases hm : x ∈ R.e :: ids.list
  · simp only [WIds.list, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [lowerWindowΔ_e h] at hxs; rw [← Option.some.inj hxs]
      refine ⟨rfl, fun b hb => ?_⟩
      simp only at hb; rw [← Option.some.inj hb]
      exact ⟨encoderBody_typed_in h wf, fun _ hp => by simp [logDecl, logDDecl, seenDecl, cursorDecl, windowDecl] at hp⟩
    · rw [lowerWindowΔ_log h] at hxs; rw [← Option.some.inj hxs]
      refine ⟨rfl, fun b hb => ?_⟩
      rw [← Option.some.inj hb]
      exact ⟨(hfive (Grant.of (.list R.E.raw)) R.E.raw_data (lowerWindowΔ_tyView_e h) (lowerWindowΔ_tyView_log h)
        (lowerWindowΔ_tyView_logD h) (lowerWindowΔ_tyView_seen h) (lowerWindowΔ_tyView_cursor h)).1,
        fun _ hp => by simp [logDecl, logDDecl, seenDecl, cursorDecl, windowDecl] at hp⟩
    · rw [lowerWindowΔ_logD h] at hxs; rw [← Option.some.inj hxs]
      refine ⟨rfl, fun b hb => ?_⟩
      rw [← Option.some.inj hb]
      exact ⟨(hfive (Grant.of (.list R.E.raw)) R.E.raw_data (lowerWindowΔ_tyView_e h) (lowerWindowΔ_tyView_log h)
        (lowerWindowΔ_tyView_logD h) (lowerWindowΔ_tyView_seen h) (lowerWindowΔ_tyView_cursor h)).2.1,
        fun _ hp => by simp [logDecl, logDDecl, seenDecl, cursorDecl, windowDecl] at hp⟩
    · rw [lowerWindowΔ_seen h] at hxs; rw [← Option.some.inj hxs]
      refine ⟨rfl, fun b hb => ?_⟩
      rw [← Option.some.inj hb]
      exact ⟨(hfive (Grant.of Buffer.Q0) R.E.raw_data (lowerWindowΔ_tyView_e h) (lowerWindowΔ_tyView_log h)
        (lowerWindowΔ_tyView_logD h) (lowerWindowΔ_tyView_seen h) (lowerWindowΔ_tyView_cursor h)).2.2.1,
        fun _ hp => by simp [logDecl, logDDecl, seenDecl, cursorDecl, windowDecl] at hp⟩
    · rw [lowerWindowΔ_cursor h] at hxs; rw [← Option.some.inj hxs]
      refine ⟨rfl, fun b hb => ?_⟩
      rw [← Option.some.inj hb]
      exact ⟨(hfive (Grant.of Buffer.Q0) R.E.raw_data (lowerWindowΔ_tyView_e h) (lowerWindowΔ_tyView_log h)
        (lowerWindowΔ_tyView_logD h) (lowerWindowΔ_tyView_seen h) (lowerWindowΔ_tyView_cursor h)).2.2.2.1,
        fun _ hp => by simp [logDecl, logDDecl, seenDecl, cursorDecl, windowDecl] at hp⟩
    · rw [lowerWindowΔ_window] at hxs; rw [← Option.some.inj hxs]
      refine ⟨rfl, fun b hb => ?_⟩
      rw [← Option.some.inj hb]
      exact ⟨(hfive (Grant.of (.list R.E.raw)) R.E.raw_data (lowerWindowΔ_tyView_e h) (lowerWindowΔ_tyView_log h)
        (lowerWindowΔ_tyView_logD h) (lowerWindowΔ_tyView_seen h) (lowerWindowΔ_tyView_cursor h)).2.2.2.2,
        fun _ hp => by simp [logDecl, logDDecl, seenDecl, cursorDecl, windowDecl] at hp⟩
  · simp only [List.mem_cons, not_or] at hm
    rw [lowerWindowΔ_other hm.2, behavior_unchanged hm.1] at hxs
    exact ⟨g.stored_id hxs, (g.wellFormed hxs).of_envRefines mono er⟩

end Structure

/-! ## The adapter's batch -/

/-- The operations of a batch: each item read by the policy, in the
    batch's order — a list of Phase 15's `Op`, no new operation. -/
def batchOps (P : Policy) (ws : List Value) : List Op :=
  ws.map fun w => match P.accept w with | some m => Op.set m | none => Op.refused

/-- The line after a batch: the last accepted item, or the line before. -/
def lineAfterBatch (P : Policy) (start : Value) (ws : List Value) : Value :=
  ws.foldl (fun l w => match P.accept w with | some m => m | none => l) start

theorem batchOps_length (P : Policy) (ws : List Value) : (batchOps P ws).length = ws.length := List.length_map ..

/-- A batch of accepted items ends on its last item; a refused item
    leaves the line where the previous one put it. -/
theorem lineAfterBatch_accepted (P : Policy) (start : Value) (ws : List Value) {w m : Value}
    (hm : P.accept w = some m) : lineAfterBatch P start (ws ++ [w]) = m := by
  simp [lineAfterBatch, List.foldl_append, hm]
theorem lineAfterBatch_refused (P : Policy) (start : Value) (ws : List Value) {w : Value}
    (hm : P.accept w = none) : lineAfterBatch P start (ws ++ [w]) = lineAfterBatch P start ws := by
  simp [lineAfterBatch, List.foldl_append, hm]
theorem lineAfterBatch_nil (P : Policy) (start : Value) : lineAfterBatch P start [] = start := rfl

/-! ## Two window realizations of one output -/

/-- **`paired_batches_of_one_window`**: two window realizations of one
    logical output into one device domain — a paired axis on two motors
    that must receive every command — carry at each device tick two
    batches of equal length whose `i`-th items are the two encoders'
    transfers of *one* value, the value the output carried at the `i`-th
    activation of the window.  The prepare/prepare/commit of each item is
    the backend's order within the batch. -/
theorem paired_batches_of_one_window {S : Sched} {Δ : DeclEnv} {I : Input} {Ω : OutputEnv} {β : DriveEnv}
    {R₁ R₂ : Realization} {spec : OutputSpec} {dc : ClockId} {f₁ f₂ : Nat → Value}
    (hs : SingleDriver β) (ho : R₁.o = R₂.o)
    (hf₁ : RepTrace S Δ I Ω β R₁ spec f₁) (hf₂ : RepTrace S Δ I Ω β R₂ spec f₂) (t : Nat) :
    ((windowTicks S spec.clock dc t).map (R₁.E.transfer ∘ f₁)).length =
      ((windowTicks S spec.clock dc t).map (R₂.E.transfer ∘ f₂)).length ∧
    ∀ i (hi : i < (windowTicks S spec.clock dc t).length),
      ∃ v, ((windowTicks S spec.clock dc t).map (R₁.E.transfer ∘ f₁))[i]'(by simpa using hi) = R₁.E.transfer v ∧
        ((windowTicks S spec.clock dc t).map (R₂.E.transfer ∘ f₂))[i]'(by simpa using hi) = R₂.E.transfer v := by
  refine ⟨by simp, fun i hi => ?_⟩
  have h1 := (hf₁ (windowTicks S spec.clock dc t)[i]).2
  have h2 := (hf₂ (windowTicks S spec.clock dc t)[i]).2
  rw [← ho] at h2
  have := single_driver_output_deterministic hs h1 h2
  have e : f₁ (windowTicks S spec.clock dc t)[i] = f₂ (windowTicks S spec.clock dc t)[i] := by
    have e := congrArg (unwrapAt spec.accepts) this
    rwa [unwrapAt_wrapAt, unwrapAt_wrapAt] at e
  rw [List.getElem_map, List.getElem_map]
  exact ⟨f₁ (windowTicks S spec.clock dc t)[i], rfl, by simp only [Function.comp]; rw [e]⟩

end BDL.OutputWindow
