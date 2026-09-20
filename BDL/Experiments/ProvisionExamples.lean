import BDL.Surface.Provision
import BDL.Surface.Stdlib

/-!
# Phase 13 — executed examples for Source provision (PRP-0001)

* A — the identity GPIO channel provisions a `bool` Source.
* B — a thermistor channel (`T = 2·n + 250 K`, a linear chart on counts)
  provisions the semantic `TempSensor : () -> RoomTemp`; the consumer
  `tooHot` computes the same truth value from raw counts as from the
  abstract temperature.
* C — rejected profiles: a channel at the wrong representation does not
  fit; a channel term that constructs a concept is untypable under
  `Grant.none`; a function raw type is not data.
* D — purity is necessary: a channel term typed in the empty design cannot
  read a declaration, but *can* hold memory, and then its value depends on
  the tick — the transfer is not a function of the raw reading.
* E — a saturating ADC is not surjective: the abstract temperature 451 K
  is observable in the abstract design and in no provisioned deployment —
  a strict refinement witness.
* F — a shared IMU image feeds `pitch` and `roll` through two channels;
  and two channels that are not jointly surjective show why trace equality
  needs a *joint* section.
-/

namespace BDL.Experiments.ProvisionEx
open BDL BDL.Reactive BDL.Clock BDL.Stdlib BDL.Provision BDL.UnitDomain

/-! ## The abstract design -/

def RoomTemp : SemanticId := ⟨90⟩
def Pitch : SemanticId := ⟨91⟩
def Roll : SemanticId := ⟨92⟩
def Θ : ConceptEnv := fun s =>
  if s = RoomTemp then some (.q Dim.Temp) else if s = Pitch ∨ s = Roll then some (.q Dim.Angle) else none

def Q0 : Ty := .q Dim.zero
def QT : Ty := .q Dim.Temp
def QA : Ty := .q Dim.Angle
def lit (d : Dim) (n : Nat) : Expr := .prim (.lit d n)

def tempSensor : DeclId := ⟨0⟩   -- () -> RoomTemp, a Source
def tooHot : DeclId := ⟨1⟩       -- bool, `rep TempSensor > 300 K`
def button : DeclId := ⟨2⟩       -- () -> bool, a plain Source
def pitch : DeclId := ⟨3⟩        -- () -> Pitch
def roll : DeclId := ⟨4⟩         -- () -> Roll
def level : DeclId := ⟨5⟩        -- bool, `rep pitch < rep roll`
def rawT : DeclId := ⟨10⟩        -- fresh: the thermistor counts
def rawB : DeclId := ⟨11⟩        -- fresh: the GPIO level
def rawImu : DeclId := ⟨12⟩      -- fresh: the IMU image

def Δ : DeclEnv := .ofList [
  ⟨tempSensor, ⟨.sem RoomTemp, []⟩, none⟩,
  ⟨tooHot, ⟨.bool, []⟩, some (ltE Dim.Temp (lit Dim.Temp 300) (.rep (.declRef tempSensor)))⟩,
  ⟨button, ⟨.bool, []⟩, none⟩,
  ⟨pitch, ⟨.sem Pitch, []⟩, none⟩,
  ⟨roll, ⟨.sem Roll, []⟩, none⟩,
  ⟨level, ⟨.bool, []⟩, some (ltE Dim.Angle (.rep (.declRef pitch)) (.rep (.declRef roll)))⟩]

def Κ : ClockEnv := fun _ => some ⟨0⟩

/-! ## Channels -/

/-- The identity GPIO channel: `bool -> bool`. -/
def gpio : Channel .bool where
  rep := .bool
  tr := .lam .bool (.var 0)
  transfer := id
  rep_semFree := trivial
  rep_data := trivial
  tr_pure := trivial
  computes := by
    rintro v ⟨b, rfl⟩
    exact .appClo .lam (.refInput rfl) (.var rfl)

/-- The thermistor term: `λn. n · 2 + 250` at `q Temp` from counts. -/
def thermTr : Expr :=
  .lam Q0 (app2 (.prim (.add Dim.Temp))
    (app2 (.prim (.mul Dim.zero Dim.Temp)) (.var 0) (lit Dim.Temp 2)) (lit Dim.Temp 250))

def thermistor : Channel Q0 where
  rep := QT
  tr := thermTr
  transfer := fun v => match v with | .nat n => .nat (n * 2 + 250) | v => v
  rep_semFree := trivial
  rep_data := trivial
  tr_pure := by simp [thermTr, app2, lit, Expr.Pure]
  computes := by
    rintro v ⟨n, rfl⟩
    have h := Ev.appClo (Δ := DeclEnv.empty) (I := fun _ _ => Value.nat n) (t := 0) (ρ := [])
      (f := thermTr) (a := .declRef ⟨0⟩) (ρ' := []) (body := _) (va := .nat n) .lam (.refInput rfl)
      (Ev.prim2 rfl (Ev.prim2 rfl (.var rfl) (Ev.lit _ _)) (Ev.lit _ _))
    simpa [Transduces, Prim.compute] using h

/-- A saturating ADC: `λn. if n < 100 then n · 2 + 250 else 450`. -/
def satTr : Expr :=
  .lam Q0 (.app (app2 (.prim (.ite QT)) (ltE Dim.zero (.var 0) (lit Dim.zero 100))
    (app2 (.prim (.add Dim.Temp)) (app2 (.prim (.mul Dim.zero Dim.Temp)) (.var 0) (lit Dim.Temp 2)) (lit Dim.Temp 250)))
    (lit Dim.Temp 450))

def satTransfer : Value → Value
  | .nat n => if n < 100 then .nat (n * 2 + 250) else .nat 450
  | v => v

def saturating : Channel Q0 where
  rep := QT
  tr := satTr
  transfer := satTransfer
  rep_semFree := trivial
  rep_data := trivial
  tr_pure := by simp [satTr, app2, lit, ltE, Expr.Pure]
  computes := by
    rintro v ⟨n, rfl⟩
    have h := Ev.appClo (Δ := DeclEnv.empty) (I := fun _ _ => Value.nat n) (t := 0) (ρ := [])
      (f := satTr) (a := .declRef ⟨0⟩) (ρ' := []) (body := _) (va := .nat n) .lam (.refInput rfl)
      (Ev.prim3 rfl (Ev.prim2 rfl (.var rfl) (Ev.lit _ _))
        (Ev.prim2 rfl (Ev.prim2 rfl (.var rfl) (Ev.lit _ _)) (Ev.lit _ _)) (Ev.lit _ _))
    unfold Transduces satTransfer
    simp only [Prim.compute] at h ⊢
    by_cases hn : n < 100 <;> simp [hn] at h ⊢ <;> exact h

/-- A channel at the wrong representation: reports counts as a temperature
    of dimension zero. -/
def wrongRep : Channel Q0 where
  rep := Q0
  tr := .lam Q0 (.var 0)
  transfer := id
  rep_semFree := trivial
  rep_data := trivial
  tr_pure := trivial
  computes := by rintro v ⟨n, rfl⟩; exact .appClo .lam (.refInput rfl) (.var rfl)

/-! ## A — the GPIO provisions `button` -/

def PB : Provision .bool := .one rawB button (some ⟨0⟩) gpio
def ΔB : DeclEnv := provision Δ PB

theorem wfB : WF Θ Δ PB :=
  WF.one rfl trivial trivial rfl rfl rfl (infer_sound (by decide))

def IB : Input := fun d t => if d = rawB then .bool (t % 2 = 0) else .nat 0

theorem exA :
    ΔB.tyView button = some .bool ∧ ΔB.tyView rawB = some .bool ∧
    ΔB.realizationOf button = some (.app gpio.tr (.declRef rawB)) ∧
    ΔB.realizationOf rawB = none ∧
    (match evalF ΔB IB 32 0 [] (.declRef button) with | some (.bool b) => b | _ => false) = true ∧
    (match evalF ΔB IB 32 1 [] (.declRef button) with | some (.bool b) => !b | _ => false) = true := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> decide

/-! ## B — the thermistor provisions `TempSensor`; `tooHot` agrees -/

def PT : Provision Q0 := .one rawT tempSensor (some ⟨0⟩) thermistor
def ΔT : DeclEnv := provision Δ PT

theorem wfT : WF Θ Δ PT :=
  WF.one rfl trivial trivial rfl rfl rfl (infer_sound (by decide))

/-- Raw counts: 20 at tick 0 (290 K), 30 at tick 1 (310 K). -/
def IT : Input := fun d t => if d = rawT then .nat (20 + 10 * t) else .nat 0

def runIsT (Δ : DeclEnv) (I : Input) (t : Nat) (e : Expr) (v : Value) : Bool :=
  match evalF Δ I 64 t [] e with | some w => Value.beq w v | none => false

theorem exB :
    ΔT.tyView tempSensor = some (.sem RoomTemp) ∧
    ΔT.realizationOf tempSensor = some (.mk RoomTemp (.app thermTr (.declRef rawT))) ∧
    -- the provisioned Source, from raw counts
    runIsT ΔT IT 0 (.declRef tempSensor) (.sem RoomTemp (.nat 290)) ∧
    runIsT ΔT IT 1 (.declRef tempSensor) (.sem RoomTemp (.nat 310)) ∧
    -- the induced abstract input is what the abstract design sees
    Value.beq (induced Δ PT IT tempSensor 0) (.sem RoomTemp (.nat 290)) ∧
    Value.beq (induced Δ PT IT tempSensor 1) (.sem RoomTemp (.nat 310)) ∧
    -- the consumer computes the same truth values on both sides
    runIsT ΔT IT 0 (.declRef tooHot) (.bool false) ∧ runIsT Δ (induced Δ PT IT) 0 (.declRef tooHot) (.bool false) ∧
    runIsT ΔT IT 1 (.declRef tooHot) (.bool true) ∧ runIsT Δ (induced Δ PT IT) 1 (.declRef tooHot) (.bool true) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The provisioned design refines the abstract one (Theorem: `EnvRefines`),
    is causal and well clocked. -/
theorem Δ_typed : GlobalWF (fun _ _ _ => True) Θ Δ := GlobalWF.ofList (by decide)

theorem exB_structure : EnvRefines Δ ΔT ∧ Causal ΔT ∧ WellClocked (provisionΚ Κ PT) ΔT := by
  refine ⟨provision_envRefines wfT, provision_causal wfT ?_ ?_, provision_wellClocked wfT ?_ ?_ ?_⟩
  · exact NoMention.of_globalWF Δ_typed rfl
  · exact Causal.ofList (fun d => if d = tooHot ∨ d = level then 1 else 0) 2 (by intro d; split <;> omega) (by decide)
  · intro s ch hc; simp [PT, Provision.one] at hc; simp [Κ, PT, Provision.one]
  · exact NoMention.of_globalWF Δ_typed rfl
  · exact WellClocked.ofList (by decide)

/-! ## C — rejected profiles -/

theorem exC :
    -- a representation mismatch does not fit the semantic Source
    ¬ Fits Θ (.sem RoomTemp) wrongRep ∧
    -- the thermistor fits it
    Fits Θ (.sem RoomTemp) thermistor ∧
    -- and does not fit a plain `bool` Source
    ¬ Fits Θ .bool thermistor ∧
    -- a channel term that constructs a concept is refused under `Grant.none`
    infer Θ DeclEnv.empty Grant.none [] (.lam QT (.mk RoomTemp (.var 0))) = none ∧
    -- (the same term is accepted under the Source's own grant — the boundary is the grant)
    infer Θ DeclEnv.empty (Grant.of (.sem RoomTemp)) [] (.lam QT (.mk RoomTemp (.var 0))) = some (.arr QT (.sem RoomTemp)) ∧
    -- a function raw type is not data: no `DeviceProfile` can carry it
    ¬ (Ty.arr Q0 Q0).Data := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, fun h => h⟩

/-! ## D — purity is necessary -/

/-- Typing in the *empty* design already forbids reading a declaration. -/
theorem Channel.WF_refFree {Θ : ConceptEnv} {raw : Ty} {ch : Channel raw} (h : ch.WF Θ) : ch.tr.RefFree := by
  unfold Expr.RefFree
  cases hr : ch.tr.refs with
  | nil => rfl
  | cons d _ =>
    obtain ⟨τ, hτ⟩ := h.refs_declared d (by rw [hr]; exact List.mem_cons_self)
    simp [DeclEnv.tyView, DeclEnv.empty] at hτ

/-- A term typed at an arrow with memory: `(λk. λn. k) (delay 0 1)`.  It is
    well typed in the empty design, it is not pure, and its "transfer"
    depends on the tick: `0` at tick 0, `1` afterwards.  A profile with this
    term would give a Source a value that is not a function of the raw
    reading — which is why `Channel` demands purity, not just typing. -/
def memTr : Expr := .app (.lam Q0 (.lam Q0 (.var 1))) (.delay (lit Dim.zero 0) (lit Dim.zero 1))

theorem exD :
    infer Θ DeclEnv.empty Grant.none [] memTr = some (.arr Q0 Q0) ∧
    ¬ memTr.Pure ∧
    -- at tick 0 the term maps 7 to 0, at tick 1 it maps 7 to 1
    (match evalF DeclEnv.empty (fun _ _ => .nat 7) 32 0 [] (.app memTr (.declRef ⟨0⟩)) with
      | some (.nat n) => n | _ => 99) = 0 ∧
    (match evalF DeclEnv.empty (fun _ _ => .nat 7) 32 1 [] (.app memTr (.declRef ⟨0⟩)) with
      | some (.nat n) => n | _ => 99) = 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem Expr.Pure.delayFree : ∀ {e : Expr}, e.Pure → e.DelayFree
  | .var _, _ | .boolLit _, _ | .natLit _, _ | .prim _, _ | .declRef _, _ => trivial
  | .lam _ b, h => Expr.Pure.delayFree (e := b) h
  | .app f a, h => ⟨Expr.Pure.delayFree (e := f) h.1, Expr.Pure.delayFree (e := a) h.2⟩
  | .rep e, h => Expr.Pure.delayFree (e := e) h
  | .mk _ e, h => Expr.Pure.delayFree (e := e) h
  | .delay _ _, h => h.elim
  | .sync _ _ _, h => h.elim
  | .fold f z l, h => ⟨Expr.Pure.delayFree (e := f) h.1, Expr.Pure.delayFree (e := z) h.2.1,
      Expr.Pure.delayFree (e := l) h.2.2⟩

theorem Expr.pure_of_refFree_delayFree : ∀ {e : Expr}, e.RefFree → e.DelayFree → e.Pure
  | .var _, _, _ | .boolLit _, _, _ | .natLit _, _, _ | .prim _, _, _ => trivial
  | .lam _ b, hr, hd => Expr.pure_of_refFree_delayFree (e := b) hr hd
  | .app f a, hr, hd => by
    simp only [Expr.RefFree, Expr.refs, List.append_eq_nil_iff] at hr
    exact ⟨Expr.pure_of_refFree_delayFree (e := f) hr.1 hd.1, Expr.pure_of_refFree_delayFree (e := a) hr.2 hd.2⟩
  | .declRef _, hr, _ => by simp [Expr.RefFree, Expr.refs] at hr
  | .rep e, hr, hd => Expr.pure_of_refFree_delayFree (e := e) hr hd
  | .mk _ e, hr, hd => Expr.pure_of_refFree_delayFree (e := e) hr hd
  | .delay _ _, _, hd => hd.elim
  | .sync _ _ _, _, hd => hd.elim
  | .fold f z l, hr, hd => by
    simp only [Expr.RefFree, Expr.refs, List.append_eq_nil_iff] at hr
    exact ⟨Expr.pure_of_refFree_delayFree (e := f) hr.1.1 hd.1,
      Expr.pure_of_refFree_delayFree (e := z) hr.1.2 hd.2.1, Expr.pure_of_refFree_delayFree (e := l) hr.2 hd.2.2⟩

/-- Purity is exactly: typed in the empty design (hence reference-free) and
    delay-free.  So the profile condition could equivalently be stated as
    `Channel.WF Θ ∧ tr.DelayFree`; `tr.Pure` is the same condition in one
    predicate. -/
theorem pure_iff_delayFree_of_wf {Θ : ConceptEnv} {raw : Ty} {ch : Channel raw} (h : ch.WF Θ) :
    ch.tr.Pure ↔ ch.tr.DelayFree :=
  ⟨Expr.Pure.delayFree, Expr.pure_of_refFree_delayFree (Channel.WF_refFree h)⟩

/-! ## E — the saturating ADC: a strict refinement witness -/

def PS : Provision Q0 := .one rawT tempSensor (some ⟨0⟩) saturating
def ΔS : DeclEnv := provision Δ PS

theorem wfS : WF Θ Δ PS :=
  WF.one rfl trivial trivial rfl rfl rfl (infer_sound (by decide))

/-- No raw count transfers to 451 K. -/
theorem sat_never_451 : ∀ v, TyVal Q0 v → saturating.transfer v ≠ .nat 451 := by
  rintro v ⟨n, rfl⟩ h
  simp only [saturating, satTransfer] at h
  split at h <;> simp at h <;> omega

/-- The abstract design observes `TempSensor = 451 K` under the input that
    says so; no provisioned deployment ever does. -/
theorem exE {S : Sched} :
    (∀ c t, MEv S Δ (fun d _ => if d = tempSensor then .sem RoomTemp (.nat 451) else .nat 0) c t []
      (.declRef tempSensor) (.sem RoomTemp (.nat 451))) ∧
    ∀ I', RawInput PS I' → ∀ c t, ¬ MEv S ΔS I' c t [] (.declRef tempSensor) (.sem RoomTemp (.nat 451)) := by
  refine ⟨fun c t => ?_, ?_⟩
  · have h := MEv.refInput (S := S) (Δ := Δ) (c := c) (t := t) (ρ := []) (d := tempSensor)
      (I := fun d _ => if d = tempSensor then .sem RoomTemp (.nat 451) else .nat 0) rfl
    simpa using h
  intro I' hI c t h
  have hv := target_value (S := S) wfS hI (Provision.one_chan_self rawT tempSensor (some ⟨0⟩) saturating)
    (h := ⟨tempSensor, ⟨.sem RoomTemp, []⟩, none⟩) rfl c t
  have hval := (MEv.refRealized (provision_realizationOf_target (Δ := Δ) (P := PS) (by decide) rfl
    (Provision.one_chan_self rawT tempSensor (some ⟨0⟩) saturating)) hv).det h
  simp only [wrapAt, Value.sem.injEq] at hval
  exact sat_never_451 _ (hI.1 t) hval.2

/-! ## F — one IMU image, two Sources; joint sections -/

def imuRaw : Ty := .prod QA QA

def chPitch : Channel imuRaw where
  rep := QA
  tr := .lam imuRaw (.app (.prim (.fst QA QA)) (.var 0))
  transfer := fun v => match v with | .pair a _ => a | v => v
  rep_semFree := trivial
  rep_data := trivial
  tr_pure := by simp [Expr.Pure]
  computes := by
    rintro v ⟨a, b, rfl, _, _⟩
    have h := Ev.appClo (Δ := DeclEnv.empty) (I := fun _ _ => Value.pair a b) (t := 0) (ρ := [])
      (f := .lam imuRaw (.app (.prim (.fst QA QA)) (.var 0))) (a := .declRef ⟨0⟩) (ρ' := []) (body := _)
      (va := .pair a b) .lam (.refInput rfl) (Ev.appPrim .prim (.var rfl))
    unfold Transduces
    simpa [applyPrim, Prim.arity, Prim.compute] using h

def chRoll : Channel imuRaw where
  rep := QA
  tr := .lam imuRaw (.app (.prim (.snd QA QA)) (.var 0))
  transfer := fun v => match v with | .pair _ b => b | v => v
  rep_semFree := trivial
  rep_data := trivial
  tr_pure := by simp [Expr.Pure]
  computes := by
    rintro v ⟨a, b, rfl, _, _⟩
    have h := Ev.appClo (Δ := DeclEnv.empty) (I := fun _ _ => Value.pair a b) (t := 0) (ρ := [])
      (f := .lam imuRaw (.app (.prim (.snd QA QA)) (.var 0))) (a := .declRef ⟨0⟩) (ρ' := []) (body := _)
      (va := .pair a b) .lam (.refInput rfl) (Ev.appPrim .prim (.var rfl))
    unfold Transduces
    simpa [applyPrim, Prim.arity, Prim.compute] using h

def PI : Provision imuRaw := .ofList rawImu (some ⟨0⟩) [(pitch, chPitch), (roll, chRoll)]
def ΔI : DeclEnv := provision Δ PI

theorem wfI : WF Θ Δ PI := by
  refine ⟨rfl, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, fun s ch hc => ?_⟩
  by_cases hp : s = pitch
  · subst hp
    have : ch = chPitch := by
      simp [PI, Provision.ofList, List.find?] at hc; exact hc.symm
    subst this
    exact ⟨_, rfl, rfl, by decide, infer_sound (by decide)⟩
  by_cases hr : s = roll
  · subst hr
    have : ch = chRoll := by
      simp [PI, Provision.ofList, List.find?, pitch, roll] at hc; exact hc.symm
    subst this
    exact ⟨_, rfl, rfl, by decide, infer_sound (by decide)⟩
  have hp' : ¬ pitch = s := fun e => hp e.symm
  have hr' : ¬ roll = s := fun e => hr e.symm
  simp [PI, Provision.ofList, List.find?, hp', hr'] at hc

def II : Input := fun d _ => if d = rawImu then .pair (.nat 10) (.nat 20) else .nat 0

theorem exF :
    -- one raw declaration, both Sources realized from it
    ΔI.realizationOf rawImu = none ∧
    ΔI.realizationOf pitch = some (.mk Pitch (.app chPitch.tr (.declRef rawImu))) ∧
    ΔI.realizationOf roll = some (.mk Roll (.app chRoll.tr (.declRef rawImu))) ∧
    ΔI.tyView pitch = some (.sem Pitch) ∧ ΔI.tyView roll = some (.sem Roll) ∧
    -- from one image: pitch 10, roll 20, and the consumer `level` sees both
    runIsT ΔI II 0 (.declRef pitch) (.sem Pitch (.nat 10)) ∧
    runIsT ΔI II 0 (.declRef roll) (.sem Roll (.nat 20)) ∧
    runIsT ΔI II 0 (.declRef level) (.bool true) ∧
    runIsT Δ (induced Δ PI II) 0 (.declRef level) (.bool true) ∧
    -- the assignment is a set: the other order is the same provision
    Provision.ofList rawImu (some ⟨0⟩) [(roll, chRoll), (pitch, chPitch)] = PI := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · exact (provision_perm (by decide) (List.Perm.swap _ _ _)).symm

/-- Two channels of one raw reading that are *not jointly* surjective: the
    identity and the successor.  Each alone is onto its range; the abstract
    input `(5, 9)` has no raw witness.  Trace equality for shared raw
    readings needs a joint section, not pointwise surjectivity. -/
def chId : Channel Q0 where
  rep := Q0
  tr := .lam Q0 (.var 0)
  transfer := id
  rep_semFree := trivial
  rep_data := trivial
  tr_pure := trivial
  computes := by rintro v ⟨n, rfl⟩; exact .appClo .lam (.refInput rfl) (.var rfl)

def chSucc : Channel Q0 where
  rep := Q0
  tr := .lam Q0 (app2 (.prim (.add Dim.zero)) (.var 0) (lit Dim.zero 1))
  transfer := fun v => match v with | .nat n => .nat (n + 1) | v => v
  rep_semFree := trivial
  rep_data := trivial
  tr_pure := by simp [app2, lit, Expr.Pure]
  computes := by
    rintro v ⟨n, rfl⟩
    have h := Ev.appClo (Δ := DeclEnv.empty) (I := fun _ _ => Value.nat n) (t := 0) (ρ := [])
      (f := .lam Q0 (app2 (.prim (.add Dim.zero)) (.var 0) (lit Dim.zero 1))) (a := .declRef ⟨0⟩) (ρ' := [])
      (body := _) (va := .nat n) .lam (.refInput rfl) (Ev.prim2 rfl (.var rfl) (Ev.lit _ _))
    simpa [Transduces, Prim.compute] using h

theorem no_joint_witness : ∀ v, TyVal Q0 v → ¬ (chId.transfer v = .nat 5 ∧ chSucc.transfer v = .nat 9) := by
  rintro v ⟨n, rfl⟩ ⟨h1, h2⟩
  simp [chId, chSucc] at h1 h2
  omega

end BDL.Experiments.ProvisionEx
