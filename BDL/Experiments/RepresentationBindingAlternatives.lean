import BDL.Experiments.SemanticTypeAlternatives

/-!
# Phase 3, part 1 — representation binding

Question: what is the smallest representation-binding mechanism that lets
semantic values participate in formulas without letting representation-level
operations bypass explicit semantic mappings?

Everything here is a *local* extended language (`RExpr`, `RHasType`) so the
core is untouched until a model survives.  One typing judgment, parametrized
by a **construction policy**, covers all candidate models:

| Policy         | Model | `rep : sem s → R` | `mk s : R → sem s` |
|----------------|-------|-------------------|--------------------|
| `.free`        | A     | everywhere        | everywhere         |
| `.none`        | B     | everywhere        | nowhere            |
| `.grant G`     | C / D | everywhere        | only for `s ∈ G`   |

The representation binding itself is Model D's *witness*: a write-once
concept environment `Θ : SemanticId → Option Ty`, and both `rep` and `mk`
require `Θ s = some R`.  Model C is `.grant` with `G` taken from the
signature of the declaration being realized (`Ty.grant`).

Results (claim strength in brackets):

* **Counterexample A** — Model A admits `mkMotor (repTilt x)` with no
  declared mapping [formally rejected].
* Representation types must be sem-free, else the binding is itself a hidden
  mapping [formal constraint from counterexample].
* Model B is safe (provenance theorem) but cannot realize any mapping by a
  formula [formally proved limitation].
* Model C/D: construction is possible exactly inside a declaration whose
  signature announces the semantic type; hidden crossings inside unrelated
  bodies are rejected; provenance holds for every ungranted concept
  [formally proved].  Binding a representation is monotone; changing one is
  an edit [formally proved / counterexample].
-/

namespace BDL.Experiments.RepBinding
open BDL BDL.Experiments.Semantic

/-! ## Representation binding witness -/

/-! `ConceptEnv`, `ConceptEnv.WF`, `ConceptRefines` and `Ty.grant` were
promoted to `BDL.Core.Decl` after this experiment; they are used from there. -/

/-! ## Construction policy -/

inductive Policy where
  | free
  | none
  | grant (G : List SemanticId)
  deriving DecidableEq, Repr

def Policy.allows : Policy → SemanticId → Prop
  | .free, _ => True
  | .none, _ => False
  | .grant G, s => s ∈ G

instance : ∀ (P : Policy) (s : SemanticId), Decidable (P.allows s)
  | .free, _ => inferInstanceAs (Decidable True)
  | .none, _ => inferInstanceAs (Decidable False)
  | .grant G, s => inferInstanceAs (Decidable (s ∈ G))

/-! ## Extended language -/

inductive RExpr where
  | var (i : Nat)
  | boolLit (b : Bool)
  | natLit (n : Nat)
  | lam (dom : Ty) (body : RExpr)
  | app (f a : RExpr)
  | declRef (d : DeclId)
  | rep (e : RExpr)                 -- observe the representation
  | mk (s : SemanticId) (e : RExpr) -- construct a semantic value
  deriving DecidableEq, Repr

inductive RHasType (Θ : ConceptEnv) (Δ : DeclEnv) (P : Policy) : Ctx → RExpr → Ty → Prop where
  | var     {Γ i τ} : Γ[i]? = some τ → RHasType Θ Δ P Γ (.var i) τ
  | boolLit {Γ b}   : RHasType Θ Δ P Γ (.boolLit b) .bool
  | natLit  {Γ n}   : RHasType Θ Δ P Γ (.natLit n) .nat
  | lam     {Γ dom body cod} :
      RHasType Θ Δ P (dom :: Γ) body cod → RHasType Θ Δ P Γ (.lam dom body) (.arr dom cod)
  | app     {Γ f a dom cod} :
      RHasType Θ Δ P Γ f (.arr dom cod) → RHasType Θ Δ P Γ a dom → RHasType Θ Δ P Γ (.app f a) cod
  | declRef {Γ d τ} : Δ.tyView d = some τ → RHasType Θ Δ P Γ (.declRef d) τ
  | rep     {Γ e s R} : Θ s = some R → RHasType Θ Δ P Γ e (.sem s) → RHasType Θ Δ P Γ (.rep e) R
  | mk      {Γ e s R} : P.allows s → Θ s = some R → RHasType Θ Δ P Γ e R → RHasType Θ Δ P Γ (.mk s e) (.sem s)

def rinfer (Θ : ConceptEnv) (Δ : DeclEnv) (P : Policy) : Ctx → RExpr → Option Ty
  | Γ, .var i => Γ[i]?
  | _, .boolLit _ => some .bool
  | _, .natLit _ => some .nat
  | Γ, .lam dom body => (rinfer Θ Δ P (dom :: Γ) body).map (.arr dom)
  | Γ, .app f a =>
    match rinfer Θ Δ P Γ f, rinfer Θ Δ P Γ a with
    | some (.arr dom cod), some dom' => if dom = dom' then some cod else none
    | _, _ => none
  | _, .declRef d => Δ.tyView d
  | Γ, .rep e =>
    match rinfer Θ Δ P Γ e with
    | some (.sem s) => Θ s
    | _ => none
  | Γ, .mk s e =>
    if P.allows s then
      match Θ s, rinfer Θ Δ P Γ e with
      | some R, some R' => if R = R' then some (.sem s) else none
      | _, _ => none
    else none

theorem rinfer_sound {Θ : ConceptEnv} {Δ : DeclEnv} {P : Policy} :
    ∀ {Γ : Ctx} {e : RExpr} {τ : Ty}, rinfer Θ Δ P Γ e = some τ → RHasType Θ Δ P Γ e τ
  | _, .var _, _, h => .var h
  | _, .boolLit _, _, h => by cases h; exact .boolLit
  | _, .natLit _, _, h => by cases h; exact .natLit
  | _, .declRef _, _, h => .declRef h
  | Γ, .lam dom body, τ, h => by
    cases hb : rinfer Θ Δ P (dom :: Γ) body with
    | none => simp [rinfer, hb] at h
    | some cod =>
      simp [rinfer, hb] at h
      subst h
      exact .lam (rinfer_sound hb)
  | Γ, .app f a, τ, h => by
    cases hf : rinfer Θ Δ P Γ f with
    | none => simp [rinfer, hf] at h
    | some τf =>
      cases ha : rinfer Θ Δ P Γ a with
      | none => cases τf <;> simp [rinfer, hf, ha] at h
      | some τa =>
        cases τf with
        | bool => simp [rinfer, hf, ha] at h
        | nat => simp [rinfer, hf, ha] at h
        | q _ => simp [rinfer, hf, ha] at h
        | opt _ => simp [rinfer, hf, ha] at h
        | sem _ => simp [rinfer, hf, ha] at h
        | arr dom cod =>
          simp [rinfer, hf, ha] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .app (rinfer_sound hf) (rinfer_sound ha)
  | Γ, .rep e, τ, h => by
    cases he : rinfer Θ Δ P Γ e with
    | none => simp [rinfer, he] at h
    | some τe =>
      cases τe with
      | sem s => simp [rinfer, he] at h; exact .rep h (rinfer_sound he)
      | bool => simp [rinfer, he] at h
      | nat => simp [rinfer, he] at h
      | q _ => simp [rinfer, he] at h
      | opt _ => simp [rinfer, he] at h
      | arr _ _ => simp [rinfer, he] at h
  | Γ, .mk s e, τ, h => by
    by_cases hp : P.allows s
    · cases hΘ : Θ s with
      | none => simp [rinfer, hp, hΘ] at h
      | some R =>
        cases he : rinfer Θ Δ P Γ e with
        | none => simp [rinfer, hp, hΘ, he] at h
        | some R' =>
          simp [rinfer, hp, hΘ, he] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .mk hp hΘ (rinfer_sound he)
    · simp [rinfer, hp] at h

theorem rinfer_complete {Θ : ConceptEnv} {Δ : DeclEnv} {P : Policy} {Γ : Ctx} {e : RExpr} {τ : Ty}
    (h : RHasType Θ Δ P Γ e τ) : rinfer Θ Δ P Γ e = some τ := by
  induction h with
  | var h => exact h
  | boolLit => rfl
  | natLit => rfl
  | lam _ ih => simp [rinfer, ih]
  | app _ _ ihf iha => simp [rinfer, ihf, iha]
  | declRef h => exact h
  | rep hΘ _ ih => simp [rinfer, ih, hΘ]
  | mk hp hΘ _ ih => simp [rinfer, hp, hΘ, ih]

instance (Θ : ConceptEnv) (Δ : DeclEnv) (P : Policy) (Γ : Ctx) (e : RExpr) (τ : Ty) :
    Decidable (RHasType Θ Δ P Γ e τ) :=
  decidable_of_iff (rinfer Θ Δ P Γ e = some τ) ⟨rinfer_sound, rinfer_complete⟩

/-! ### Structural facts that hold for every policy -/

/-- Typing reads the declaration environment through `tyView` only. -/
theorem RHasType.mono_env {Θ : ConceptEnv} {Δ₁ Δ₂ : DeclEnv} {P : Policy}
    (hv : ∀ d τ, Δ₁.tyView d = some τ → Δ₂.tyView d = some τ)
    {Γ : Ctx} {e : RExpr} {τ : Ty} (h : RHasType Θ Δ₁ P Γ e τ) : RHasType Θ Δ₂ P Γ e τ := by
  induction h with
  | var h => exact .var h
  | boolLit => exact .boolLit
  | natLit => exact .natLit
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha
  | declRef h => exact .declRef (hv _ _ h)
  | rep hΘ _ ih => exact .rep hΘ ih
  | mk hp hΘ _ ih => exact .mk hp hΘ ih

/-- **Binding a representation is monotone**: derivations survive binding
    more concepts (the concept environment is write-once, like realizations). -/
theorem RHasType.mono_concept {Θ₁ Θ₂ : ConceptEnv} (hc : ConceptRefines Θ₁ Θ₂) {Δ : DeclEnv} {P : Policy}
    {Γ : Ctx} {e : RExpr} {τ : Ty} (h : RHasType Θ₁ Δ P Γ e τ) : RHasType Θ₂ Δ P Γ e τ := by
  induction h with
  | var h => exact .var h
  | boolLit => exact .boolLit
  | natLit => exact .natLit
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha
  | declRef h => exact .declRef h
  | rep hΘ _ ih => exact .rep (hc _ _ hΘ) ih
  | mk hp hΘ _ ih => exact .mk hp (hc _ _ hΘ) ih

/-- Granting more construction rights is monotone. -/
theorem RHasType.mono_policy {Θ : ConceptEnv} {Δ : DeclEnv} {P₁ P₂ : Policy}
    (hp : ∀ s, P₁.allows s → P₂.allows s)
    {Γ : Ctx} {e : RExpr} {τ : Ty} (h : RHasType Θ Δ P₁ Γ e τ) : RHasType Θ Δ P₂ Γ e τ := by
  induction h with
  | var h => exact .var h
  | boolLit => exact .boolLit
  | natLit => exact .natLit
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha
  | declRef h => exact .declRef h
  | rep hΘ _ ih => exact .rep hΘ ih
  | mk hp' hΘ _ ih => exact .mk (hp _ hp') hΘ ih

/-- Does `mk s` occur anywhere in the term? -/
def RExpr.constructs (s : SemanticId) : RExpr → Prop
  | .lam _ b => b.constructs s
  | .app f a => f.constructs s ∨ a.constructs s
  | .rep e => e.constructs s
  | .mk s' e => s' = s ∨ e.constructs s
  | _ => False

/-- **Syntactic invariant (Model E, occurrence form).**  A well-typed term
    constructs `s` only if the policy grants `s`.  Under `.grant τ.grant`
    this reads: a semantic value of `s` is constructed only inside the
    realization of a declaration whose signature announces `sem s`. -/
theorem mk_requires_grant {Θ : ConceptEnv} {Δ : DeclEnv} {P : Policy} {Γ : Ctx} {e : RExpr} {τ : Ty}
    (h : RHasType Θ Δ P Γ e τ) : ∀ s, e.constructs s → P.allows s := by
  induction h with
  | var _ | boolLit | natLit | declRef _ => intro s hs; exact hs.elim
  | lam _ ih => exact ih
  | app _ _ ihf iha => intro s hs; exact hs.elim (ihf s) (iha s)
  | rep _ _ ih => exact ih
  | mk hp _ _ ih =>
    intro s hs
    rcases hs with rfl | hs
    · exact hp
    · exact ih s hs

/-! ## Provenance: per-concept denotation

Interpret `sem t` as an uninhabited type and every other `sem s` as `Unit`.
A type is a *`t`-source* iff its interpretation is empty; a closed term of a
`t`-source type can then only exist if some declaration has one — unless
the policy grants `t`. -/

def _root_.BDL.Ty.isSourceB (t : SemanticId) : Ty → Bool
  | .bool => false
  | .nat => false
  | .q _ => false
  | .opt _ => false   -- `none` inhabits every option type: an absent event is no source
  | .sem s => decide (s = t)
  | .arr a b => !a.isSourceB t && b.isSourceB t

/-- `τ` can *produce* a `t`-value: `sem t` itself, or an arrow whose domain is
    not a `t`-source and whose codomain is.  (`mk_t : R → sem t` and
    `f : Tilt → MotorAngle` are motor-sources; `rep_t : sem t → R` and
    `id : sem t → sem t` are not.) -/
def _root_.BDL.Ty.IsSource (t : SemanticId) (τ : Ty) : Prop := τ.isSourceB t = true

instance (t : SemanticId) (τ : Ty) : Decidable (τ.IsSource t) :=
  inferInstanceAs (Decidable (τ.isSourceB t = true))

def _root_.BDL.Ty.tdenote (t : SemanticId) : Ty → Type
  | .bool => Bool
  | .nat => Nat
  | .q _ => Nat
  | .opt τ => Option (τ.tdenote t)
  | .arr a b => a.tdenote t → b.tdenote t
  | .sem s => PLift (s ≠ t)

/-- Inhabitants for non-sources, emptiness for sources. -/
structure TInfo (t : SemanticId) (τ : Ty) where
  inh : ¬ τ.IsSource t → τ.tdenote t
  emp : τ.IsSource t → τ.tdenote t → False

def _root_.BDL.Ty.tinfo (t : SemanticId) : ∀ τ : Ty, TInfo t τ
  | .bool => ⟨fun _ => (show Bool from true), fun h => by simp [Ty.IsSource, Ty.isSourceB] at h⟩
  | .nat => ⟨fun _ => (show Nat from 0), fun h => by simp [Ty.IsSource, Ty.isSourceB] at h⟩
  | .q _ => ⟨fun _ => (show Nat from 0), fun h => by simp [Ty.IsSource, Ty.isSourceB] at h⟩
  | .opt _ => ⟨fun _ => (show Option _ from Option.none), fun h => by simp [Ty.IsSource, Ty.isSourceB] at h⟩
  | .sem s =>
    ⟨fun h => ⟨by simpa [Ty.IsSource, Ty.isSourceB] using h⟩,
     fun h x => PLift.down x (by simpa [Ty.IsSource, Ty.isSourceB] using h)⟩
  | .arr a b =>
    let ia := Ty.tinfo t a
    let ib := Ty.tinfo t b
    ⟨fun h x =>
      if ha : a.IsSource t then (ia.emp ha x).elim
      else ib.inh (fun hb => h (by simp [Ty.IsSource, Ty.isSourceB] at ha hb ⊢; exact ⟨ha, hb⟩)),
     fun h f =>
      have h' : ¬ a.IsSource t ∧ b.IsSource t := by
        simpa [Ty.IsSource, Ty.isSourceB] using h
      ib.emp h'.2 (f (ia.inh h'.1))⟩

theorem _root_.BDL.Ty.SemFree.not_source {t : SemanticId} : ∀ {τ : Ty}, τ.SemFree → ¬ τ.IsSource t
  | .bool, _ => by simp [Ty.IsSource, Ty.isSourceB]
  | .nat, _ => by simp [Ty.IsSource, Ty.isSourceB]
  | .q _, _ => by simp [Ty.IsSource, Ty.isSourceB]
  | .opt _, _ => by simp [Ty.IsSource, Ty.isSourceB]
  | .sem _, h => h.elim
  | .arr a b, h => by
    have := Ty.SemFree.not_source (t := t) (τ := b) h.2
    simp [Ty.IsSource, Ty.isSourceB] at this ⊢
    intro _; exact this

def CtxInterp (t : SemanticId) (Γ : Ctx) : Type := ∀ (i : Nat) (τ : Ty), Γ[i]? = some τ → τ.tdenote t

def CtxInterp.nil (t : SemanticId) : CtxInterp t [] := fun _ _ h => absurd h (by simp)

def CtxInterp.cons {t : SemanticId} {Γ : Ctx} {dom : Ty} (x : dom.tdenote t) (γ : CtxInterp t Γ) :
    CtxInterp t (dom :: Γ) :=
  fun i τ h =>
    match i, h with
    | 0, h => by rw [List.getElem?_cons_zero] at h; exact (Option.some.inj h) ▸ x
    | i + 1, h => γ i τ (by rwa [List.getElem?_cons_succ] at h)

/-- Evaluation under the `t`-interpretation, for any policy that does not
    grant `t`.  `rep` never needs the value of its argument (the result is a
    sem-free representation); `mk s` for `s ≠ t` is `()`. -/
def REval {Θ : ConceptEnv} (hΘ : Θ.WF) {Δ : DeclEnv} {P : Policy} {t : SemanticId}
    (hP : ¬ P.allows t) (δ : ∀ (d : DeclId) (τ : Ty), Δ.tyView d = some τ → τ.tdenote t) :
    ∀ (e : RExpr) (Γ : Ctx), CtxInterp t Γ → ∀ (τ : Ty), rinfer Θ Δ P Γ e = some τ → τ.tdenote t
  | .var i, _, γ, τ, h => γ i τ h
  | .boolLit b, _, _, _, h => by cases h; exact b
  | .natLit n, _, _, _, h => by cases h; exact n
  | .declRef d, _, _, τ, h => δ d τ h
  | .lam dom b, Γ, γ, τ, h => by
    cases hb : rinfer Θ Δ P (dom :: Γ) b with
    | none => simp [rinfer, hb] at h
    | some cod =>
      simp [rinfer, hb] at h
      subst h
      exact fun x => REval hΘ hP δ b (dom :: Γ) (γ.cons x) cod hb
  | .app f a, Γ, γ, τ, h => by
    cases hf : rinfer Θ Δ P Γ f with
    | none => simp [rinfer, hf] at h
    | some τf =>
      cases ha : rinfer Θ Δ P Γ a with
      | none => cases τf <;> simp [rinfer, hf, ha] at h
      | some τa =>
        cases τf with
        | bool => simp [rinfer, hf, ha] at h
        | nat => simp [rinfer, hf, ha] at h
        | q _ => simp [rinfer, hf, ha] at h
        | opt _ => simp [rinfer, hf, ha] at h
        | sem _ => simp [rinfer, hf, ha] at h
        | arr dom cod =>
          simp [rinfer, hf, ha] at h
          obtain ⟨rfl, rfl⟩ := h
          exact (REval hΘ hP δ f Γ γ _ hf) (REval hΘ hP δ a Γ γ _ ha)
  | .rep e, Γ, _, τ, h => by
    cases he : rinfer Θ Δ P Γ e with
    | none => simp [rinfer, he] at h
    | some τe =>
      cases τe with
      | sem s =>
        simp [rinfer, he] at h
        exact (Ty.tinfo t τ).inh ((hΘ s τ h).1.not_source)
      | bool => simp [rinfer, he] at h
      | nat => simp [rinfer, he] at h
      | q _ => simp [rinfer, he] at h
      | opt _ => simp [rinfer, he] at h
      | arr _ _ => simp [rinfer, he] at h
  | .mk s e, Γ, _, τ, h => by
    by_cases hp : P.allows s
    · cases hΘs : Θ s with
      | none => simp [rinfer, hp, hΘs] at h
      | some R =>
        cases he : rinfer Θ Δ P Γ e with
        | none => simp [rinfer, hp, hΘs, he] at h
        | some R' =>
          simp [rinfer, hp, hΘs, he] at h
          obtain ⟨_, rfl⟩ := h
          exact ⟨fun hst => hP (hst ▸ hp)⟩
    · simp [rinfer, hp] at h

/-- **Provenance theorem.**  If the policy does not grant `t` and no
    declaration has a `t`-source type, then no closed term has a `t`-source
    type.  So `t`-values arise only from declarations typed as `t`-sources
    (sensors `sem t`, explicit mappings `… → sem t`) or inside realizations
    granted `t`. -/
theorem provenance {Θ : ConceptEnv} (hΘ : Θ.WF) {Δ : DeclEnv} {P : Policy} {t : SemanticId}
    (hP : ¬ P.allows t) (hΔ : ∀ d τ, Δ.tyView d = some τ → ¬ τ.IsSource t)
    {e : RExpr} {τ : Ty} (h : RHasType Θ Δ P [] e τ) : ¬ τ.IsSource t := by
  intro hsrc
  have δ : ∀ (d : DeclId) (τ : Ty), Δ.tyView d = some τ → τ.tdenote t :=
    fun d τ hd => (Ty.tinfo t τ).inh (hΔ d τ hd)
  exact (Ty.tinfo t τ).emp hsrc (REval hΘ hP δ e [] (CtxInterp.nil t) τ (rinfer_complete h))

/-! ## The concrete scenario -/

def brightnessCtrl : DeclId := ⟨50⟩
def motorConsumer  : DeclId := ⟨51⟩

/-- Everything is represented by `nat`. -/
def Θnat : ConceptEnv := fun _ => some .nat
theorem Θnat_wf : Θnat.WF := fun _ _ h => by cases h; exact ⟨trivial, trivial⟩

def dTilt : DesignDecl := ⟨tiltSensor, ⟨Tilt, []⟩, none⟩
def dMotorConsumer : DesignDecl := ⟨motorConsumer, ⟨.arr MotorAngle Brightness, []⟩, none⟩
def Δ₁ : DeclEnv := .ofList [dTilt, dMotorConsumer]

/-! ### Model A — unrestricted symmetric `mk`/`rep` -/

/-- **Counterexample A.**  With both directions free, `λx. mkMotor (repTilt x)`
    is a closed, well-typed `Tilt → MotorAngle` in the *empty* environment:
    no declaration, no mapping, nothing to see at the signature level. -/
theorem unrestricted_representation_binding_bypasses_semantic_identity :
    RHasType Θnat .empty .free [] (.lam Tilt (.mk cMotor (.rep (.var 0)))) (.arr Tilt MotorAngle) := by
  decide

/-- Worse: semantic values from nothing. -/
theorem unrestricted_mk_creates_semantic_values_from_nothing :
    RHasType Θnat .empty .free [] (.mk cMotor (.natLit 0)) MotorAngle := by decide

/-- And the crossing can hide inside a body whose signature says nothing
    about motors: `brightnessCtrl : Tilt → Brightness` secretly drives the
    motor consumer with a re-labelled tilt. -/
theorem hidden_crossing_inside_unrelated_body :
    RHasType Θnat Δ₁ .free []
      (.lam Tilt (.app (.declRef motorConsumer) (.mk cMotor (.rep (.var 0)))))
      (.arr Tilt Brightness) := by
  decide

/-- Model A therefore falsifies the Phase-2 provenance result. -/
theorem modelA_breaks_phase2_provenance :
    ∃ e, RHasType Θnat .empty .free [] e MotorAngle :=
  ⟨_, unrestricted_mk_creates_semantic_values_from_nothing⟩

/-! ### The binding itself must be sem-free -/

/-- If a concept may be "represented by" another semantic type, `rep` is a
    hidden mapping — under *every* policy, even observation-only. -/
def Θbad : ConceptEnv := fun s => if s = cTilt then some MotorAngle else some .nat

theorem binding_to_semantic_type_is_hidden_mapping :
    RHasType Θbad .empty .none [] (.lam Tilt (.rep (.var 0))) (.arr Tilt MotorAngle) := by
  decide

example : ¬ Θbad.WF := fun h => (h cTilt MotorAngle (by decide)).1.elim

/-! ### Model B — observation only -/

/-- Tilt can be inspected numerically … -/
theorem observation_is_available :
    RHasType Θnat Δ₁ .none [] (.lam Tilt (.rep (.var 0))) (.arr Tilt .nat) := by decide

/-- … and Model B is safe: no concept can be manufactured anywhere. -/
theorem modelB_provenance {Δ : DeclEnv} {t : SemanticId}
    (hΔ : ∀ d τ, Δ.tyView d = some τ → ¬ τ.IsSource t) {e : RExpr} {τ : Ty}
    (h : RHasType Θnat Δ .none [] e τ) : ¬ τ.IsSource t :=
  provenance Θnat_wf (P := .none) (t := t) (fun hf => hf) hΔ h

/-- **But no mapping can be realized by a formula.**  In an environment with
    only a tilt sensor, *no* closed term has type `Tilt → Brightness` — the
    mapping can only be supplied externally.  (Note that `motorConsumer :
    MotorAngle → Brightness` would itself count as a Brightness-source, so it
    is excluded here; the point is that the *formula* `λx. …` cannot be
    written.) -/
def Δ₀ : DeclEnv := .ofList [dTilt]

theorem modelB_cannot_realize_mapping :
    ¬ ∃ e, RHasType Θnat Δ₀ .none [] e (.arr Tilt Brightness) := by
  rintro ⟨e, h⟩
  refine modelB_provenance (t := cBright) ?_ h (by decide)
  intro d τ hd
  simp only [DeclEnv.tyView, Option.map_eq_some_iff] at hd
  obtain ⟨dh, hfind, rfl⟩ := hd
  obtain ⟨hmem, _⟩ := DeclEnv.ofList_some hfind
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  subst hmem
  decide

/-! ### Model C / D — construction granted by the signature -/

/-- **Positive result.**  The global bypass is rejected in the base judgment
    (no grants): the invalid wire, written with explicit `rep`/`mk`, is
    ill-typed. -/
theorem representation_binding_does_not_enable_hidden_semantic_mapping :
    ¬ RHasType Θnat Δ₁ (.grant []) [] (.mk cMotor (.rep (.declRef tiltSensor))) MotorAngle := by
  decide

/-- **Explicit mappings can be realized by formulas.**  Inside the realization
    of `tiltToBright : Tilt → Brightness` (grant `[cBright]`), the body may
    observe the tilt and construct a brightness. -/
theorem explicit_semantic_mapping_can_use_representation_formula :
    RHasType Θnat Δ₁ (.grant (Ty.arr Tilt Brightness).grant) []
      (.lam Tilt (.mk cBright (.rep (.var 0)))) (.arr Tilt Brightness) := by
  decide

/-- **The hidden crossing of Model A is rejected.**  The same body, realized
    under `brightnessCtrl`'s own grant, cannot construct a motor angle. -/
theorem hidden_crossing_rejected_under_grant :
    ¬ RHasType Θnat Δ₁ (.grant (Ty.arr Tilt Brightness).grant) []
      (.lam Tilt (.app (.declRef motorConsumer) (.mk cMotor (.rep (.var 0)))))
      (.arr Tilt Brightness) := by
  decide

/-- To drive the motor from a tilt, the designer must *declare* the crossing;
    the mapping's own realization is then granted `cMotor`. -/
def dTiltToMotor : DesignDecl := ⟨tiltToMotor, ⟨.arr Tilt MotorAngle, []⟩, none⟩
theorem declared_crossing_realizable :
    RHasType Θnat Δ₁ (.grant (Ty.arr Tilt MotorAngle).grant) []
      (.lam Tilt (.mk cMotor (.rep (.var 0)))) (.arr Tilt MotorAngle) ∧
    RHasType Θnat (Δ₁.update dTiltToMotor) (.grant (Ty.arr Tilt Brightness).grant) []
      (.lam Tilt (.app (.declRef motorConsumer) (.app (.declRef tiltToMotor) (.var 0))))
      (.arr Tilt Brightness) := by
  decide

/-- Provenance under grants: for every concept *not* granted to the body
    being typed, values still trace to declared sources. -/
theorem grant_provenance {Δ : DeclEnv} {G : List SemanticId} {t : SemanticId} (ht : t ∉ G)
    (hΔ : ∀ d τ, Δ.tyView d = some τ → ¬ τ.IsSource t) {e : RExpr} {τ : Ty}
    (h : RHasType Θnat Δ (.grant G) [] e τ) : ¬ τ.IsSource t :=
  provenance Θnat_wf (P := .grant G) (t := t) ht hΔ h

/-! ### Representation binding: deferred, monotone to bind, edit to change -/

/-- Unbound concept: `rep`/`mk` are untypable, but ordinary semantic wiring
    (`declRef`, mappings) is unaffected — signature-first at the type level. -/
def Θnone : ConceptEnv := fun _ => none
theorem unbound_concept_still_wires :
    RHasType Θnone (Δ₁.update dTiltToMotor) (.grant []) []
      (.app (.declRef motorConsumer) (.app (.declRef tiltToMotor) (.declRef tiltSensor))) Brightness ∧
    ¬ RHasType Θnone Δ₁ (.grant [cBright]) [] (.lam Tilt (.mk cBright (.rep (.var 0)))) (.arr Tilt Brightness) := by
  decide

/-- **Counterexample D (representation change).**  A body typed with
    `Tilt ↦ nat` breaks when the binding is changed to `Tilt ↦ bool`. -/
def ΘtiltBool : ConceptEnv := fun s => if s = cTilt then some .bool else some .nat

theorem representation_change_is_edit_not_refinement :
    RHasType Θnat Δ₁ (.grant [cBright]) [] (.lam Tilt (.mk cBright (.rep (.var 0)))) (.arr Tilt Brightness) ∧
    ¬ RHasType ΘtiltBool Δ₁ (.grant [cBright]) [] (.lam Tilt (.mk cBright (.rep (.var 0)))) (.arr Tilt Brightness) ∧
    ¬ ConceptRefines Θnat ΘtiltBool := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have := h cTilt .nat rfl
  simp [ΘtiltBool] at this

end BDL.Experiments.RepBinding
