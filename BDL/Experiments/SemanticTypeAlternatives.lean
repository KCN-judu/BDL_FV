import BDL.Core.Dependency

/-!
# Phase 2 — where should semantic identity live?

Question: what is the smallest mechanism that makes representation-compatible
but semantically distinct concepts (Tilt, MotorAngle, both numeric)
non-interchangeable *by default*, while still allowing an explicit mapping
`Tilt → MotorAngle` to be authored?

Sections:

* §0 Baseline — representation types only.  **Counterexample A.**
* §A Model A — nominal `Ty.sem SemanticId` (promoted to core `Base.lean`).
  Results: mismatch rejected; explicit mapping allowed; erasure soundness
  (and: the baseline *is* erased Model A); conservativity over sem-free
  programs; rename preserves identity; identity change is an edit
  (**Counterexample B**, **Counterexample C**); refinement preservation is
  inherited from Phase 1; semantic values originate only from declarations.
* §B Model B — semantic role as interface data, separate checker.
  Results: **Counterexample D** (typing accepts what the checker must later
  reject); the tested direct-wire checker is evaded by η-expansion (formal
  rejection); role change is an edit.  §B.2 argues — it does not prove —
  that a checker enforcing identity through arbitrary term structure needs a
  compositional discipline of type-system strength, and that the tested
  strong formulation duplicates nominal typing.  The broader family of
  compositional semantic analyses is *not* universally ruled out.
* §C Model C — concepts as ordinary `DesignDecl`s in the value sort.
  Results: two category errors (formal rejection of *that* encoding).  A
  stratified concept-declaration sort is not rejected; it reintroduces an
  independent `SemanticId`, which is the Phase-2 kernel requirement anyway.

Claim strength is labelled per result: *formally rejected by counterexample*,
*tested formulation redundant*, *not rejected*, or *engineering preference*.

`nat` stands in for `Real` throughout; nothing depends on which
representation type is shared.
-/

namespace BDL.Experiments.Semantic
open BDL

/-- Evidence that discharges everything; the phase is about typing, not evidence. -/
def trivEv : Evidence := fun _ _ _ => True
instance : ∀ Δ e p, Decidable (trivEv Δ e p) := fun _ _ _ => inferInstanceAs (Decidable True)

def tiltSensor  : DeclId := ⟨30⟩
def motorTarget : DeclId := ⟨31⟩
def tiltToMotor : DeclId := ⟨32⟩
def tiltDisplay : DeclId := ⟨33⟩
def tiltSensor₂ : DeclId := ⟨34⟩

/-! ## §0 Baseline — representation types only

Tilt ↦ nat, MotorAngle ↦ nat.  The model has no place to record that these
are different concepts, so the direct wire is accepted. -/

def repTilt  : DesignDecl := ⟨tiltSensor,  ⟨.nat, []⟩, none⟩
def repMotor : DesignDecl := ⟨motorTarget, ⟨.nat, []⟩, some (.declRef tiltSensor)⟩
def Δrep : DeclEnv := .ofList [repTilt, repMotor]

/-- **Counterexample A — representation compatibility ≠ semantic compatibility.**
    A tilt reading wired straight into a motor target is accepted, and the
    design is globally well formed: there is nothing to reject it *with*. -/
theorem counterexampleA_baseline_accepts_invalid_wire : GlobalWF trivEv ConceptEnv.empty Δrep :=
  GlobalWF.ofList (by decide)

/-! ## §A Model A — nominal semantic types (`Ty.sem`)

Concepts have a stable internal id; the type `Ty.sem c` is nominal.  No
introduction/elimination forms exist in the pure fragment. -/

def cTilt   : SemanticId := ⟨0⟩
def cMotor  : SemanticId := ⟨1⟩
def cBright : SemanticId := ⟨2⟩

abbrev Tilt       : Ty := .sem cTilt
abbrev MotorAngle : Ty := .sem cMotor
abbrev Brightness : Ty := .sem cBright

/-- Distinct ids are distinct types, whatever their representation. -/
theorem sem_injective (s₁ s₂ : SemanticId) : Ty.sem s₁ = Ty.sem s₂ ↔ s₁ = s₂ := by
  constructor
  · intro h; cases h; rfl
  · intro h; rw [h]
example : Tilt ≠ MotorAngle ∧ Tilt ≠ Brightness := by decide

def aTilt      : DesignDecl := ⟨tiltSensor,  ⟨Tilt, []⟩, none⟩
def aTilt₂     : DesignDecl := ⟨tiltSensor₂, ⟨Tilt, []⟩, none⟩
def aMotorWire : DesignDecl := ⟨motorTarget, ⟨MotorAngle, []⟩, some (.declRef tiltSensor)⟩
def ΔA_bad : DeclEnv := .ofList [aTilt, aMotorWire]

/-- **Result 1 — semantic mismatch is rejected statically.**  Same wire as the
    baseline; now ill-formed, because `Tilt ≠ MotorAngle` as types. -/
theorem semantic_identity_mismatch_rejected : ¬ WellFormedDecl trivEv ConceptEnv.empty ΔA_bad [] aMotorWire := by
  decide

/-- The same semantic type may be shared by several declarations, and a
    like-to-like wire is fine. -/
def aTiltDisplay : DesignDecl := ⟨tiltDisplay, ⟨Tilt, []⟩, some (.declRef tiltSensor₂)⟩
example : GlobalWF trivEv ConceptEnv.empty (.ofList [aTilt, aTilt₂, aTiltDisplay]) := GlobalWF.ofList (by decide)

/-- **Result 2 — explicit semantic mappings are accepted.**  A *declared*
    design relationship `tiltToMotor : Tilt → MotorAngle` (itself still
    unresolved) makes the connection well typed.  The mapping is visible in
    the term.  This is a behavioural relationship between concepts, not a
    coercion, cast, or representation-level conversion — no such mechanism
    exists in the Phase-2 kernel. -/
def aMap        : DesignDecl := ⟨tiltToMotor, ⟨.arr Tilt MotorAngle, []⟩, none⟩
def aMotorMapped : DesignDecl :=
  ⟨motorTarget, ⟨MotorAngle, []⟩, some (.app (.declRef tiltToMotor) (.declRef tiltSensor))⟩
def ΔA_good : DeclEnv := .ofList [aTilt, aMap, aMotorMapped]

theorem explicit_semantic_mapping_accepted : GlobalWF trivEv ConceptEnv.empty ΔA_good :=
  GlobalWF.ofList (by decide)

/-- Semantic identity is established before any realization exists: every
    declaration in `ΔA_good` is unresolved except the wire itself. -/
example : aTilt.realization = none ∧ aMap.realization = none := by decide

/-! ### Erasure: the baseline is Model A with semantic types erased -/

/-- Erase semantic types to representation types via a binding `ρ`. -/
def _root_.BDL.Ty.erase (ρ : SemanticId → Ty) : Ty → Ty
  | .sem s => ρ s
  | .arr a b => .arr (a.erase ρ) (b.erase ρ)
  | .bool => .bool
  | .nat => .nat
  | .q d => .q d

theorem _root_.BDL.Ty.erase_semFree (ρ : SemanticId → Ty) : ∀ {τ : Ty}, τ.SemFree → τ.erase ρ = τ
  | .bool, _ => rfl
  | .nat, _ => rfl
  | .q _, _ => rfl
  | .sem _, h => h.elim
  | .arr a b, h => by simp [Ty.erase, Ty.erase_semFree ρ h.1, Ty.erase_semFree ρ h.2]

theorem _root_.BDL.Prim.ty_semFree : ∀ p : Prim, p.ty.SemFree
  | .lit _ _ => trivial
  | .add _ => ⟨trivial, trivial, trivial⟩
  | .mul _ _ => ⟨trivial, trivial, trivial⟩
  | .div _ _ => ⟨trivial, trivial, trivial⟩

/-- Erasing terms: `rep`/`mk` disappear (the representation *is* the value). -/
def _root_.BDL.Expr.erase (ρ : SemanticId → Ty) : Expr → Expr
  | .lam dom b => .lam (dom.erase ρ) (b.erase ρ)
  | .app f a => .app (f.erase ρ) (a.erase ρ)
  | .rep e => e.erase ρ
  | .mk _ e => e.erase ρ
  | e => e

def _root_.BDL.DesignDecl.erase (ρ : SemanticId → Ty) (d : DesignDecl) : DesignDecl :=
  { d with interface := { d.interface with expectedType := d.interface.expectedType.erase ρ },
           realization := d.realization.map (Expr.erase ρ) }

def _root_.BDL.DeclEnv.erase (ρ : SemanticId → Ty) (Δ : DeclEnv) : DeclEnv :=
  fun id => (Δ id).map (DesignDecl.erase ρ)

theorem _root_.BDL.DeclEnv.tyView_erase (ρ : SemanticId → Ty) (Δ : DeclEnv) (d : DeclId) :
    (Δ.erase ρ).tyView d = (Δ.tyView d).map (Ty.erase ρ) := by
  unfold DeclEnv.tyView DeclEnv.erase DesignDecl.erase
  cases Δ d <;> simp

/-- **Result 3 — erasure soundness** (Phase 3 form).  Semantic typing implies
    representation typing, for any grant, provided the erasure agrees with the
    representation binding on bound concepts (`Θ s = some R → ρ s = R`, with
    `R` sem-free).  `rep`/`mk` erase to their arguments.  So the semantic
    kernel is conservative over the representation language: generated code
    is well typed after erasing concepts. -/
theorem _root_.BDL.HasType.erase (ρ : SemanticId → Ty) {Θ : ConceptEnv} (hΘ : Θ.WF)
    (hρ : ∀ s R, Θ s = some R → ρ s = R) {Δ : DeclEnv} {G G' : Grant} {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : HasType Θ Δ G Γ e τ) :
    HasType Θ (Δ.erase ρ) G' (Γ.map (Ty.erase ρ)) (e.erase ρ) (τ.erase ρ) := by
  induction h with
  | var h => exact .var (by simp [List.getElem?_map, h])
  | boolLit => exact .boolLit
  | natLit => exact .natLit
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha
  | declRef h => exact .declRef (by rw [DeclEnv.tyView_erase, h]; rfl)
  | @rep _ _ s R hb _ ih =>
    have hR : R.erase ρ = R := Ty.erase_semFree ρ (hΘ s R hb)
    simpa [Expr.erase, hR, Ty.erase, hρ s R hb] using ih
  | @mk _ _ s R _ hb _ ih =>
    have hR : R.erase ρ = R := Ty.erase_semFree ρ (hΘ s R hb)
    simp only [Expr.erase, Ty.erase, hρ s R hb]
    simpa [hR] using ih
  | prim => simpa [Expr.erase, Ty.erase_semFree ρ (Prim.ty_semFree _)] using HasType.prim

/-- The numeric binding: every concept is represented by `nat`. -/
def ρnat : SemanticId → Ty := fun _ => .nat

/-- Erasure is not injective — this is the whole problem in one line. -/
theorem erase_not_injective : Tilt.erase ρnat = MotorAngle.erase ρnat ∧ Tilt ≠ MotorAngle := by
  decide

/-- **The baseline is erased Model A.**  Erasing the rejected design gives a
    design the baseline accepts. -/
theorem baseline_is_erased_modelA :
    ¬ WellFormedDecl trivEv ConceptEnv.empty ΔA_bad [] aMotorWire ∧
    WellFormedDecl trivEv ConceptEnv.empty (ΔA_bad.erase ρnat) [] (aMotorWire.erase ρnat) := by
  decide

/-! ### Conservativity over sem-free programs -/

def _root_.BDL.Expr.SemFree : Expr → Prop
  | .lam dom b => dom.SemFree ∧ b.SemFree
  | .app f a => f.SemFree ∧ a.SemFree
  | .rep e => e.SemFree
  | .mk _ _ => False
  | _ => True

/-- **Result 4 — semantic extension preserves structural typing.**  A
    sem-free term in a sem-free environment and context can only have a
    sem-free type: the new constructor never leaks into old programs.  (The
    stronger statement — old derivations are unchanged — holds syntactically:
    no typing rule mentions `sem`; adding the constructor added no rule.) -/
theorem semantic_extension_preserves_structural_typing {Θ : ConceptEnv} {Δ : DeclEnv} {G : Grant} {Γ : Ctx} {e : Expr} {τ : Ty}
    (hΔ : ∀ d τ', Δ.tyView d = some τ' → τ'.SemFree)
    (hΓ : ∀ τ' ∈ Γ, τ'.SemFree) (he : e.SemFree) (h : HasType Θ Δ G Γ e τ) : τ.SemFree := by
  induction h with
  | var h =>
    obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.mp h
    exact hΓ _ (List.getElem_mem _)
  | boolLit => trivial
  | natLit => trivial
  | lam _ ih =>
    refine ⟨he.1, ih ?_ he.2⟩
    intro τ' hτ'
    rcases List.mem_cons.mp hτ' with rfl | hmem
    · exact he.1
    · exact hΓ _ hmem
  | app _ _ ihf _ => exact (ihf hΓ he.1).2
  | declRef h => exact hΔ _ _ h
  | rep _ _ ih => exact (ih hΓ he).elim
  | mk _ _ _ _ => exact he.elim
  | prim => exact Prim.ty_semFree _

/-! ### Refinement preservation is inherited from Phase 1

Semantic identity lives inside `expectedType`, so `tyView` is unchanged and
every Phase-1 theorem applies verbatim: refining a semantic-typed
declaration preserves all clients. -/

def aTilt' : DesignDecl := ⟨tiltSensor, ⟨Tilt, [.monotone]⟩, none⟩

theorem semantic_check_preserved_under_interface_refinement :
    HasType ConceptEnv.empty (ΔA_good.update aTilt') Grant.none [] (.app (.declRef tiltToMotor) (.declRef tiltSensor)) MotorAngle :=
  local_refinement_preserves_global_typing (by decide : ΔA_good aTilt.id = some aTilt)
    (by decide : DeclLeq aTilt aTilt') (by decide)

/-! ### Identity change is an edit -/

/-- **Counterexample B — changing semantic identity breaks dependents.**
    Same representation (`nat` under `ρnat`), different concept: the mapping
    `tiltToMotor` no longer accepts the sensor. -/
def aTiltAsMotor : DesignDecl := ⟨tiltSensor, ⟨MotorAngle, []⟩, none⟩

theorem semantic_identity_change_is_not_refinement : ¬ InterfaceRefines aTilt.interface aTiltAsMotor.interface := by
  decide

theorem semantic_identity_change_breaks_client :
    ¬ HasType ConceptEnv.empty (ΔA_good.update aTiltAsMotor) Grant.none [] (.app (.declRef tiltToMotor) (.declRef tiltSensor)) MotorAngle := by
  decide

/-- … while its erasure changes nothing, so the baseline cannot see the edit. -/
example : (aTilt.erase ρnat).interface = (aTiltAsMotor.erase ρnat).interface := by decide

/-! ### Rename vs identity -/

/-- Surface names are an inductive here only so examples stay decidable. -/
inductive SurfaceName where
  | Tilt | DeviceTilt | MotorAngle
  deriving DecidableEq, Repr

/-- A concept: internal identity plus a display name.  Typing mentions only `id`. -/
structure Concept where
  id   : SemanticId
  name : SurfaceName
  deriving DecidableEq, Repr

def Concept.rename (c : Concept) (n : SurfaceName) : Concept := { c with name := n }

/-- **Result 5 — renaming preserves identity**, hence preserves every type
    and every client: `Ty.sem c.id` does not mention the name. -/
theorem semantic_rename_preserves_identity (c : Concept) (n : SurfaceName) :
    Ty.sem (c.rename n).id = Ty.sem c.id := rfl

/-- **Counterexample C — names as identity make renaming destructive.**
    Suppose identity *were* derived from the display name. -/
def nameAsId : SurfaceName → SemanticId
  | .Tilt => ⟨10⟩ | .DeviceTilt => ⟨11⟩ | .MotorAngle => ⟨12⟩

def nTilt : DesignDecl := ⟨tiltSensor, ⟨.sem (nameAsId .Tilt), []⟩, none⟩
def nMap  : DesignDecl := ⟨tiltToMotor, ⟨.arr (.sem (nameAsId .Tilt)) MotorAngle, []⟩, none⟩
def nRenamed : DesignDecl := ⟨tiltSensor, ⟨.sem (nameAsId .DeviceTilt), []⟩, none⟩

theorem rename_under_name_identity_breaks_client :
    HasType ConceptEnv.empty (.ofList [nTilt, nMap]) Grant.none [] (.app (.declRef tiltToMotor) (.declRef tiltSensor)) MotorAngle ∧
    ¬ HasType ConceptEnv.empty ((DeclEnv.ofList [nTilt, nMap]).update nRenamed) Grant.none []
        (.app (.declRef tiltToMotor) (.declRef tiltSensor)) MotorAngle := by
  decide

/-! ### Semantic values originate only from declarations

With no introduction form, a closed term of semantic type cannot be built
from nothing: it must come from a declaration of semantic type.  Proved by
interpreting `sem _` as the empty type. -/

def _root_.BDL.Ty.denote : Ty → Type
  | .bool => Bool
  | .nat => Nat
  | .q _ => Nat
  | .arr a b => a.denote → b.denote
  | .sem _ => Empty

def _root_.BDL.Prim.denote : ∀ p : Prim, p.ty.denote
  | .lit _ n => (show Nat from n)
  | .add _ => (show Nat → Nat → Nat from fun a b => a + b)
  | .mul _ _ => (show Nat → Nat → Nat from fun a b => a * b)
  | .div _ _ => (show Nat → Nat → Nat from fun a b => a / b)

/-- Interpretation of a context: a value for every variable. -/
def _root_.BDL.Ctx.Interp (Γ : Ctx) : Type := ∀ (i : Nat) (τ : Ty), Γ[i]? = some τ → τ.denote

def _root_.BDL.Ctx.Interp.nil : Ctx.Interp [] :=
  fun _ _ h => absurd h (by simp)

def _root_.BDL.Ctx.Interp.cons {Γ : Ctx} {dom : Ty} (x : dom.denote) (γ : Γ.Interp) :
    Ctx.Interp (dom :: Γ) :=
  fun i τ h =>
    match i, h with
    | 0, h => by
      rw [List.getElem?_cons_zero] at h
      exact (Option.some.inj h) ▸ x
    | i + 1, h => γ i τ (by rwa [List.getElem?_cons_succ] at h)

/-- Interpretation of an environment: a value for every declared type. -/
def _root_.BDL.DeclEnv.Interp (Δ : DeclEnv) : Type := ∀ (d : DeclId) (τ : Ty), Δ.tyView d = some τ → τ.denote

/-- Evaluation, by recursion on the term, driven by `infer`.  (`HasType` is a
    `Prop`, so it cannot be eliminated into `Type` directly.) -/
def _root_.BDL.Expr.eval {Θ : ConceptEnv} {Δ : DeclEnv} (δ : Δ.Interp) :
    ∀ (e : Expr) (Γ : Ctx), Γ.Interp → ∀ (τ : Ty), infer Θ Δ Grant.none Γ e = some τ → τ.denote
  | .var i, _, γ, τ, h => γ i τ h
  | .boolLit b, _, _, _, h => by cases h; exact b
  | .natLit n, _, _, _, h => by cases h; exact n
  | .declRef d, _, _, τ, h => δ d τ h
  | .prim p, _, _, _, h => by cases h; exact p.denote
  | .lam dom b, Γ, γ, τ, h => by
    cases hb : infer Θ Δ Grant.none (dom :: Γ) b with
    | none => simp [infer, hb] at h
    | some cod =>
      simp [infer, hb] at h
      subst h
      exact fun x => Expr.eval δ b (dom :: Γ) (γ.cons x) cod hb
  | .app f a, Γ, γ, τ, h => by
    cases hf : infer Θ Δ Grant.none Γ f with
    | none => simp [infer, hf] at h
    | some τf =>
      cases ha : infer Θ Δ Grant.none Γ a with
      | none => cases τf <;> simp [infer, hf, ha] at h
      | some τa =>
        cases τf with
        | bool => simp [infer, hf, ha] at h
        | nat => simp [infer, hf, ha] at h
        | q _ => simp [infer, hf, ha] at h
        | sem _ => simp [infer, hf, ha] at h
        | arr dom cod =>
          simp [infer, hf, ha] at h
          obtain ⟨rfl, rfl⟩ := h
          exact (Expr.eval δ f Γ γ _ hf) (Expr.eval δ a Γ γ _ ha)
  | .rep e, Γ, γ, τ, h => by
    -- the argument denotes `Empty`; nothing can be observed from nothing
    cases he : infer Θ Δ Grant.none Γ e with
    | none => simp [infer, he] at h
    | some τe =>
      cases τe with
      | sem s => exact (Expr.eval δ e Γ γ _ he).elim
      | bool => simp [infer, he] at h
      | nat => simp [infer, he] at h
      | q _ => simp [infer, he] at h
      | arr _ _ => simp [infer, he] at h
  | .mk s e, _, _, _, h => by simp [infer, Grant.none] at h

def _root_.BDL.HasType.denote {Θ : ConceptEnv} {Δ : DeclEnv} (δ : Δ.Interp) {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : HasType Θ Δ Grant.none Γ e τ) (γ : Γ.Interp) : τ.denote :=
  e.eval δ Γ γ τ (infer_complete h)

/-- Sem-free types are inhabited. -/
def _root_.BDL.Ty.SemFree.inhabitant : ∀ {τ : Ty}, τ.SemFree → τ.denote
  | .bool, _ => (show Bool from true)
  | .nat, _ => (show Nat from 0)
  | .q _, _ => (show Nat from 0)
  | .arr _ b, h => fun _ => Ty.SemFree.inhabitant (τ := b) h.2

/-- **Result 6.**  In an environment declaring only sem-free types, no closed
    term has a semantic type.  Hence under Model A every semantic value in a
    design traces back to a declaration of semantic type (a sensor, or a
    declared mapping).  Phase 3 refines this: with `Grant.none` — i.e. in
    client code — this remains true *even with* representation binding
    present, because `mk` needs a grant and `rep` cannot conjure a value from
    an uninhabited one.  Construction happens only inside realizations
    granted by their own signature (`RepresentationBindingAlternatives`). -/
theorem no_semantic_value_without_declaration {Θ : ConceptEnv} {Δ : DeclEnv}
    (hΔ : ∀ d τ, Δ.tyView d = some τ → τ.SemFree) (e : Expr) (s : SemanticId) :
    ¬ HasType Θ Δ Grant.none [] e (.sem s) := by
  intro h
  have δ : Δ.Interp := fun d τ hd => (hΔ d τ hd).inhabitant
  exact (h.denote δ Ctx.Interp.nil).elim

example (Θ : ConceptEnv) (e : Expr) (s : SemanticId) : ¬ HasType Θ .empty Grant.none [] e (.sem s) :=
  no_semantic_value_without_declaration (fun _ _ h => by simp [DeclEnv.tyView, DeclEnv.empty] at h) e s

/-! ## §B Model B — semantic role as interface data, typing unchanged

`Ty` stays sem-free; the interface carries `semanticRole : Option SemanticId`;
a *separate* judgment checks roles.  We build the weakest plausible checker
(direct wires only) and try to break it. -/

structure InterfaceB where
  expectedType : Ty
  semanticRole : Option SemanticId
  commitments  : List PropertyId
  deriving DecidableEq, Repr

structure DeclB where
  id          : DeclId
  interface   : InterfaceB
  realization : Option Expr
  deriving DecidableEq, Repr

abbrev EnvB := DeclId → Option DeclB

def DeclB.toDecl (b : DeclB) : DesignDecl :=
  ⟨b.id, ⟨b.interface.expectedType, b.interface.commitments⟩, b.realization⟩

/-- Typing under Model B sees the representation type only. -/
def EnvB.toDeclEnv (Δ : EnvB) : DeclEnv := fun id => (Δ id).map DeclB.toDecl

def EnvB.roleOf (Δ : EnvB) (d : DeclId) : Option (Option SemanticId) :=
  (Δ d).map (·.interface.semanticRole)

/-- The direct-wire checker: a realization that *is* a reference must have
    the same role as its target. -/
def wireOK (Δ : EnvB) (b : DeclB) : Prop :=
  match b.realization with
  | some (.declRef d) => Δ.roleOf d = some b.interface.semanticRole
  | _ => True

instance (Δ : EnvB) (b : DeclB) : Decidable (wireOK Δ b) := by
  unfold wireOK; split <;> infer_instance

def EnvB.ofList (l : List DeclB) : EnvB := fun id => l.find? (·.id = id)

def bTilt  : DeclB := ⟨tiltSensor,  ⟨.nat, some cTilt, []⟩, none⟩
def bMotorWire : DeclB := ⟨motorTarget, ⟨.nat, some cMotor, []⟩, some (.declRef tiltSensor)⟩
def ΔB_bad : EnvB := .ofList [bTilt, bMotorWire]

/-- **Counterexample D — typing accepts what the semantic checker must later
    reject.**  Under Model B the invalid wire is *well typed* (representation
    `nat` matches) and only the second judgment rejects it.  Whether this is
    acceptable is a design choice (it permits "type-correct but semantically
    pending" as a state); the cost is that structural typing is no longer a
    guarantee of connectability. -/
theorem counterexampleD_typing_accepts_semantic_check_rejects :
    WellFormedDecl trivEv ConceptEnv.empty ΔB_bad.toDeclEnv [] bMotorWire.toDecl ∧ ¬ wireOK ΔB_bad bMotorWire := by
  decide

/-- **The direct-wire checker is evaded by η-expansion.**  The same flow,
    written `(λx. x) tilt`, is not a direct wire, so the checker is silent —
    and typing is silent too.  Any checker that is not compositional over
    terms has this hole; a compositional one is a second type system (§B.2). -/
def bMotorEta : DeclB :=
  ⟨motorTarget, ⟨.nat, some cMotor, []⟩, some (.app (.lam .nat (.var 0)) (.declRef tiltSensor))⟩

theorem bweak_evaded_by_eta :
    wireOK (EnvB.ofList [bTilt, bMotorEta]) bMotorEta ∧
    WellFormedDecl trivEv ConceptEnv.empty (EnvB.ofList [bTilt, bMotorEta]).toDeclEnv [] bMotorEta.toDecl := by
  decide

/-- **Role change is an edit under Model B too.**  Retagging the sensor's
    role keeps every type (representation unchanged) but flips the semantic
    verdict of an *unchanged* client: `tiltDisplay` was fine and is now
    rejected, `motorTarget` was rejected and is now accepted. -/
def bTiltDisplay : DeclB := ⟨tiltDisplay, ⟨.nat, some cTilt, []⟩, some (.declRef tiltSensor)⟩
def bTiltAsMotor : DeclB := ⟨tiltSensor, ⟨.nat, some cMotor, []⟩, none⟩

theorem role_change_flips_unchanged_clients :
    (wireOK (EnvB.ofList [bTilt, bTiltDisplay, bMotorWire]) bTiltDisplay ∧
      ¬ wireOK (EnvB.ofList [bTilt, bTiltDisplay, bMotorWire]) bMotorWire) ∧
    (¬ wireOK (EnvB.ofList [bTiltAsMotor, bTiltDisplay, bMotorWire]) bTiltDisplay ∧
      wireOK (EnvB.ofList [bTiltAsMotor, bTiltDisplay, bMotorWire]) bMotorWire) ∧
    (bTilt.toDecl.interface = bTiltAsMotor.toDecl.interface) := by
  decide

/-! ### §B.2 What a sound Model-B checker would need (argued, not proved)

The η-gap shows that any checker enforcing semantic identity through
*arbitrary* term structure must reason compositionally about semantic flow:
it must say something about variables, lambdas, applications, and
references — i.e. it needs a discipline comparable in strength to a type
system.  The obvious such formulation — assign a role to every subterm, with
role arrows for lambdas — has the same rule shapes as `HasType` over
`Ty`-with-`sem`, and would then run *alongside* representation typing:

    Model B-strong (tested formulation)
      = HasType ConceptEnv.empty over Grant.none erased types  ×  role judgment of the same shape

where the first component is implied by the second (`HasType.erase`).  In
that formulation the second judgment carries all the information and the
first is redundant, so B-strong offers no observed benefit over Model A.

What this does **not** establish: that every compositional semantic
analysis is literally `HasType`.  Flow-sensitive, indexed/effect-like,
abstract-interpretation, or relational analyses were not formalized and are
not ruled out in general.  The claim strength is: *tested formulation
redundant with nominal typing; broader family not universally excluded*. -/

/-! ## §C Model C — concepts as ordinary `DesignDecl`s

Try the *unstratified* encoding: a concept *is* a `DesignDecl` in the same
sort as value declarations, and semantic identity is its `DeclId`.  The two
category errors below formally reject **this encoding**; they do not reject
declaration-based concept architectures in general (see the sketch after
them). -/

def cTiltDecl : DeclId := ⟨40⟩
/-- "decl Tilt, represented by nat" as an ordinary declaration. -/
def conceptTiltAsDecl : DesignDecl := ⟨cTiltDecl, ⟨.nat, []⟩, none⟩
def semOfDecl : DeclId → SemanticId := fun d => ⟨d.n⟩
def ΔC : DeclEnv := .ofList [conceptTiltAsDecl]

/-- **Category error 1.**  The concept is usable as a *value*: `declRef Tilt`
    is a well-typed `nat`. -/
theorem conceptC_usable_as_value : HasType ConceptEnv.empty ΔC Grant.none [] (.declRef cTiltDecl) .nat := by decide

/-- **Category error 2.**  The concept can be *realized by a number*, and the
    kernel calls it a valid refinement step. -/
theorem conceptC_realizable_by_a_number :
    DeclRefines trivEv ConceptEnv.empty ΔC [] conceptTiltAsDecl ⟨cTiltDecl, ⟨.nat, []⟩, some (.natLit 3)⟩ :=
  .realize (by decide)

/-- A *stratified* concept-declaration sort is not rejected: a concept
    declaration has its own identity, a display name, and an optional
    (deferred, write-once) representation — the Phase-1 declaration pattern
    at the level of types.  Once concepts inhabit a distinct sort with
    independent identity, the Phase-2 kernel requirement is again an
    independent `SemanticId` — Model A's core — and the remaining fields are
    representation metadata deferred to Phase 3.  Sketched here, not used. -/
structure ConceptDecl where
  id             : SemanticId
  name           : SurfaceName
  representation : Option Ty

end BDL.Experiments.Semantic
