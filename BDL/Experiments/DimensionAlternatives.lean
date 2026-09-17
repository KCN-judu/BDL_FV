import BDL.Experiments.RepresentationBindingAlternatives

/-!
# Phase 3, part 2 — physical dimensions

Question: what is the smallest dimensional mechanism that rejects
dimensionally invalid computation while keeping semantic identity independent
of physical representation?

The candidate in core: `Ty.q d` with `d : Dim` an exponent vector, and
dimension algebra living in the *types of registered operators* (`Prim.ty`):
`add d : q d → q d → q d`, `mul d₁ d₂ : … → q (d₁ + d₂)`, `div`.  Typing an
application is ordinary STLC; there is no dimension-specific rule.

Results (claim strength in brackets):

* **Counterexample B** — erasing dimensions to `q 0` (the "everything is a
  number" baseline) accepts `Length + Time`; the erasure is sound and not
  injective, so the baseline is exactly erased dimensional typing
  [formally proved / reduction by proof].
* `dimension_mismatch_rejected`, `dimensional_addition_requires_equal_dimensions`,
  products and quotients [formally proved].
* Units are surface: a unit literal elaborates to a dimensioned literal;
  changing the unit changes the value, never the type [formally proved].
* **Counterexample C** — Tilt and MotorAngle both bound to `q Angle` remain
  distinct types and the direct wire is still rejected [formally proved].
* A semantic mapping realized by a dimensioned formula, with a dimension
  error *inside* the formula caught by the same typing [formally proved].
* **Counterexample D** — rebinding Tilt from `q Angle` to `q Length` breaks
  an existing realization and is not a `ConceptRefines` step [formally proved].
* Dimensions as metadata / validation: not formalized; see §D for the
  argument and its (limited) strength.
-/

namespace BDL.Experiments.Dimension
open BDL BDL.Experiments.Semantic BDL.Experiments.RepBinding

/-! ## Dimension algebra is just `Prim.ty` -/

example : (Prim.mul Dim.Length Dim.Time).ty = .arr (.q Dim.Length) (.arr (.q Dim.Time) (.q ⟨1, 1, 0⟩)) := by
  decide
example : (Prim.div Dim.Length Dim.Time).ty = .arr (.q Dim.Length) (.arr (.q Dim.Time) (.q ⟨1, -1, 0⟩)) := by
  decide

def lenSensor  : DeclId := ⟨60⟩
def timeSensor : DeclId := ⟨61⟩
def gainDecl   : DeclId := ⟨62⟩

def dLen  : DesignDecl := ⟨lenSensor,  ⟨.q Dim.Length, []⟩, none⟩
def dTime : DesignDecl := ⟨timeSensor, ⟨.q Dim.Time, []⟩, none⟩
def Δdim : DeclEnv := .ofList [dLen, dTime]

/-- `length + time` -/
def lenPlusTime : Expr := .app (.app (.prim (.add Dim.Length)) (.declRef lenSensor)) (.declRef timeSensor)
/-- `length / time` -/
def velocity : Expr := .app (.app (.prim (.div Dim.Length Dim.Time)) (.declRef lenSensor)) (.declRef timeSensor)

/-- **`dimension_mismatch_rejected`.**  Not well typed at any type. -/
theorem dimension_mismatch_rejected :
    infer ConceptEnv.empty Δdim Grant.none [] lenPlusTime = none := by decide

/-- Quotients compute their dimension. -/
theorem velocity_typed :
    HasType ConceptEnv.empty Δdim Grant.none [] velocity (.q ⟨1, -1, 0⟩) := by decide

/-- **`dimensional_addition_requires_equal_dimensions`** — by inversion of
    ordinary application typing against `Prim.ty`. -/
theorem dimensional_addition_requires_equal_dimensions {Θ : ConceptEnv} {Δ : DeclEnv} {G : Grant}
    {Γ : Ctx} {d : Dim} {a b : Expr} {τ : Ty}
    (h : HasType Θ Δ G Γ (.app (.app (.prim (.add d)) a) b) τ) :
    HasType Θ Δ G Γ a (.q d) ∧ HasType Θ Δ G Γ b (.q d) ∧ τ = .q d := by
  cases h with
  | app hf hb =>
    cases hf with
    | app hp ha =>
      cases hp
      exact ⟨ha, hb, rfl⟩

/-! ## Counterexample B — the numeric baseline is erased dimensional typing -/

def _root_.BDL.Dim.erase : Dim → Dim := fun _ => Dim.zero

def _root_.BDL.Ty.eraseDim : Ty → Ty
  | .q _ => .q Dim.zero
  | .arr a b => .arr a.eraseDim b.eraseDim
  | .opt τ => .opt τ.eraseDim
  | .list τ => .list τ.eraseDim
  | .prod a b => .prod a.eraseDim b.eraseDim
  | τ => τ

theorem _root_.BDL.Ty.eraseDim_data : ∀ {τ : Ty}, τ.Data → τ.eraseDim.Data
  | .bool, _ | .nat, _ | .q _, _ | .sem _, _ => trivial
  | .opt τ, h => Ty.eraseDim_data (τ := τ) h
  | .list τ, h => Ty.eraseDim_data (τ := τ) h
  | .prod _ _, h => ⟨Ty.eraseDim_data h.1, Ty.eraseDim_data h.2⟩
  | .arr _ _, h => h.elim

def _root_.BDL.Prim.eraseDim : Prim → Prim
  | .lit _ n => .lit Dim.zero n
  | .add _ => .add Dim.zero
  | .sub _ => .sub Dim.zero
  | .mul _ _ => .mul Dim.zero Dim.zero
  | .div _ _ => .div Dim.zero Dim.zero
  | .lt τ h => .lt τ.eraseDim (Ty.eraseDim_data h)
  | .eq τ h => .eq τ.eraseDim (Ty.eraseDim_data h)
  | .ite τ => .ite τ.eraseDim
  | .none τ => .none τ.eraseDim
  | .some τ => .some τ.eraseDim
  | .isSome τ => .isSome τ.eraseDim
  | .getD τ => .getD τ.eraseDim
  | .nil τ => .nil τ.eraseDim
  | .cons τ => .cons τ.eraseDim
  | .length τ => .length τ.eraseDim
  | .take τ => .take τ.eraseDim
  | .reverse τ => .reverse τ.eraseDim
  | .head τ => .head τ.eraseDim
  | .pair a b => .pair a.eraseDim b.eraseDim
  | .fst a b => .fst a.eraseDim b.eraseDim
  | .snd a b => .snd a.eraseDim b.eraseDim
  | .drop τ => .drop τ.eraseDim
  | .toList τ => .toList τ.eraseDim
  | p => p

theorem _root_.BDL.Prim.ty_eraseDim (p : Prim) : p.eraseDim.ty = p.ty.eraseDim := by
  cases p <;> simp [Prim.eraseDim, Prim.ty, Ty.eraseDim, Dim.add, Dim.sub, Dim.zero]

def _root_.BDL.Expr.eraseDim : Expr → Expr
  | .lam dom b => .lam dom.eraseDim b.eraseDim
  | .app f a => .app f.eraseDim a.eraseDim
  | .rep e => .rep e.eraseDim
  | .mk s e => .mk s e.eraseDim
  | .prim p => .prim p.eraseDim
  | .delay i e => .delay i.eraseDim e.eraseDim
  | .sync c i e => .sync c i.eraseDim e.eraseDim
  | .fold f z l => .fold f.eraseDim z.eraseDim l.eraseDim
  | e => e

def _root_.BDL.DesignDecl.eraseDim (d : DesignDecl) : DesignDecl :=
  { d with interface := { d.interface with expectedType := d.interface.expectedType.eraseDim },
           realization := d.realization.map Expr.eraseDim }

def _root_.BDL.DeclEnv.eraseDim (Δ : DeclEnv) : DeclEnv := fun id => (Δ id).map DesignDecl.eraseDim
def _root_.BDL.ConceptEnv.eraseDim (Θ : ConceptEnv) : ConceptEnv := fun s => (Θ s).map Ty.eraseDim

theorem _root_.BDL.DeclEnv.tyView_eraseDim (Δ : DeclEnv) (d : DeclId) :
    Δ.eraseDim.tyView d = (Δ.tyView d).map Ty.eraseDim := by
  unfold DeclEnv.tyView DeclEnv.eraseDim DesignDecl.eraseDim
  cases Δ d <;> simp

/-- Erasing dimensions is sound: dimensional typing implies numeric typing. -/
theorem _root_.BDL.HasType.eraseDim {Θ : ConceptEnv} {Δ : DeclEnv} {G : Grant} {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : HasType Θ Δ G Γ e τ) :
    HasType Θ.eraseDim Δ.eraseDim G (Γ.map Ty.eraseDim) e.eraseDim τ.eraseDim := by
  induction h with
  | var h => exact .var (by simp [List.getElem?_map, h])
  | boolLit => exact .boolLit
  | natLit => exact .natLit
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha
  | declRef h => exact .declRef (by rw [DeclEnv.tyView_eraseDim, h]; rfl)
  | rep hb _ ih => exact .rep (by simp [ConceptEnv.eraseDim, hb]) ih
  | mk hg hb _ ih => exact .mk hg (by simp [ConceptEnv.eraseDim, hb]) ih
  | prim => exact (Prim.ty_eraseDim _) ▸ HasType.prim
  | delay hd _ _ ihi ihe => exact .delay (Ty.eraseDim_data hd) ihi ihe
  | sync hd _ _ ihi ihe => exact .sync (Ty.eraseDim_data hd) ihi ihe
  | fold _ _ _ ihf ihz ihl => exact .fold ihf ihz ihl

/-- **Counterexample B.**  After erasure `length + time` is accepted, and the
    erased environment cannot tell the sensors apart. -/
theorem counterexampleB_baseline_accepts_length_plus_time :
    HasType ConceptEnv.empty Δdim.eraseDim Grant.none [] lenPlusTime.eraseDim (.q Dim.zero) ∧
    dLen.eraseDim.interface = dTime.eraseDim.interface := by
  decide

/-! ## Units are surface -/

/-- A unit: a dimension and a scale factor relative to the canonical unit
    (integers suffice for the experiment). -/
structure Unit where
  dim   : Dim
  scale : Nat
  deriving DecidableEq, Repr

def meter      : Unit := ⟨Dim.Length, 1000⟩   -- canonical unit: millimetre
def centimeter : Unit := ⟨Dim.Length, 10⟩
def millimeter : Unit := ⟨Dim.Length, 1⟩

/-- Elaboration of a surface literal `n u` to a core dimensioned literal. -/
def elabUnit (n : Nat) (u : Unit) : Expr := .prim (.lit u.dim (n * u.scale))

/-- **`unit_scaling_preserves_dimension`.**  Every unit literal is typed by
    its unit's dimension, in any environment — `Unit` never reaches `Ty`. -/
theorem unit_scaling_preserves_dimension (Θ : ConceptEnv) (Δ : DeclEnv) (G : Grant) (n : Nat) (u : Unit) :
    HasType Θ Δ G [] (elabUnit n u) (.q u.dim) :=
  .prim

/-- Changing the unit changes the *value*, never the *type*: `5 cm` and
    `5 m` are different core terms of the same type. -/
theorem unit_change_is_value_not_type :
    elabUnit 5 centimeter ≠ elabUnit 5 meter ∧
    infer ConceptEnv.empty .empty Grant.none [] (elabUnit 5 centimeter)
      = infer ConceptEnv.empty .empty Grant.none [] (elabUnit 5 meter) := by
  decide

/-- Same-dimension quantities in different units add after elaboration —
    unit reconciliation is scale arithmetic done by the elaborator. -/
example : HasType ConceptEnv.empty .empty Grant.none []
    (.app (.app (.prim (.add Dim.Length)) (elabUnit 5 centimeter)) (elabUnit 2 meter)) (.q Dim.Length) := by
  decide

/-! ## Counterexample C — semantic identity is independent of dimension -/

/-- Tilt and MotorAngle are both angles; Brightness is dimensionless. -/
def Θdim : ConceptEnv := fun s =>
  if s = cTilt then some (.q Dim.Angle)
  else if s = cMotor then some (.q Dim.Angle)
  else if s = cBright then some (.q Dim.zero)
  else none

theorem Θdim_wf : Θdim.WF := by
  intro s R h
  unfold Θdim at h
  split at h
  · cases h; exact ⟨trivial, trivial⟩
  · split at h
    · cases h; exact ⟨trivial, trivial⟩
    · split at h
      · cases h; exact ⟨trivial, trivial⟩
      · exact nomatch h

/-- **`same_dimension_does_not_imply_same_semantic_identity`.**  Same
    representation, distinct types, direct wire still rejected — with
    dimensions present. -/
theorem same_dimension_does_not_imply_same_semantic_identity :
    Θdim cTilt = Θdim cMotor ∧ Tilt ≠ MotorAngle ∧
    ¬ WellFormedDecl trivEv Θdim ΔA_bad [] aMotorWire := by
  decide

/-! ## A semantic mapping realized by a dimensioned formula

    brightness = tilt * gain,   gain : q (0 − Angle)   so that   q Angle · q (0 − Angle) = q 0
-/

def gainTy : Ty := .q (Dim.zero.sub Dim.Angle)
def dGain : DesignDecl := ⟨gainDecl, ⟨gainTy, []⟩, none⟩
def Δformula : DeclEnv := .ofList [dTilt, dGain]

/-- `λx. mk bright (rep x * gain)` -/
def tiltTimesGain : Expr :=
  .lam Tilt (.mk cBright
    (.app (.app (.prim (.mul Dim.Angle (Dim.zero.sub Dim.Angle))) (.rep (.var 0))) (.declRef gainDecl)))

/-- **`explicit_semantic_mapping_can_use_representation_formula`** (dimensioned
    form): typed under the mapping's own grant; the product's dimension
    `Angle + (0 − Angle) = 0` matches Brightness's representation. -/
theorem explicit_semantic_mapping_uses_dimensioned_formula :
    HasType Θdim Δformula (Grant.of (.arr Tilt Brightness)) [] tiltTimesGain (.arr Tilt Brightness) := by
  decide

/-- A dimension error *inside* the mapping is caught by the same typing:
    an angle is not a brightness representation. -/
theorem dimension_error_inside_mapping_rejected :
    ¬ HasType Θdim Δformula (Grant.of (.arr Tilt Brightness)) []
      (.lam Tilt (.mk cBright (.rep (.var 0)))) (.arr Tilt Brightness) := by
  decide

/-- And the semantic isolation still holds with dimensions: the same formula
    cannot manufacture a motor angle, although Tilt and MotorAngle share
    `q Angle`. -/
theorem shared_dimension_no_hidden_mapping :
    ¬ HasType Θdim Δformula (Grant.of (.arr Tilt Brightness)) []
      (.lam Tilt (.mk cMotor (.rep (.var 0)))) (.arr Tilt MotorAngle) := by
  decide

/-! ## Counterexample D — rebinding a representation is an edit -/

def Θdim' : ConceptEnv := fun s =>
  if s = cTilt then some (.q Dim.Length) else Θdim s

theorem representation_change_is_edit_not_refinement' :
    HasType Θdim Δformula (Grant.of (.arr Tilt Brightness)) [] tiltTimesGain (.arr Tilt Brightness) ∧
    ¬ HasType Θdim' Δformula (Grant.of (.arr Tilt Brightness)) [] tiltTimesGain (.arr Tilt Brightness) ∧
    ¬ ConceptRefines Θdim Θdim' := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have := h cTilt (.q Dim.Angle) (by decide)
  simp [Θdim'] at this
  exact absurd this (by decide)

/-- Binding a previously unbound concept, by contrast, is a refinement and
    preserves every realization (`GlobalWF.of_conceptRefines`). -/
example : ConceptRefines ConceptEnv.empty Θdim := fun _ _ h => nomatch h

/-! ## §D Dimensions as metadata or validation — not formalized

A dimension checker outside typing would have to compute the dimension of
`(length / time) * time` compositionally: `div` and `mul` *produce*
dimensions, they do not merely compare them.  Any such checker recomputes
exactly what `infer` computes from `Prim.ty`.  This is the Phase-2 Model-B
argument again and carries the same strength: the *tested* alternative —
the numeric baseline, which is erased dimensional typing
(`HasType.eraseDim`) — cannot distinguish `Length` from `Time`; a
compositional metadata checker was not formalized and is not universally
ruled out, but would duplicate `Prim.ty`-driven inference.  Engineering
preference, recorded as such. -/

end BDL.Experiments.Dimension
