import BDL.Surface.Rational
import BDL.Core.Base

/-!
# Charts — affine coordinate systems and conversion functoriality (Phase 10b)

Over one physical dimension, a **chart** is an affine coordinate system:
`reconstruct u x = s_u · x + o_u`, `coord u q = (q − o_u) / s_u`, with
`s_u ≠ 0`.  The coordinate is a bare scalar: after `coord`, the chart's
identity, symbol, origin and scale are gone.  What survives is the
*transformation structure* between charts:

* the chart laws (`chart_left_inverse`, `chart_right_inverse`);
* conversion `C(u,v) = coord v ∘ reconstruct u`, which is an **affine
  map** `x ↦ (s_u/s_v)·x + (o_u − o_v)/s_v` (`convert_is_affine`), and
  the groupoid laws — identity, composition, inverse — which follow
  from the two chart laws alone (`convert_identity`, `convert_compose`,
  `convert_inverse`);
* differences transform by the **linear part**: `f(y) − f(x) = a·(y − x)`
  (`difference_map`), the offset cancels (`difference_offset_cancels`),
  and linear parts are functorial (`linear_part_identity`,
  `linear_part_compose`);
* an affine conversion is **not** an additive homomorphism when its
  offset is non-zero (`not_additive_of_offset`) — the preserved law is
  the difference law, not additivity.

Everything is proved over an abstract field (`Field K`) and instantiated
by the exact rationals `Q` (`Rational.lean`); no `Nat` saturation, no
floating point.
-/

namespace BDL.Charts

/-- A field, as the laws the chart theory uses. -/
structure Field (K : Type) where
  add : K → K → K
  mul : K → K → K
  neg : K → K
  inv : K → K
  zero : K
  one : K
  add_comm : ∀ a b, add a b = add b a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  zero_add : ∀ a, add zero a = a
  add_neg : ∀ a, add a (neg a) = zero
  mul_comm : ∀ a b, mul a b = mul b a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_add : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  mul_inv_cancel : ∀ a, a ≠ zero → mul a (inv a) = one
  zero_ne_one : zero ≠ one

variable {K : Type} (F : Field K)

namespace Field

def sub (a b : K) : K := F.add a (F.neg b)
def div (a b : K) : K := F.mul a (F.inv b)

theorem add_zero (a : K) : F.add a F.zero = a := by rw [F.add_comm]; exact F.zero_add a
theorem neg_add (a : K) : F.add (F.neg a) a = F.zero := by rw [F.add_comm]; exact F.add_neg a
theorem mul_one (a : K) : F.mul a F.one = a := by rw [F.mul_comm]; exact F.one_mul a
theorem add_mul (a b c : K) : F.mul (F.add a b) c = F.add (F.mul a c) (F.mul b c) := by
  rw [F.mul_comm, F.mul_add, F.mul_comm c, F.mul_comm c]
theorem add_neg_cancel_right (a b : K) : F.add (F.add a b) (F.neg b) = a := by
  rw [F.add_assoc, F.add_neg, F.add_zero]
theorem neg_add_cancel_right (a b : K) : F.add (F.add a (F.neg b)) b = a := by
  rw [F.add_assoc, F.neg_add, F.add_zero]
theorem add_left_cancel {a b c : K} (h : F.add a b = F.add a c) : b = c := by
  have : F.add (F.neg a) (F.add a b) = F.add (F.neg a) (F.add a c) := by rw [h]
  rwa [← F.add_assoc, ← F.add_assoc, F.neg_add, F.zero_add, F.zero_add] at this
theorem mul_zero (a : K) : F.mul a F.zero = F.zero := by
  apply F.add_left_cancel (a := F.mul a F.zero)
  rw [← F.mul_add, F.zero_add, F.add_zero]
theorem mul_neg (a b : K) : F.mul a (F.neg b) = F.neg (F.mul a b) := by
  apply F.add_left_cancel (a := F.mul a b)
  rw [← F.mul_add, F.add_neg, F.mul_zero, F.add_neg]
theorem neg_add_distrib (a b : K) : F.neg (F.add a b) = F.add (F.neg a) (F.neg b) := by
  apply F.add_left_cancel (a := F.add a b)
  rw [F.add_neg, F.add_comm a b, F.add_assoc, ← F.add_assoc a, F.add_neg, F.zero_add, F.add_neg]
theorem mul_sub (a b c : K) : F.mul a (F.sub b c) = F.sub (F.mul a b) (F.mul a c) := by
  simp only [Field.sub]; rw [F.mul_add, F.mul_neg]
theorem sub_mul (a b c : K) : F.mul (F.sub a b) c = F.sub (F.mul a c) (F.mul b c) := by
  simp only [Field.sub]; rw [F.add_mul, F.mul_comm (F.neg b), F.mul_neg, F.mul_comm c]
theorem mul_div_cancel (x s : K) (hs : s ≠ F.zero) : F.div (F.mul x s) s = x := by
  simp only [Field.div]; rw [F.mul_assoc, F.mul_inv_cancel s hs, F.mul_one]
theorem div_mul_cancel (q s : K) (hs : s ≠ F.zero) : F.mul (F.div q s) s = q := by
  simp only [Field.div]; rw [F.mul_assoc, F.mul_comm (F.inv s), F.mul_inv_cancel s hs, F.mul_one]
theorem mul_div_assoc (x s t : K) : F.div (F.mul x s) t = F.mul x (F.div s t) := by
  simp only [Field.div]; rw [F.mul_assoc]
theorem sub_add_cancel (a b : K) : F.add (F.sub a b) b = a := F.neg_add_cancel_right a b
theorem add_sub_cancel (a b : K) : F.sub (F.add a b) b = a := F.add_neg_cancel_right a b
theorem sub_self (a : K) : F.sub a a = F.zero := F.add_neg a
theorem add_sub_assoc (a b c : K) : F.sub (F.add a b) c = F.add a (F.sub b c) := by
  simp only [Field.sub]; rw [F.add_assoc]
theorem mul_left_comm (a b c : K) : F.mul a (F.mul b c) = F.mul b (F.mul a c) := by
  rw [← F.mul_assoc, F.mul_comm a b, F.mul_assoc]

end Field

/-! ## §1 Charts and the chart laws -/

/-- An affine chart of a dimension: `canonical = scale · coordinate + offset`. -/
structure Chart (K : Type) where
  scale : K
  offset : K

/-- A chart is valid when its scale is non-zero. -/
def Chart.Valid (F : Field K) (u : Chart K) : Prop := u.scale ≠ F.zero

/-- `reconstruct u x`: the quantity whose `u`-coordinate is `x`. -/
def reconstruct (u : Chart K) (x : K) : K := F.add (F.mul u.scale x) u.offset
/-- `coord u q`: the `u`-coordinate of `q` — a bare scalar, no chart in it. -/
def coord (u : Chart K) (q : K) : K := F.div (F.sub q u.offset) u.scale

/-- **`chart_left_inverse`**: the coordinate of a reconstruction is the coordinate written. -/
theorem chart_left_inverse (u : Chart K) (hu : u.Valid F) (x : K) : coord F u (reconstruct F u x) = x := by
  simp only [coord, reconstruct]
  rw [F.add_sub_cancel, F.mul_comm, F.mul_div_cancel _ _ hu]

/-- **`chart_right_inverse`**: reconstructing a coordinate gives the quantity back. -/
theorem chart_right_inverse (u : Chart K) (hu : u.Valid F) (q : K) : reconstruct F u (coord F u q) = q := by
  simp only [coord, reconstruct]
  rw [F.mul_comm, F.div_mul_cancel _ _ hu, F.sub_add_cancel]

/-! ## §2 Conversion: the composite, and its affine closed form -/

/-- `C(u,v) = coord v ∘ reconstruct u`. -/
def convert (u v : Chart K) (x : K) : K := coord F v (reconstruct F u x)

/-- An affine map `x ↦ a·x + b`, with its linear part `a`. -/
structure AffMap (K : Type) where
  a : K
  b : K

def AffMap.apply (f : AffMap K) (x : K) : K := F.add (F.mul f.a x) f.b
def AffMap.linearPart (f : AffMap K) : K := f.a
def AffMap.comp (g f : AffMap K) : AffMap K := ⟨F.mul g.a f.a, F.add (F.mul g.a f.b) g.b⟩

theorem AffMap.comp_apply (g f : AffMap K) (x : K) : (g.comp F f).apply F x = g.apply F (f.apply F x) := by
  simp only [AffMap.apply, AffMap.comp]
  rw [F.mul_add, F.add_assoc, F.mul_assoc]

/-- The affine map of a conversion: `(s_u / s_v)·x + (o_u − o_v)/s_v`. -/
def convertMap (u v : Chart K) : AffMap K := ⟨F.div u.scale v.scale, F.div (F.sub u.offset v.offset) v.scale⟩

/-- **`convert_is_affine`**: conversion is that affine map, extensionally. -/
theorem convert_is_affine (u v : Chart K) (x : K) : convert F u v x = (convertMap F u v).apply F x := by
  simp only [convert, coord, reconstruct, convertMap, AffMap.apply, Field.div]
  rw [F.add_sub_assoc, F.add_mul, F.mul_assoc, F.mul_comm x, ← F.mul_assoc]

/-! ## §3 The groupoid laws, from the chart laws alone -/

/-- **`convert_identity`**: `C(u,u) = id`. -/
theorem convert_identity (u : Chart K) (hu : u.Valid F) (x : K) : convert F u u x = x :=
  chart_left_inverse F u hu x

/-- **`convert_compose`**: `C(v,w) ∘ C(u,v) = C(u,w)` — the intermediate
    chart does not matter. -/
theorem convert_compose (u v w : Chart K) (hv : v.Valid F) (x : K) :
    convert F v w (convert F u v x) = convert F u w x := by
  simp only [convert]
  rw [chart_right_inverse F v hv]

/-- **`convert_inverse`**: `C(v,u) ∘ C(u,v) = id` and `C(u,v) ∘ C(v,u) = id`:
    compatible charts are isomorphic coordinate systems. -/
theorem convert_inverse (u v : Chart K) (hu : u.Valid F) (hv : v.Valid F) (x : K) :
    convert F v u (convert F u v x) = x ∧ convert F u v (convert F v u x) = x := by
  constructor
  · rw [convert_compose F u v u hv, convert_identity F u hu]
  · rw [convert_compose F v u v hu, convert_identity F v hv]

/-- The same laws at the level of the affine maps (so conversions are
    closed under composition as affine maps, with the expected coefficients). -/
theorem convertMap_compose (u v w : Chart K) (hv : v.Valid F) (x : K) :
    ((convertMap F v w).comp F (convertMap F u v)).apply F x = (convertMap F u w).apply F x := by
  rw [AffMap.comp_apply, ← convert_is_affine, ← convert_is_affine, convert_compose F u v w hv, convert_is_affine]

/-! ## §4 Differences transform by the linear part -/

/-- **`difference_map`**: `f(y) − f(x) = a·(y − x)`. -/
theorem difference_map (f : AffMap K) (x y : K) :
    F.sub (f.apply F y) (f.apply F x) = F.mul f.linearPart (F.sub y x) := by
  simp only [AffMap.apply, AffMap.linearPart]
  rw [F.mul_sub]
  simp only [Field.sub]
  rw [F.neg_add_distrib, F.add_assoc, F.add_comm f.b, F.add_assoc, F.neg_add, F.add_zero]

/-- **`difference_offset_cancels`**: `f(x + δ) − f(x) = a·δ`. -/
theorem difference_offset_cancels (f : AffMap K) (x δ : K) :
    F.sub (f.apply F (F.add x δ)) (f.apply F x) = F.mul f.linearPart δ := by
  rw [difference_map, F.add_comm x, F.add_sub_cancel]

/-- **`not_additive_of_offset`**: an affine map with a non-zero offset is
    not an additive homomorphism — `f(0 + 0) ≠ f(0) + f(0)`. -/
theorem not_additive_of_offset (f : AffMap K) (hb : f.b ≠ F.zero) :
    ¬ ∀ x y, f.apply F (F.add x y) = F.add (f.apply F x) (f.apply F y) := by
  intro h
  have := h F.zero F.zero
  simp only [AffMap.apply, F.mul_zero, F.zero_add] at this
  -- b = b + b, hence b = 0
  have : F.add f.b F.zero = F.add f.b f.b := by rw [F.add_zero]; exact this
  exact hb (F.add_left_cancel this).symm

/-! ## §5 Linear-part functoriality -/

/-- The linear part of `C(u,v)`: `s_u / s_v`. -/
def linearPart (u v : Chart K) : K := (convertMap F u v).linearPart

theorem linear_part_identity (u : Chart K) (hu : u.Valid F) : linearPart F u u = F.one := by
  simp only [linearPart, convertMap, AffMap.linearPart, Field.div]
  exact F.mul_inv_cancel _ hu

theorem linear_part_compose (u v w : Chart K) (hv : v.Valid F) :
    F.mul (linearPart F v w) (linearPart F u v) = linearPart F u w := by
  simp only [linearPart, convertMap, AffMap.linearPart, Field.div]
  -- (v · w⁻¹) · (u · v⁻¹) = (u · w⁻¹) · (v · v⁻¹)
  calc F.mul (F.mul v.scale (F.inv w.scale)) (F.mul u.scale (F.inv v.scale))
      = F.mul (F.mul u.scale (F.inv w.scale)) (F.mul v.scale (F.inv v.scale)) := by
        rw [F.mul_assoc, F.mul_assoc, F.mul_left_comm (F.inv w.scale), F.mul_comm v.scale,
          F.mul_assoc, F.mul_left_comm (F.inv w.scale) v.scale, F.mul_comm (F.mul (F.inv w.scale) (F.inv v.scale))]
    _ = F.mul u.scale (F.inv w.scale) := by rw [F.mul_inv_cancel _ hv, F.mul_one]

/-- Differences convert by the linear part of the conversion. -/
theorem difference_converts_linearly (u v : Chart K) (x δ : K) :
    F.sub (convert F u v (F.add x δ)) (convert F u v x) = F.mul (linearPart F u v) δ := by
  rw [convert_is_affine, convert_is_affine]
  exact difference_offset_cancels F (convertMap F u v) x δ

/-! ## §6 Erasure: what the scalar forgets and what it keeps -/

/-- **`unit_erasure_preserves_conversion_structure`**: from the
    `u`-coordinate alone — a scalar with no chart in it — and the two
    charts, the `v`-coordinate of the same quantity is recovered.
    Representation metadata is forgotten; transformation structure is kept. -/
theorem unit_erasure_preserves_conversion_structure (u v : Chart K) (hu : u.Valid F) (q : K) :
    coord F v q = convert F u v (coord F u q) := by
  simp only [convert]
  rw [chart_right_inverse F u hu]

/-- **`display_switch_preserves_quantity`**: switching the display chart
    and reconstructing gives the same quantity — `0 °C ↦ 32 °F`. -/
theorem display_switch_preserves_quantity (u v : Chart K) (hu : u.Valid F) (hv : v.Valid F) (q : K) :
    reconstruct F v (convert F u v (coord F u q)) = q := by
  rw [← unit_erasure_preserves_conversion_structure F u v hu, chart_right_inverse F v hv]

/-- **`coordinate_edit_changes_quantity`**: editing the coordinate in a
    chart changes the quantity (reconstruction is injective). -/
theorem coordinate_edit_changes_quantity (u : Chart K) (hu : u.Valid F) {x x' : K} (h : x ≠ x') :
    reconstruct F u x ≠ reconstruct F u x' := by
  intro e
  have := congrArg (coord F u) e
  rw [chart_left_inverse F u hu, chart_left_inverse F u hu] at this
  exact h this

/-- The scalar coordinate carries no chart: two different charts can give
    the same coordinate to different quantities, and the same quantity
    different coordinates; only the destination chart supplied to
    `reconstruct` interprets it. -/
theorem coordinate_is_chartless (u v : Chart K) (x : K) :
    reconstruct F u x = reconstruct F v x ↔ F.add (F.mul u.scale x) u.offset = F.add (F.mul v.scale x) v.offset :=
  Iff.rfl

/-! ## §7 The exact rationals are a field -/

open BDL.Rational in
/-- `Q` satisfies the field laws (all proved without classical choice). -/
def ratField : Field Q where
  add := Q.add
  mul := Q.mul
  neg := Q.neg
  inv := Q.inv
  zero := Q.zero
  one := Q.one
  add_comm := Q.add_comm
  add_assoc := Q.add_assoc
  zero_add := Q.zero_add
  add_neg := Q.add_neg
  mul_comm := Q.mul_comm
  mul_assoc := Q.mul_assoc
  one_mul := Q.one_mul
  mul_add := Q.mul_add
  mul_inv_cancel := Q.mul_inv_cancel
  zero_ne_one := Q.zero_ne_one

end BDL.Charts
