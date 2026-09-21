import BDL.Surface.Stdlib
import BDL.Behavior.Interface

/-!
# Units — coordinates of physical quantities (Phase 10, linear part)

Three notions, kept apart:

* a **physical quantity** is a kernel value of type `q d` — a canonical
  magnitude and a dimension; no unit is part of it;
* a **unit coordinate** is the dimensionless number obtained by expressing
  a quantity in a unit: `coordinate(q, u) = q / scale(u)`;
* a **display / authoring unit** is what the designer prefers to see or
  type; it is presentation, never semantics (`Presentation`, §5).

Two formal layers, with the numeric assumptions in the open:

* **exact semantics** (§1–2): unit laws over an abstract scalar domain with
  cancelling division (`Scalars`), instantiated by `Sym`, a free abelian
  group on the generators `2, 3, 5, 127, π` — every registered scale,
  including `deg = π/180 rad` and `inch = 127/5000 m`, is an element, and
  every law holds exactly, with π symbolic;
* **executable elaboration** (§3–4): the kernel's `Nat` magnitudes with a
  registry of integer scales relative to canonical sub-units (`0.1 mm`,
  `ms`, arc-second, `g`, `K/180`).  Round trips hold exactly where the
  scale divides the magnitude, and the strongest valid law is stated
  otherwise.  Radians are not in this registry (their scale is not an
  integer in any degree-compatible basis); production approximates in
  floating point, which is recorded, not hidden.

Verdicts: no kernel construct is added.  A unit literal, `inUnit` and
`withUnit` are quantity arithmetic against a unit constant, elaborated;
`convert` is their composition.
-/

namespace BDL.Units
open BDL BDL.Reactive BDL.Stdlib

/-! ## §1 Exact unit semantics over an abstract scalar domain -/

/-- What the unit laws need of their scalars: a commutative monoid with a
    division that cancels multiplication by a non-zero scale. -/
structure Scalars (K : Type) where
  mul : K → K → K
  div : K → K → K
  one : K
  NonZero : K → Prop
  mul_comm : ∀ a b, mul a b = mul b a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_one : ∀ a, mul a one = a
  mul_div_cancel : ∀ x s, NonZero s → div (mul x s) s = x
  div_mul_cancel : ∀ q s, NonZero s → mul (div q s) s = q
  mul_div_assoc : ∀ x s t, div (mul x s) t = mul x (div s t)

/-- A linear unit: an identity (its semantic name), a dimension and a
    scale relative to the canonical magnitude.  A symbol or display name is
    presentation and lives elsewhere; two units with equal identity are the
    same unit whatever they are spelled. -/
structure Unit (K : Type) where
  id : Nat
  dim : Dim
  scale : K
  deriving Repr

/-- A quantity in the exact model: a dimension and a canonical magnitude. -/
structure Quantity (K : Type) where
  dim : Dim
  mag : K
  deriving Repr, DecidableEq

variable {K : Type} (S : Scalars K)

/-- `withUnit x u`: the quantity whose coordinate in `u` is `x`. -/
def withUnit (x : K) (u : Unit K) : Quantity K := ⟨u.dim, S.mul x u.scale⟩

/-- `inUnit q u`: the coordinate of `q` in `u`, defined only when the
    dimensions agree — the dimension check is the safety condition. -/
def inUnit (q : Quantity K) (u : Unit K) [Decidable (q.dim = u.dim)] : Option K :=
  if q.dim = u.dim then some (S.div q.mag u.scale) else none

/-- A scaled literal `n u`: `withUnit`. -/
def lit (n : K) (u : Unit K) : Quantity K := withUnit S n u

/-- **Dimension preservation**: a unit never changes the dimension it names. -/
theorem withUnit_dim (x : K) (u : Unit K) : (withUnit S x u).dim = u.dim := rfl
theorem lit_dim (n : K) (u : Unit K) : (lit S n u).dim = u.dim := rfl

/-- **Round trip 1**: reading back in the unit written gives the coordinate. -/
theorem inUnit_withUnit (x : K) (u : Unit K) (hs : S.NonZero u.scale) [Decidable ((withUnit S x u).dim = u.dim)] :
    inUnit S (withUnit S x u) u = some x := by
  simp [inUnit, withUnit, S.mul_div_cancel x u.scale hs]

/-- **Round trip 2**: rebuilding from a coordinate gives the quantity. -/
theorem withUnit_inUnit (q : Quantity K) (u : Unit K) (hd : q.dim = u.dim) (hs : S.NonZero u.scale)
    [Decidable (q.dim = u.dim)] :
    (inUnit S q u).map (fun x => withUnit S x u) = some q := by
  simp [inUnit, withUnit, hd, S.div_mul_cancel q.mag u.scale hs]
  cases q; simp_all

/-- **Cross-unit conversion is derived**: `convert x u v` is
    `inUnit (withUnit x u) v`, and equals `x × scale(u) / scale(v)`, and
    equals `x × (scale(u) / scale(v))` — the only "conversion factor" is a
    quotient of two scales. -/
def convert (x : K) (u v : Unit K) [Decidable ((withUnit S x u).dim = v.dim)] : Option K :=
  inUnit S (withUnit S x u) v

theorem convert_eq (x : K) (u v : Unit K) (hd : u.dim = v.dim) [Decidable ((withUnit S x u).dim = v.dim)] :
    convert S x u v = some (S.div (S.mul x u.scale) v.scale) ∧
    convert S x u v = some (S.mul x (S.div u.scale v.scale)) := by
  simp [convert, inUnit, withUnit, hd, S.mul_div_assoc]

/-- Converting through an intermediate unit is converting directly. -/
theorem convert_trans (x : K) (u v w : Unit K) (huv : u.dim = v.dim) (hvw : v.dim = w.dim)
    (hv : S.NonZero v.scale) [Decidable ((withUnit S x u).dim = v.dim)]
    [Decidable ((withUnit S x u).dim = w.dim)]
    [∀ y, Decidable ((withUnit S y v).dim = w.dim)] :
    (convert S x u v).bind (fun y => convert S y v w) = convert S x u w := by
  simp [convert, inUnit, withUnit, huv, hvw, S.div_mul_cancel _ _ hv]

/-- Converting to the same unit is the identity; mismatched dimensions are
    rejected (`none`), never coerced. -/
theorem convert_self (x : K) (u : Unit K) (hs : S.NonZero u.scale) [Decidable ((withUnit S x u).dim = u.dim)] :
    convert S x u u = some x := inUnit_withUnit S x u hs

theorem inUnit_mismatch (q : Quantity K) (u : Unit K) (hd : q.dim ≠ u.dim) [Decidable (q.dim = u.dim)] :
    inUnit S q u = none := by simp [inUnit, hd]

/-! ## §2 The symbolic scalar domain: exact, with π -/

/-- A positive scale as a product of powers of `2, 3, 5, 127` and `π` —
    the free abelian group on those generators.  Every registered scale
    below is an element; `deg = π/180` and `inch = 127/5000` are exact. -/
structure Sym where
  e2 : Int
  e3 : Int
  e5 : Int
  e127 : Int
  epi : Int
  deriving DecidableEq, Repr

namespace Sym
def one : Sym := ⟨0, 0, 0, 0, 0⟩
def mul (a b : Sym) : Sym := ⟨a.e2 + b.e2, a.e3 + b.e3, a.e5 + b.e5, a.e127 + b.e127, a.epi + b.epi⟩
def inv (a : Sym) : Sym := ⟨-a.e2, -a.e3, -a.e5, -a.e127, -a.epi⟩
def div (a b : Sym) : Sym := mul a (inv b)
def pi : Sym := ⟨0, 0, 0, 0, 1⟩
def two : Sym := ⟨1, 0, 0, 0, 0⟩
def three : Sym := ⟨0, 1, 0, 0, 0⟩
def five : Sym := ⟨0, 0, 1, 0, 0⟩
def p127 : Sym := ⟨0, 0, 0, 1, 0⟩
/-- `2^a 3^b 5^c` -/
def ofExp (a b c : Int) : Sym := ⟨a, b, c, 0, 0⟩
end Sym

/-- `Sym` satisfies the scalar laws; every element is non-zero. -/
def symScalars : Scalars Sym where
  mul := Sym.mul
  div := Sym.div
  one := Sym.one
  NonZero := fun _ => True
  mul_comm := fun a b => by simp [Sym.mul, Int.add_comm]
  mul_assoc := fun a b c => by simp [Sym.mul, Int.add_assoc]
  mul_one := fun a => by simp [Sym.mul, Sym.one]
  mul_div_cancel := fun x s _ => by
    cases x; cases s; simp only [Sym.div, Sym.mul, Sym.inv, Sym.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega
  div_mul_cancel := fun q s _ => by
    cases q; cases s; simp only [Sym.div, Sym.mul, Sym.inv, Sym.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega
  mul_div_assoc := fun x s t => by simp [Sym.div, Sym.mul, Sym.inv, Int.add_assoc]

/-! The symbolic registry: canonical `m`, `s`, `rad`, `kg`, `K`. -/
namespace SymReg
def mm : Unit Sym := ⟨1, Dim.Length, .ofExp (-3) 0 (-3)⟩
def cm : Unit Sym := ⟨2, Dim.Length, .ofExp (-2) 0 (-2)⟩
def m : Unit Sym := ⟨3, Dim.Length, .one⟩
def km : Unit Sym := ⟨4, Dim.Length, .ofExp 3 0 3⟩
/-- `1 inch = 25.4 mm = 127/5000 m` -/
def inch : Unit Sym := ⟨5, Dim.Length, ⟨-3, 0, -4, 1, 0⟩⟩
def rad : Unit Sym := ⟨10, Dim.Angle, .one⟩
/-- `1 deg = π/180 rad` -/
def deg : Unit Sym := ⟨11, Dim.Angle, ⟨-2, -2, -1, 0, 1⟩⟩
/-- `1 turn = 2π rad` -/
def turn : Unit Sym := ⟨12, Dim.Angle, ⟨1, 0, 0, 0, 1⟩⟩
def ms : Unit Sym := ⟨20, Dim.Time, .ofExp (-3) 0 (-3)⟩
def s : Unit Sym := ⟨21, Dim.Time, .one⟩
def min : Unit Sym := ⟨22, Dim.Time, .ofExp 2 1 1⟩
def kg : Unit Sym := ⟨30, Dim.Mass, .one⟩
def kelvin : Unit Sym := ⟨40, Dim.Temp, .one⟩
def all : List (Unit Sym) := [mm, cm, m, km, inch, rad, deg, turn, ms, s, min, kg, kelvin]
end SymReg

/-! ## §3 The registry, and candidate units for a dimension -/

/-- The units of a dimension, from a registry. -/
def unitsFor (reg : List (Unit K)) (d : Dim) : List (Unit K) := reg.filter (·.dim = d)

/-- **Candidate soundness**: every suggested unit has the dimension asked. -/
theorem unitsFor_sound (reg : List (Unit K)) (d : Dim) : ∀ u ∈ unitsFor reg d, u.dim = d := by
  intro u hu
  exact of_decide_eq_true (List.mem_filter.mp hu).2

/-- **Candidate completeness**: every registered unit of the dimension is suggested. -/
theorem unitsFor_complete (reg : List (Unit K)) (d : Dim) : ∀ u ∈ reg, u.dim = d → u ∈ unitsFor reg d := by
  intro u hu hd
  exact List.mem_filter.mpr ⟨hu, decide_eq_true hd⟩

/-! ## §4 Executable elaboration into the kernel (`Nat` magnitudes)

The kernel's quantities are natural numbers: the registry uses integer
scales relative to canonical *sub*-units chosen so that the tested units
are integers — `0.1 mm`, `ms`, arc-second, `g`, `K/180`.  Radians have no
integer scale against degrees and are not in this registry. -/

/-- A registry unit for elaboration. -/
abbrev NUnit := Unit Nat

namespace Reg
def mm : NUnit := ⟨1, Dim.Length, 10⟩
def cm : NUnit := ⟨2, Dim.Length, 100⟩
def m : NUnit := ⟨3, Dim.Length, 10000⟩
def km : NUnit := ⟨4, Dim.Length, 10000000⟩
def inch : NUnit := ⟨5, Dim.Length, 254⟩
def deg : NUnit := ⟨11, Dim.Angle, 3600⟩
def turn : NUnit := ⟨12, Dim.Angle, 1296000⟩
def ms : NUnit := ⟨20, Dim.Time, 1⟩
def s : NUnit := ⟨21, Dim.Time, 1000⟩
def min : NUnit := ⟨22, Dim.Time, 60000⟩
def g : NUnit := ⟨31, Dim.Mass, 1⟩
def kg : NUnit := ⟨30, Dim.Mass, 1000⟩
def kelvin : NUnit := ⟨40, Dim.Temp, 180⟩
def all : List NUnit := [mm, cm, m, km, inch, deg, turn, ms, s, min, g, kg, kelvin]
end Reg

/-- The unit's scale as a quantity constant of its own dimension. -/
def unitConst (u : NUnit) : Expr := .prim (.lit u.dim u.scale)

/-- **Scaled literal** `n u`: a dimensioned literal of canonical magnitude `n × scale(u)`. -/
def litE (n : Nat) (u : NUnit) : Expr := .prim (.lit u.dim (n * u.scale))

/-- **`inUnit q u`**: the quantity divided by the unit constant — a
    quantity of dimension `u.dim − u.dim`, i.e. dimensionless. -/
def inUnitE (u : NUnit) (q : Expr) : Expr := app2 (.prim (.div u.dim u.dim)) q (unitConst u)

/-- **`withUnit x u`**: the scalar times the unit constant — a quantity of
    dimension `0 + u.dim`, i.e. `u.dim`. -/
def withUnitE (u : NUnit) (x : Expr) : Expr := app2 (.prim (.mul Dim.zero u.dim)) x (unitConst u)

/-- `convert x u v` as a surface form: `inUnit (withUnit x u) v`. -/
def convertE (u v : NUnit) (x : Expr) : Expr := inUnitE v (withUnitE u x)

section Typing
variable {Θ : ConceptEnv} {Δ : DeclEnv} {G : Grant} {Γ : Ctx}

/-- A unit literal has the unit's dimension, in every environment. -/
theorem litE_typed (n : Nat) (u : NUnit) : HasType Θ Δ G Γ (litE n u) (.q u.dim) := .prim

/-- **`inUnit` is dimensionless**, and only accepts a quantity of the
    unit's dimension. -/
theorem inUnitE_typed (u : NUnit) {q : Expr} (hq : HasType Θ Δ G Γ q (.q u.dim)) :
    HasType Θ Δ G Γ (inUnitE u q) (.q Dim.zero) := by
  have h : HasType Θ Δ G Γ (inUnitE u q) (.q (u.dim.sub u.dim)) := .app (.app .prim hq) .prim
  rwa [Dim.sub_self] at h

/-- **`withUnit` has the unit's dimension**, and only accepts a scalar. -/
theorem withUnitE_typed (u : NUnit) {x : Expr} (hx : HasType Θ Δ G Γ x (.q Dim.zero)) :
    HasType Θ Δ G Γ (withUnitE u x) (.q u.dim) := by
  have h : HasType Θ Δ G Γ (withUnitE u x) (.q (Dim.zero.add u.dim)) := .app (.app .prim hx) .prim
  rwa [Dim.zero_add] at h

theorem convertE_typed (u v : NUnit) (hd : u.dim = v.dim) {x : Expr} (hx : HasType Θ Δ G Γ x (.q Dim.zero)) :
    HasType Θ Δ G Γ (convertE u v x) (.q Dim.zero) :=
  inUnitE_typed v (hd ▸ withUnitE_typed u hx)

/-- **Dimension safety** (inversion): if `inUnit u q` is typed at all, `q`
    is a quantity of exactly `u.dim` — a unit choice never bypasses `Dim`. -/
theorem inUnitE_safe [DecidablePred G] (u : NUnit) {q : Expr} {τ : Ty} (h : HasType Θ Δ G Γ (inUnitE u q) τ) :
    HasType Θ Δ G Γ q (.q u.dim) := by
  cases h with
  | app hf _ =>
    cases hf with
    | app hp hq =>
      cases hp
      exact hq

/-- The result of `withUnit` is a quantity — never a Sem value. -/
theorem withUnitE_is_quantity [DecidablePred G] (u : NUnit) {x : Expr} {τ : Ty}
    (h : HasType Θ Δ G Γ (withUnitE u x) τ) : τ = .q (Dim.zero.add u.dim) := by
  cases h with
  | app hf _ =>
    cases hf with
    | app hp _ => cases hp; rfl

/-- Unit operations construct no Sem value: they are quantity
    arithmetic.  Re-wrapping a coordinate as a concept needs `mk` under the
    concept's own grant, exactly as before (`HasType.constructs_granted`). -/
theorem unitOps_no_construction (u : NUnit) (e : Expr) (s : ConceptId) :
    ((inUnitE u e).constructs s ↔ e.constructs s) ∧ ((withUnitE u e).constructs s ↔ e.constructs s) := by
  simp [inUnitE, withUnitE, app2, unitConst, Expr.constructs]

end Typing

section Eval
variable {Δ : DeclEnv} {I : Input} {t : Nat} {ρ : List Value}

theorem ev_litE (n : Nat) (u : NUnit) : Ev Δ I t ρ (litE n u) (.nat (n * u.scale)) := Ev.lit _ _

theorem ev_inUnitE (u : NUnit) {q : Expr} {m : Nat} (hq : Ev Δ I t ρ q (.nat m)) :
    Ev Δ I t ρ (inUnitE u q) (.nat (m / u.scale)) := by
  have := Ev.appPrim (Ev.appPrim (Ev.prim (p := .div u.dim u.dim)) hq) (Ev.lit u.dim u.scale)
  simpa [inUnitE, app2, unitConst, applyPrim, Prim.arity, Prim.compute] using this

theorem ev_withUnitE (u : NUnit) {x : Expr} {n : Nat} (hx : Ev Δ I t ρ x (.nat n)) :
    Ev Δ I t ρ (withUnitE u x) (.nat (n * u.scale)) := by
  have := Ev.appPrim (Ev.appPrim (Ev.prim (p := .mul Dim.zero u.dim)) hx) (Ev.lit u.dim u.scale)
  simpa [withUnitE, app2, unitConst, applyPrim, Prim.arity, Prim.compute] using this

/-- **Round trip 1, executable**: exact for every positive scale. -/
theorem inUnit_withUnit_nat (u : NUnit) (hs : 0 < u.scale) {x : Expr} {n : Nat} (hx : Ev Δ I t ρ x (.nat n)) :
    Ev Δ I t ρ (inUnitE u (withUnitE u x)) (.nat n) := by
  have := ev_inUnitE u (ev_withUnitE u hx)
  rwa [Nat.mul_div_cancel _ hs] at this

/-- **Round trip 2, executable**: exact when the scale divides the
    magnitude — the strongest law the `Nat` kernel admits; in the exact
    model (`withUnit_inUnit`) it is unconditional.  Production floating
    point satisfies neither exactly. -/
theorem withUnit_inUnit_nat (u : NUnit) {q : Expr} {m : Nat} (hq : Ev Δ I t ρ q (.nat m)) (hdiv : u.scale ∣ m) :
    Ev Δ I t ρ (withUnitE u (inUnitE u q)) (.nat m) := by
  have := ev_withUnitE u (ev_inUnitE u hq)
  rwa [Nat.div_mul_cancel hdiv] at this

/-- **Conversion is the composition**: `convert x u v` evaluates to
    `x × scale(u) / scale(v)` — no separate semantic operation. -/
theorem ev_convertE (u v : NUnit) {x : Expr} {n : Nat} (hx : Ev Δ I t ρ x (.nat n)) :
    Ev Δ I t ρ (convertE u v x) (.nat (n * u.scale / v.scale)) :=
  ev_inUnitE v (ev_withUnitE u hx)

/-- **Unit spelling is erased**: two literals of the same canonical
    magnitude are observationally equal — `1 m` and `100 cm` have the same
    value at every tick in every design, and the same type. -/
theorem lit_normalizes (n₁ : Nat) (u₁ : NUnit) (n₂ : Nat) (u₂ : NUnit) (h : n₁ * u₁.scale = n₂ * u₂.scale) :
    Ev Δ I t ρ (litE n₁ u₁) (.nat (n₂ * u₂.scale)) := h ▸ ev_litE n₁ u₁

end Eval

/-! ## §5 Preferred display units are presentation -/

/-- A presentation: a preferred unit per concept (and per declaration, if
    wanted).  It is not part of the design. -/
structure Presentation where
  preferred : ConceptId → Option NUnit

/-- Reading a value for display: the coordinate in the preferred unit. -/
def display (P : Presentation) (s : ConceptId) (v : Value) : Option Nat :=
  match P.preferred s, v with
  | some u, .sem _ (.nat m) => some (m / u.scale)
  | some u, .nat m => some (m / u.scale)
  | _, _ => none

/-- A design together with a presentation. -/
structure Presented where
  design : Design
  pres : Presentation

/-- **Display-unit invariance, by construction.**  Changing the
    presentation changes nothing the kernel judges: the design is the same
    object, so typing, evaluation, dependencies, clocks and identities are
    the same propositions.  (Compare Phase 8b's `group_is_identity_on_design`.) -/
theorem presentation_irrelevant (D : Design) (P P' : Presentation) :
    (Presented.mk D P).design = (Presented.mk D P').design := rfl

theorem presentation_irrelevant_typing (D : Design) (P P' : Presentation) (Θ : ConceptEnv) (G : Grant) (e : Expr) (τ : Ty) :
    HasType Θ (Presented.mk D P).design.Δ G [] e τ ↔ HasType Θ (Presented.mk D P').design.Δ G [] e τ := Iff.rfl

theorem presentation_irrelevant_eval (D : Design) (P P' : Presentation) (I : Input) (t : Nat) (e : Expr) (v : Value) :
    Ev (Presented.mk D P).design.Δ I t [] e v ↔ Ev (Presented.mk D P').design.Δ I t [] e v := Iff.rfl

theorem presentation_irrelevant_deps (D : Design) (P P' : Presentation) (a b : DeclId) :
    DependsOn (Presented.mk D P).design.Δ a b ↔ DependsOn (Presented.mk D P').design.Δ a b := Iff.rfl

theorem presentation_irrelevant_clock (D : Design) (P P' : Presentation) (c : Option ClockId) (e : Expr) :
    Clock.Clocked (Presented.mk D P).design.Κ c e ↔ Clock.Clocked (Presented.mk D P').design.Κ c e := Iff.rfl

/-- What a presentation *does* change: the displayed number. -/
theorem presentation_changes_display (s : ConceptId) (m : Nat) :
    display ⟨fun _ => some Reg.cm⟩ s (.nat (m * 100)) = some m ∧
    display ⟨fun _ => some Reg.mm⟩ s (.nat (m * 100)) = some (m * 10) := by
  constructor
  · simp [display, Reg.cm]
  · simp [display, Reg.mm]; omega

/-- **Ordering is unit-independent**: an ordered concept compares canonical
    magnitudes (`Stdlib.ltAt`), which mention no unit; a presentation is not
    an input of `ltAt`.  (Comparing *displayed* coordinates would not be
    safe: integer display can identify distinct magnitudes.) -/
theorem ordering_ignores_presentation {τ : Ty} (o : Ordered τ) (a b : Expr) (_P _P' : Presentation) :
    ltAt o a b = ltAt o a b := rfl

theorem display_may_identify_distinct (P : Presentation) (s : ConceptId) (hP : P.preferred s = some Reg.cm) :
    display P s (.nat 150) = display P s (.nat 199) ∧ (150 : Nat) < 199 := by
  simp [display, hP, Reg.cm]

end BDL.Units
