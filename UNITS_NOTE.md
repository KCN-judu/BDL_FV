# Unit Coordinates and Formula-Assembly Semantics

*A formal note on Phases 10 and 10b of the BDL development (`BDL/Surface/Units.lean`,
`Composer.lean`, `Affine.lean`; `BDL/Experiments/UnitExamples.lean`),
followed by production guidance for `KCN-judu/BDL`.*

## 1. Baseline, confirmed

Before this phase: units were surface-level scaling (D-32,
`unit_scaling_preserves_dimension`, `unit_change_is_value_not_type`);
`q d` is the semantic type; the unit is not part of `Ty`; only linear
scaling was modelled; affine units were not modelled. None of these facts
was changed before the alternatives were compared. One kernel *datum*
changed: `Dim` gained `mass` and `temp` exponents (production already
carries eight SI bases; the base set is not a kernel decision, the group
structure is).

## 2. Three notions, kept apart

| notion | formal object | layer |
|---|---|---|
| physical quantity | a value of type `q d`: a canonical magnitude and a dimension | kernel |
| unit coordinate | `inUnit q u = q / scale(u)`, a dimensionless number | surface elaboration |
| display / authoring unit | `Presentation.preferred : SemanticId → Option Unit` | presentation |

A unit itself is `⟨id, dim, scale⟩` in a registry; its symbol is not part
of it (§4). `withUnit x u = x × scale(u)` builds a quantity from a
coordinate; a scaled literal `n u` *is* `withUnit n u`.

## 3. Models compared (§2 of the brief)

| model | verdict | reason |
|---|---|---|
| A literal-only elaboration | insufficient alone | a coordinate (`inUnit`) is needed for display, normalization (`tilt` in degrees ÷ 90) and export; it is not a literal |
| B `inUnit(q, u) : Scalar` by elaboration | **adopted** | it is `div q (lit u.dim scale(u))` — kernel arithmetic against a unit *constant*; typed `q (d − d) = q 0` (`inUnitE_typed`); rejects a wrong dimension (`inUnitE_safe`, `exI`) |
| C `withUnit(x, u) : Q[d]` by elaboration | **adopted** | it is `mul x (lit u.dim scale(u))`, typed `q (0 + d)` (`withUnitE_typed`); never a `sem` (`withUnitE_is_quantity`) |
| D first-class runtime units | rejected | no tested case delays, syncs, stores or compares a unit; a dropdown is not a value (§15) |
| E units in quantity types | rejected | `1 m` and `100 cm` would have different types while being the same quantity (`exA`: same type, equal values) |
| F kernel conversion primitive | rejected | `convert x u v = inUnit (withUnit x u) v = x × scale(u)/scale(v)` (`convert_eq`, `ev_convertE`); transitive (`convert_trans`); nothing to add |

**Q1 answer: no new kernel construct.** Every unit operation is
quantity arithmetic against a constant, elaborated.

## 4. Two formal layers and the numeric domain (§31–33)

* **Exact semantics** (`Scalars K`, `Sym`). The unit laws are proved over
  an abstract scalar domain with cancelling division, and instantiated by
  `Sym` — the free abelian group on the generators `2, 3, 5, 127, π`. Every
  registered scale is an element, exactly: `deg = π/180 rad =
  π·2⁻²·3⁻²·5⁻¹`, `inch = 127/5000 m`. Round trips (`inUnit_withUnit`,
  `withUnit_inUnit`), conversion (`convert_eq`, `convert_trans`,
  `convert_self`) and mismatch rejection (`inUnit_mismatch`) hold with π
  symbolic: `90 deg` in radians is `π/2` (`exD`), not 1.5707….
* **Executable elaboration** (`Nat`). The kernel's magnitudes are natural
  numbers; the registry uses integer scales relative to canonical
  sub-units (`0.1 mm`, `ms`, arc-second, `g`, `K/180`) so that mm, cm, m,
  km, inch, deg, turn, ms, s, min, g, kg, K are exact. Round trip 1 is
  exact for every positive scale (`inUnit_withUnit_nat`); round trip 2 is
  exact when the scale divides the magnitude (`withUnit_inUnit_nat`) —
  the strongest law integer division admits. Radians are *not* in this
  registry: their scale is not an integer in any degree-compatible basis.
* **Production** uses IEEE doubles with radians canonical (ADR-0011,
  `bdl-elab::units`): neither round trip holds exactly there. This is an
  approximation of the exact model, and the note says so rather than
  hiding it.

## 5. What is proved (linear part)

| law | theorem | layer |
|---|---|---|
| a unit literal has its unit's dimension | `litE_typed`, `lit_dim` | both |
| `inUnit` is dimensionless and only accepts its dimension | `inUnitE_typed`, `inUnitE_safe` | kernel elaboration |
| `withUnit` has the unit's dimension, never a concept | `withUnitE_typed`, `withUnitE_is_quantity` | kernel elaboration |
| unit spelling is erased: same magnitude ⇒ same value and type | `lit_normalizes`, `exA` | kernel elaboration |
| round trips | `inUnit_withUnit`, `withUnit_inUnit` (exact); `inUnit_withUnit_nat`, `withUnit_inUnit_nat` (Nat, divisibility) | both |
| conversion is derived | `convert_eq`, `convert_trans`, `convert_self`, `ev_convertE` | both |
| candidate units sound and complete | `unitsFor_sound`, `unitsFor_complete` | registry |
| unit operations construct nothing | `unitOps_no_construction` | kernel elaboration |
| display unit irrelevant to typing, evaluation, dependencies, clocks | `presentation_irrelevant_*` (by construction, `rfl`) | presentation |
| ordering ignores presentation | `ordering_ignores_presentation`; `display_may_identify_distinct` warns against comparing displayed coordinates | presentation |

## 6. Nominal concepts and the representation boundary (§11–12)

`inUnit(TiltValue, deg)` is `inUnit` of `rep tilt`: the coordinate of a
concept goes through `rep`, which is free everywhere, and produces a
scalar. Rebuilding a concept from a coordinate requires `mk` under that
concept's grant, exactly as before. Executed (`nominal_distinct`): Tilt
and MotorAngle are both readable in degrees; `withUnit (inUnit tilt)` is
a `q Angle`, not a `MotorAngle`; `mk MotorAngle …` without the grant is
rejected; `inUnit` on a concept *without* `rep` is rejected. Brightness
and Opacity likewise (`brightness_opacity_distinct`). So unit operations
are not a second representation escape hatch: they add no observation
power beyond `rep` and no construction power at all
(`unitOps_no_construction`). Unit compatibility is not identity.

Ordered concepts (9c) compare canonical magnitudes through `rep`;
presentation is not an input of `ltAt` (`ordering_unit_independent`).

## 7. The realistic formula (§13)

`Tilt → Brightness`: `tilt / (90 deg)` and `inUnit(tilt, deg) / 90` are
both dimensionless and evaluate equal for every tilt
(`normalizations_agree`, `exF`). The representation-aware form is the
second: it names the unit the designer thinks in and keeps the divisor a
plain number. The first is equally well typed. Neither changes the
concept: both consume `rep tilt`; the result is wrapped as Brightness by
the block's own signature (ADR-0013).

## 8. Formula Composer (§16–21, §42)

`PExpr` = holes, known operands by dimension, `add/sub/mul/div`. `check`
is bottom-up; `solve` pushes an expected dimension down by the local
rules of each operator in the `Dim` group (`add/sub`: both sides get `r`;
`mul`: the other side gets `r − d`; `div`: numerator `r + d`, denominator
`d − r`). It is deterministic and one-pass; a product of two holes is
*unsolved*, not searched (`exH`). **Proved for the whole fragment**:

* `solve_sound` — filling holes as solved makes the expression check at
  the expected dimension;
* `solve_complete` — any filling that checks agrees with the solution
  (one-hole equations in an abelian group have one solution);
* `candidates_sound`, `candidates_complete`, `slot_sound` — the units
  offered for a hole are exactly the registered units of its solved
  dimension; `refCandidates_sound` for declaration references.

Executed: `? / (1 s) : Speed ⇒ ? : Length` with candidates mm, cm, m, km,
inch (`exG`); `Force × ? : Torque ⇒ ? : Length` (`exH`); the explanation
`Speed = [Length] / [Time]` as slots (`speed_slot`). No unification, no
symbolic algebra beyond the group laws: **Q5 and Q6 are yes.**

## 9. Display units and persistence (§22–24)

`Presentation` is a separate object; a design with a presentation is a
pair, and every kernel judgment of the pair is literally the judgment of
the design (`presentation_irrelevant_*`, `exJ`). What changes is the
displayed number (`presentation_changes_display`). **Q7: yes.**

Design guidance (not a theorem):

| datum | class | where |
|---|---|---|
| source literal unit (`90 deg`) | semantic source — its scale enters elaboration | the formula text |
| concept preferred display unit (`Tilt shown as deg`) | authoring metadata — never enters elaboration | the concept's inspector record, beside display name |
| simulation-input display unit | presentation/UI state | the session |

## 10. Affine units (§25–29)

* **K**: `0 °C = 273.15 K` — no scale produces it from 0
  (`celsius_not_linear`); the same for °F. In the `K/180` basis the
  scales and offsets are integers and `0 °C = 32 °F`, `100 °C = 212 °F`
  (`scales_agree`, `exK`).
* Affine **literals and coordinates** elaborate exactly with no kernel
  change: `n °C ↦ lit Temp (n·s + off)`, `inUnit°C q ↦ (q − off)/s`
  (`affLitE_typed`, `affInUnitE_typed`, `affine_roundtrip_ev`); conversion
  is derived (`convert_examples`).
* **L**: what breaks is arithmetic on *absolute* values. `20 °C − 10 °C
  = 10 K` (`delta_is_linear`), but `10 °C + 10 °C` is well typed at
  `q Temp` and reads `293 °C` (`sum_of_points_is_not_a_point`,
  `sum_well_typed`). The kernel's dimension cannot separate a point on
  the scale from a difference. The missing information is a *sort*
  (`AffSort`: point / delta) with the affine-space rules (`affAdd`,
  `affSub`, `sort_decides`), and the Composer cannot offer only
  difference units for a delta slot from the dimension alone
  (`delta_candidates_need_sort`).
* Models: A (defer entirely) is too weak — conversion is already safe;
  B (affine coordinate) is what elaboration does; C (point vs difference)
  is the information that is missing and is **deferred** as a surface
  sort, not a kernel type; D (°C as display over kelvin semantics) is
  exactly the persistence recommendation; E (a stdlib rule) adds nothing
  over B. **Q8/Q9**: conversion and display of °C are safe now;
  *arithmetic* on °C values needs the point/delta sort and must remain
  deferred until it exists. `Dim` minimality is untouched.

## 11. Verdicts

| construct | verdict | claim |
|---|---|---|
| unit as kernel type | REMOVE | `exA`: unit-indexed types would split one quantity |
| unit as runtime value | REMOVE | no case delays, syncs, stores or compares a unit |
| scaled literal | KEEP IN SURFACE-DESUGAR | `litE_typed`, `lit_normalizes` |
| coordinate extraction `inUnit` | KEEP IN SURFACE-DESUGAR | kernel `div` against a unit constant; `inUnitE_typed`, `inUnitE_safe` |
| quantity construction `withUnit` | KEEP IN SURFACE-DESUGAR | kernel `mul` against a unit constant |
| explicit `convert` | KEEP IN STANDARD LIBRARY (convenience) | the composition, `convert_eq` |
| unit registry | KEEP IN SURFACE (elaboration data) | `unitsFor_sound/_complete` |
| preferred display unit | MOVE TO AUTHORING/UI | `presentation_irrelevant_*` |
| partial-expression holes | KEEP IN SURFACE (editor) | `PExpr`, no execution |
| local dimension inference | KEEP IN SURFACE (editor) | `solve_sound`, `solve_complete` |
| candidate unit inference | KEEP IN SURFACE (editor) | `candidates_sound/_complete` |
| affine literals / coordinates | KEEP IN SURFACE-DESUGAR | exact, `affine_roundtrip_ev` |
| affine arithmetic safety (point/delta) | DEFER | `sum_of_points_is_not_a_point`; sort not yet in the language |
| visual layout, structured components | out of scope | no formal content |

Claim strength: proved for the stated fragments; minimal among the six
models compared; executed cases A–L; no global minimality theorem.

## 12. Surface syntax (§14) — recommendation, not a theorem

Semantics fixed as above, the names are interchangeable; recommended:
`inUnit(x, deg)` for the coordinate (reads as "x in degrees"; `valueOf`
and `scalarIn` are less specific; `x as deg` suggests a cast, which it
is not), `withUnit(n, deg)` or the literal `n deg` for construction, and
no `convert` in designer syntax (`inUnit(withUnit(...))` is rarely
written by hand; the library may expose `convert` for tooling).

## 13. Diagnostics (§41)

* dimension mismatch on `inUnit`: "This value is an angle; millimetres
  measure length." (from `inUnitE_safe`: the unit's dimension vs the
  quantity's);
* empty slot: "This slot expects a length. Choose a length unit such as
  mm, cm, m, km." (from `slot`);
* dimensionless result: "The result is dimensionless." (from
  `Dim.sub_self`);
* affine: "°C is an affine temperature scale; this operation requires a
  temperature difference." (from `affAdd .point .point = none`, once the
  sort exists; until then the sum is accepted and this diagnostic cannot
  be issued — that is the deferred item);
* exponent vectors (`L¹T⁻¹`) only in the Explain view.

## 14. Production guidance for `KCN-judu/BDL`

1. **IR constructs**: none. `Ty::Q { dim }` with `Dim` as today; no unit
   type, no unit value, no conversion primitive. (If `Dim` in
   `bdl-model` lacks a base the registry needs, add the exponent, not a
   construct.)
2. **`inUnit` / `withUnit`**: elaborator forms (`bdl-elab`) producing
   `Div(q, Lit{dim, scale})` and `Mul(x, Lit{dim, scale})`; `convert` as
   a library convenience over them; the checker (`bdl-check`) needs no
   change — dimension safety is the existing `Prim.ty` rule.
3. **Registry**: a data file like `library/std/concepts.toml` — entries
   `{ id, dim, scale, offset? }` with symbols and display names as
   presentation columns; identity is the id, not the spelling; keyed
   lookup `units_for(dim)`; the current `bdl-elab::units` table is the
   seed, radians canonical in production (float), and the formal
   registries document the exactness that is lost.
4. **Source literals**: keep the spelling in the formula text (already
   so: formulas are stored as written and re-elaborated). Never store the
   canonical magnitude as the source.
5. **Preferred display units**: an authoring-metadata field of the
   concept (inspector), never read by `bdl-elab`/`bdl-check`; a
   simulation-input unit is session state.
6. **Candidate units for a hole**: Studio sends the partial expression
   and expected dimension; the daemon runs `solve` and `units_for` and
   returns the slot (`expected`, `units`) plus reference candidates by
   type — pure functions over the design snapshot, no new store.
7. **Local inference**: implement `solve` verbatim (add/sub propagate;
   mul: `r − d`; div: `r + d` / `d − r`); report two-hole operands as
   unsolved; never unify.
8. **Affine — not yet**: do not implement °C/°F arithmetic; °C/°F may be
   offered as *display* and *literal* scales over kelvin semantics only
   if the point/difference sort is also introduced; until then keep DI-7
   open and reject affine units in formulas.
9. **Design / Code / Split**: one semantic store — the formula text (and
   the concept table). The Composer edits the same text through a
   structured view; presentation preferences live beside display names;
   nothing about units is a second formula representation.

## 15. Final answers (§49)

* **Q1** No new kernel feature: same-dimension conversion is `x × scale(u) / scale(v)`, kernel arithmetic (`convert_eq`, `ev_convertE`).
* **Q2** `inUnit(q, u)` means the canonical magnitude divided by the unit's scale, defined only when `dim(q) = dim(u)` (`inUnit`, `inUnitE_safe`).
* **Q3** Yes: its type is `q (d − d) = q 0` (`inUnitE_typed`); it is a scalar and constructs nothing.
* **Q4** Yes: `withUnit` is `mul` against the unit constant (`withUnitE_typed`, `ev_withUnitE`).
* **Q5** Yes: `solve` uses only the `Dim` group and local rules, sound and complete (`solve_sound`, `solve_complete`).
* **Q6** Yes: `candidates_sound`, `candidates_complete`.
* **Q7** Yes: `presentation_irrelevant_*` (by construction); it changes the displayed number only.
* **Q8** Linear scaling cannot express an offset (`celsius_not_linear`); conversion still elaborates exactly; what breaks is the meaning of point arithmetic (`sum_of_points_is_not_a_point`), which the dimension cannot see.
* **Q9** °C conversion and display are safe now; °C arithmetic must remain deferred until a point/difference sort exists.
* **Q10** Scaled literals, `inUnit`, `withUnit`, a unit registry, `solve` + `units_for` for the Composer, presentation-level preferred units — and nothing in the IR.

## 16. Not established (Phase 10)

The exact model is stated over an abstract scalar domain and the
symbolic group; no theorem relates it to production floating point. The
`Nat` kernel truncates (speed `333` in `0.1 m/s`); the exact value is in
`Sym`. The affine sort is defined and tested as arithmetic on sorts, not
integrated into typing. Two-hole operands are outside `solve` by design.


---

## 17. Phase 10b — affine coordinate erasure and conversion functoriality

Phase 10 ended with "affine conversion works, but the point/difference
sort is missing information." Phase 10b tested the smaller hypothesis:
for *conversion*, chart-specific information is intentionally erased at
coordinatization, and what must survive is only the affine transformation
structure between charts. The hypothesis holds, and the sort is
downgraded (`BDL/Surface/Charts.lean`, `Rational.lean`,
`BDL/Experiments/AffineExamples.lean`).

### 17.1 The chart model, over an abstract field

`Chart K = ⟨scale, offset⟩` over a dimension, valid when `scale ≠ 0`;
`reconstruct u x = s_u·x + o_u`, `coord u q = (q − o_u)/s_u`. The scalar
domain is an abstract `Field K` (commutative, with inverses of non-zero
elements, negatives and fractions), instantiated by `Q`, exact rationals
built as a quotient with every law proved from `Int`'s ring laws — no
`Nat` saturation, no floating point, and no `Classical.choice` (core's
`Rat` would have brought it in).

### 17.2 What is proved

| law | theorem |
|---|---|
| chart left inverse `coord u (reconstruct u x) = x` | `chart_left_inverse` |
| chart right inverse `reconstruct u (coord u q) = q` | `chart_right_inverse` |
| conversion is affine: `C(u,v)(x) = (s_u/s_v)·x + (o_u − o_v)/s_v` | `convert_is_affine`, `convertMap` |
| identity `C(u,u) = id` | `convert_identity` |
| composition `C(v,w) ∘ C(u,v) = C(u,w)` | `convert_compose` (from the chart laws alone), `convertMap_compose` |
| inverse `C(v,u) ∘ C(u,v) = id`, both ways | `convert_inverse` |
| difference map `f(y) − f(x) = a·(y − x)` | `difference_map` |
| offset cancels `f(x+δ) − f(x) = a·δ` | `difference_offset_cancels`, `difference_converts_linearly` |
| linear-part functoriality `L(u,u) = 1`, `L(v,w)·L(u,v) = L(u,w)` | `linear_part_identity`, `linear_part_compose` |
| not additive when offset ≠ 0 | `not_additive_of_offset`, `CtoF_not_additive` |
| erasure keeps conversion structure `coord v q = C(u,v)(coord u q)` | `unit_erasure_preserves_conversion_structure` |
| display switch preserves the quantity `reconstruct v (C(u,v)(coord u q)) = q` | `display_switch_preserves_quantity`, `exJ` |
| coordinate edit changes the quantity | `coordinate_edit_changes_quantity`, `edit_vs_switch` |

Identity, composition and inverse follow from the two chart laws with no
algebra: compatible charts form a groupoid of affine isomorphisms
(theorem-level; no category-theory framework was built).

### 17.3 Celsius / Fahrenheit, exactly

Kelvin canonical: `celsius = ⟨1, 27315/100⟩`, `fahrenheit = ⟨5/9,
45967/180⟩`. Proved for every `x`: `C(°C,°F)(x) = 9/5·x + 32`
(`CtoF_closed`) and `C(°F,°C)(x) = 5/9·x − 160/9 = 5/9·(x − 32)`
(`FtoC_closed`). Executed: `0 °C = 32 °F`, `100 °C = 212 °F`,
`−40 °C = −40 °F` (`exA`–`exC`), the °C→°F→°C round trip (`exD`),
°C→K→°F equal to °C→°F (`exE`), `Δ10 °C = Δ18 °F` from two base points
(`exF`, `exG`), the linear part `9/5` and `Δ°C = 5/9·Δ°F`
(`delta_law`, `delta_law_FtoC`).

### 17.4 Not a Celsius special case

The same laws instantiate sensor calibration (`physical = a·raw + b`: a
10-bit ADC, millivolts and a calibrated reading with a 0.5 V zero —
`exH`, composition through millivolts, inverse back to raw, difference
independent of base) and an encoder with home offset (`angle = 45/512 ·
count + 30°` — `exI`). Unit conversion and calibration are one affine-map
abstraction.

### 17.5 Erasure

The coordinate is a bare scalar: `32` is a Fahrenheit coordinate of `0 °C`
and a Celsius coordinate of `32 °C` (`coordinate_needs_chart`). The
destination chart supplied to `reconstruct`/`convert` interprets it; no
runtime tag is needed, and none of the theorems requires a unit to be
`Data`, delayed, synced, stored or compared (re-audit of Phase 10's
rejection of runtime units: confirmed).

### 17.6 AffSort, revised

Conversion never takes a sort; the sort checker never takes a chart
(`sort_orthogonal_to_conversion`, `conversion_orthogonal_to_sort`, by
construction). So:

* **A** — unit conversion is complete and correct without point/delta;
* **B** — a domain checker may still use point/delta to reject `point +
  point`; that is *optional physical-arithmetic validation*, orthogonal
  to A.

Old framing: "affine conversion works, but the sort is missing
information." New framing (D-106 revised): **affine conversion is
complete as coordinate-change semantics; point/delta is additional
validation information for restricting physical arithmetic.** `Ty.q d`
is unchanged: no theorem about conversion needed a sort in the type.

### 17.7 Kernel

Nothing changed: `Ty`, `Value`, `Expr`, `delay`/`sync`, the generic
machinery. Affine conversion is compiler-known chart metadata plus scalar
affine arithmetic, already elaborable (Phase 10's `affLitE`,
`affInUnitE`).

### 17.8 Production guidance (addendum)

1. **Kernel constructs**: none.
2. **°C/°F**: compiler-known charts `⟨scale, offset⟩` per unit plus
   scalar arithmetic; `convert(x, u, v) = (s_u/s_v)·x + (o_u − o_v)/s_v`,
   with the intermediate canonical value never materialized if unwanted.
3. **Runtime tag after coordinate extraction**: none. A scalar is a
   scalar; the chart is supplied where the scalar is reinterpreted.
4. **Studio unit picker stores**: the chart identity (registry id) of the
   *authoring* unit for a literal (semantic source, in the formula text)
   and the *preferred* chart per concept (authoring metadata); never the
   canonical value as source.
5. **Switch unit, preserve value**: `x' = C(u,v)(x)`; the quantity is
   unchanged (`display_switch_preserves_quantity`).
6. **Edit coordinate**: `x ↦ x'` in the same chart changes the quantity
   (`coordinate_edit_changes_quantity`); the two interactions are
   different equations and must be different commands.
7. **Point/delta for conversion**: not required.
8. **If retained**: as a validation annotation on operations
   (`affAdd`/`affSub` over sorts of operands), in the checker layer, never
   in `Ty` or in the conversion path.
9. **Sensor calibration**: the same `Chart` abstraction (`exH`, `exI`).
10. **Property tests** (production is `f64`; the formal laws are exact):
    for registered charts `u, v, w` and sampled `x`,
    `|C(u,u)(x) − x| ≤ ε·|x|`, `|C(v,w)(C(u,v)(x)) − C(u,w)(x)| ≤ ε·|x|`,
    `|C(v,u)(C(u,v)(x)) − x| ≤ ε·|x|`, `|(C(u,v)(x+δ) − C(u,v)(x)) −
    L(u,v)·δ| ≤ ε·|δ|`, and `|reconstruct_v(C(u,v)(coord_u(q))) − q| ≤
    ε·|q|`, with `ε` a few ulps scaled by the largest coefficient; plus
    exact-rational oracles for the registered charts. Do not claim exact
    `f64` identity or composition.

### 17.9 Answers

* **Q1** No: no conversion theorem mentions `AffSort`.
* **Q2** No: `Ty.q d` unchanged.
* **Q3** Yes: the coordinate forgets chart identity, symbol, origin and scale, and `unit_erasure_preserves_conversion_structure` recovers the other coordinates.
* **Q4** The affine coordinate change `C(u,v)` (an affine map), with its linear part acting on differences — not an additive homomorphism.
* **Q5** Yes: `convert_compose`, `convertMap_compose`.
* **Q6** Yes: `convert_inverse`, both directions.
* **Q7** Yes: `difference_map`, linear part `s_u/s_v`.
* **Q8** Yes: `CtoF_closed`, `FtoC_closed`, `exA`–`exG`, with `Ty.q` untouched.
* **Q9** Yes: orthogonal by construction; optional validation.
* **Q10** Yes: `exH`, `exI` are instances of the same theorems.

Claim strength: proved over any field and instantiated exactly; executed
cases A–J; the production `f64` contract is a recommendation.
