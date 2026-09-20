---
kind: report
phase: 10
area: surface
date: 2026-09-18
status: current
---

# Phase 10 — Unit coordinates and formula-assembly semantics

Question: the smallest correct semantics for expressing one quantity in
different units, extracting a coordinate, constructing a quantity from a
coordinate, letting a structured Formula Composer infer dimensions and units for
incomplete expressions, keeping units out of type identity, and what affine
units (°C/°F) need. Files: `BDL/Surface/Units.lean`, `Composer.lean`,
`Affine.lean`, `BDL/Experiments/UnitExamples.lean`; note
`docs/notes/unit-coordinates-and-formula-assembly.md` (with the production
guidance and the ten answers). Baseline confirmed first: units surface, `q d`
semantic, units not in `Ty`, linear only, affine unsolved (FVD-0032). `Dim`
gained `mass` and `temp` exponents (data, not structure).

## 10.1 Result

**No kernel construct.** `inUnit q u = div q (lit d scale(u))` (typed
`q (d−d) = q 0`: `inUnitE_typed`; rejects other dimensions: `inUnitE_safe`),
`withUnit x u = mul x (lit d scale(u))` (typed `q d`: `withUnitE_typed`; never a
concept: `withUnitE_is_quantity`), a literal `n u = withUnit n u`;
`convert x u v = inUnit (withUnit x u) v = x·scale(u)/scale(v)` (`convert_eq`,
`convert_trans`, `ev_convertE`). Unit operations construct nothing
(`unitOps_no_construction`); on a concept they go through `rep`, and rewrapping
needs the grant (`nominal_distinct`). Models D (runtime units), E (units in
types), F (conversion primitive) rejected.

## 10.2 Numeric domain

Exact laws over an abstract `Scalars K` (round trips, conversion), instantiated
by `Sym`, the free abelian group on `2,3,5,127,π`: `90 deg = π/2 rad` exactly
(`exD`). Executable `Nat` registry with canonical sub-units (`0.1 mm`, `ms`,
arc-second, `g`, `K/180`): round trip 1 exact (`inUnit_withUnit_nat`), round
trip 2 under divisibility (`withUnit_inUnit_nat`); radians not representable
there. Production floats: approximation, stated.

## 10.3 Composer

`PExpr` holes + `check`/`solve` (local group rules) with **`solve_sound`** and
**`solve_complete`**; `candidates_sound/_complete`, `slot_sound`,
`refCandidates_sound`. `? / 1 s : Speed ⇒ Length` (`exG`);
`Force × ? : Torque ⇒ Length` (`exH`); two-hole products unsolved by design.

## 10.4 Presentation

`Presentation` separate from `Design`; `presentation_irrelevant_*` by
construction (`rfl`); `presentation_changes_display`; ordering ignores it
(`ordering_ignores_presentation`; `display_may_identify_distinct`).

## 10.5 Affine

`celsius_not_linear` (K); literals/coordinates elaborate exactly
(`affLitE_typed`, `affInUnitE_typed`, `affine_roundtrip_ev`); differences are
linear (`delta_is_linear`); `10 °C + 10 °C` well typed and equal to `293 °C`
(`sum_of_points_is_not_a_point`, `sum_well_typed`) — the point/difference sort
(`AffSort`, `affAdd`, `affSub`) is the missing information, deferred as a
surface sort; the Composer needs it to offer delta units
(`delta_candidates_need_sort`).

## 10.6 Executed cases A–L

A `1 m == 100 cm`; B `254 mm == 10 inch` (0.1 mm resolution); C 90° in degrees;
D π/2 rad symbolically; E `10 km / 5 min = 333 (0.1 m/s)`, `100/3` exactly; F
normalized tilt, two forms agree (`normalizations_agree`); G, H Composer; I time
in mm rejected; J display change, core unchanged; K, L affine. Also
`nominal_distinct`, `brightness_opacity_distinct`, `generics_after_units`
(`min(10 cm, 1 m)`, `clamp`), `ordering_unit_independent`,
`lists_products_core_types`, `speed_slot`. 87 theorems on
`propext`/`Quot.sound`.
