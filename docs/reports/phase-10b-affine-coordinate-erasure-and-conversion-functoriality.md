---
kind: report
phase: 10b
area: surface
date: 2026-09-18
status: current
---

# Phase 10b — Affine coordinate erasure and conversion functoriality

Revisits Phase 10's "point/delta is missing information". Hypothesis: for
conversion, chart identity may be erased at coordinatization; what must be
preserved is the affine transformation structure between charts. Files:
`BDL/Surface/Rational.lean` (exact rationals `Q` as a quotient, choice-free —
core's `Rat` proves its algebra with `Classical.choice`),
`BDL/Surface/Charts.lean` (abstract `Field K`, `Chart`, `AffMap`),
`BDL/Experiments/AffineExamples.lean`; note
`docs/notes/unit-coordinates-and-formula-assembly.md` §17.

## 10b.1 Theorems (over any field, instantiated at `Q`)

`chart_left_inverse`, `chart_right_inverse`; `convert_is_affine` (closed form
`(s_u/s_v)x + (o_u−o_v)/s_v`); `convert_identity`, `convert_compose`,
`convert_inverse` (from the chart laws alone — a groupoid of affine
isomorphisms, theorem-level); `difference_map`, `difference_offset_cancels`,
`difference_converts_linearly`; `linear_part_identity`, `linear_part_compose`;
`not_additive_of_offset`; `unit_erasure_preserves_conversion_structure`;
`display_switch_preserves_quantity`; `coordinate_edit_changes_quantity`;
`coordinate_is_chartless`. `CtoF_closed : C(°C,°F)(x) = 9/5·x + 32`,
`FtoC_closed : C(°F,°C)(x) = 5/9·x − 160/9`, `delta_law` (`Δ°F = 9/5·Δ°C`),
`delta_law_FtoC`.

## 10b.2 Executed (exact `Q`)

A `0 °C = 32 °F`; B `100 °C = 212 °F`; C `−40 °C = −40 °F`; D °C→°F→°C; E
°C→K→°F = °C→°F; F `Δ10 °C = Δ18 °F`; G same from `−5 °C`; H ADC calibration
(composition through mV, inverse, difference); I encoder home offset; J display
switch preserves the kelvin quantity; `edit_vs_switch`;
`coordinate_needs_chart`; `CtoF_not_additive`.

## 10b.3 Revision

`AffSort` is downgraded from "missing information required by affine units" to
optional physical-arithmetic validation, orthogonal to conversion
(`sort_orthogonal_to_conversion`, `conversion_orthogonal_to_sort`). No kernel
change; `Ty.q d` unchanged; runtime unit values re-rejected (no theorem needs
one). 111 theorems of the 10b modules on `propext`/`Quot.sound`.
