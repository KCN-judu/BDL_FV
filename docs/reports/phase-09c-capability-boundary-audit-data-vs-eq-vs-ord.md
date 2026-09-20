---
kind: report
phase: 9c
area: core
date: 2026-09-18
status: current
---

# Phase 9c — Capability boundary audit: Data vs Eq vs Ord

Question: does "may be delayed/transported as data" imply "has meaningful
equality", and does that imply "has meaningful ordering"? Phase 9b had answered
yes to both by generalizing `lt` and `eq` to every `Data` type through a
structural order. The audit (`docs/notes/polymorphic-equation-language.md` §11)
rejects the second implication and makes the kernel smaller.

## 9c.1 Findings

| expression                                                   | verdict                             | evidence                                   |
| ------------------------------------------------------------ | ----------------------------------- | ------------------------------------------ |
| `temperature1 == / < temperature2`                           | Eq, Ord (`q d`)                     | `exI`; `q Length < q Time` still rejected  |
| `brightness1 < brightness2`                                  | Ord by _declaration_, through `rep` | `Ordered.sem`, `exA`, `exJ`                |
| `mode1 == mode2`                                             | Eq                                  | `eq_accepted`                              |
| `mode1 < mode2`                                              | **rejected**                        | `lt_rejected`, `min_mode_rejected`         |
| `pair == pair`, `list == list`, `opt == opt`                 | Eq                                  | `eq_accepted`                              |
| `pair < pair`, `list < list`, `None < Some x`, `bool < bool` | **rejected**                        | `lt_rejected`, `Cap.ord_not_data_converse` |

`Data ⇒ Eq` holds extensionally (`Cap.eq_iff_data`); `Eq ⇏ Ord`.

## 9c.2 The change

- Kernel: `lt` reverted to `lt (d : Dim)` on quantities (Phase-4 form);
  `Value.blt`/`bltList` deleted — the kernel has no structural order at all;
  `eq τ (h : τ.Data)` unchanged. `lt_only_on_quantities`.
- Surface: `Poly.Cap = data | eq | ord`, `Scheme.caps`, `Ty.ordB O Θ`
  (quantities, and concepts declared ordered in `OrdDecl` with a quantity
  representation), `Scheme.instantiate O Θ` with `instantiate_sound`;
  `Cap.ord_data` (Ord ⇒ Data), `Cap.ord_not_data_converse`.
- Stdlib: `Ordered τ` evidence (`q d` | `sem s d`), `Ordered.WF Θ`, `ltAt`
  (quantity comparison, through `rep` on a concept); `minF`, `maxF`, `clampF`,
  `inRangeF`, `inIntervalF` take `Ordered`; `containsF`/`oneOfE` keep the `Data`
  proof; `map`/`fold`/`any`/`all`/`filter` need neither. Specs restated with
  `Ordered.key` (the compared magnitude): `min_spec`, `max_spec`, `clamp_spec`,
  `inRange_spec`; `ltAt_typed`, `*_typed` under `Ordered.WF`. Comparator escape
  hatch: `minByF`, `maxByF`, `minBy_spec`, **`minBy_recovers_min`** (the
  comparator `λa b. a < b` makes `minBy` compute `min` exactly).
- Combinators admit `rep` (`Comb`); `HasType.comb_irrelevant` and
  `lib_expansion` hold Θ fixed (typing of an ordered concept's comparison reads
  its representation binding, which is write-once).

## 9c.3 Models

| model                              | verdict                                                                    |
| ---------------------------------- | -------------------------------------------------------------------------- |
| A {Data} for eq and lt             | rejected — conflates state with order                                      |
| B {Data, Eq}, lt on ordered shapes | the kernel's shape; the surface still needs Ord for concepts               |
| C {Data, Eq, Ord} closed           | **adopted at the surface**; no kernel Ord evidence needed (`rep` + `lt d`) |
| D user typeclasses                 | rejected — no case                                                         |
| E comparators only                 | kept as escape hatch; loses nothing (`minBy_recovers_min`)                 |

## 9c.4 Re-established (statements unchanged)

`Ev.det`, `MEv.det`, `reactive_total`, `multi_domain_total`, `fold_total`,
`mfold_total`, `Ev.tag_provenance`, `MEv.tag_provenance`, `Ev.pure`,
`unfolds_preserves_eval`, `generic_preserves_identity`,
`generic_preserves_dimension`, `forall_in_list`, `exists_in_list`,
`buffer_window_correspondence`, `eval_flat_to_inst`, `eval_inst_to_flat`,
`orig_iff_flat`; 178 theorems of the 9a/9b/9c modules on `propext`/`Quot.sound`.

## 9c.5 Answer

`Ty.Data` is a sufficient semantic boundary for equality and state, not for
ordering. Smallest closed split supporting all tested cases: surface {Data, Eq,
Ord} with Eq ≡ Data (today) and Ord = quantities ∪ declared-ordered concepts;
kernel: `eq τ (h : τ.Data)` and `lt d` only. Claim strength: minimal among the
tested models; no minimality theorem.
