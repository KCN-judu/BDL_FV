---
kind: note
phase: 13
area: surface
date: 2026-09-20
status: current
---

# Source provision by device transducers — formal audit of PRP-0001 (Phase 13)

Production proposal PRP-0001 (`KCN-judu/BDL` at `876005c`, status _draft_) asks
for a construction that turns an abstract Source `s : () -> C` into a raw
peripheral reading `r : () -> R` plus a realization `s := tr(r)` taken from a
device profile, with a theorem that the design cannot tell the difference. This
note records what was tested in Lean (`BDL/Surface/Provision.lean`,
`BDL/Experiments/ProvisionExamples.lean`; 92 theorems, every one on
`propext`/`Quot.sound`, no `Classical.choice`), which of the proposal's claims
survived, which were corrected, and what remains a design decision. It is an
audit, not an acceptance.

## 1. Claims that survived unchanged

- Provision is a **construction over designs** using only existing kernel
  objects: `DesignDecl`, the environment function, `declRef`, `app`, `mk`, the
  clock environment. No `Ty` constructor, expression form, Source kind, effect,
  typing rule or clock rule (`provision`, `provisionΚ`).
- The **grant argument** (PRP theorem 1's footing): a declaration typed `sem c`
  is realized under `Grant.of (sem c) = {c}`
  (`realization_checked_under_own_grant`, `grant_of_sem`, both from
  `Satisfies`/`GlobalWF` as they stand); a profile term typed under `Grant.none`
  constructs nothing (`channel_constructs_nothing`). The executed `exC` shows
  the same `λx. mk RoomTemp x` refused under `Grant.none` and accepted under the
  Source's own grant.
- Provision is an **`EnvRefines` step** (`provision_envRefines`): each target
  keeps its id and interface and goes from unresolved to realized; `r` is new.
  The type view of every pre-existing identity is unchanged
  (`provision_tyView_eq`).
- **Causality** and **clocks** are preserved (`provision_causal`,
  `provision_wellClocked`) with `Κ r = Κ s`.
- **Transparency** in both directions (`provision_transparent`), the **trace
  abstraction** (`provision_abstracts`), the **physical outputs** unchanged
  (`provision_physicalOutput`), and the strict-refinement reading of a
  non-surjective transducer (`exE`).
- Independent provisions **commute exactly** (`provision_comm`, environment
  equality by `funext`).

## 2. Claims that were too strong, incorrect or under-specified

| PRP said                                                                                   | audit found                                                                                                                                                                                                                                                                                                                                                                                                   | replacement                                                                                                                                                                                                                                                                    |
| ------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `tr` is "a closed term such that `HasType Θ [] tr (arr raw rep)` under `Grant.none`"       | typing alone does not make `tr` a function of the raw reading: `(λk. λn. k) (delay 0 1)` is typed at `q0 -> q0` in the empty design and maps `7` to `0` at tick 0 and to `1` at tick 1 (`exD`)                                                                                                                                                                                                                | `tr.Pure` (`Expr.Pure`: no `declRef`, `delay`, `sync`). Typing in the _empty_ design already excludes `declRef` (`Channel.WF_refFree`), so purity is exactly `WF ∧ DelayFree` (`pure_iff_delayFree_of_wf`)                                                                     |
| the profile is `⟨raw, tr, rep⟩`                                                            | to _name_ the induced input without choice the profile must carry the transfer function on values, not only the term                                                                                                                                                                                                                                                                                          | `Channel = ⟨rep, tr, transfer, …, computes⟩`, `computes : ∀ v, TyVal raw v → Transduces tr v (transfer v)`; `transfer` is the data sheet, `tr` the compiled term, `computes` the per-profile coherence obligation (discharged by hand in every example)                        |
| theorem 1: "`Δ'` is globally well typed" from `GlobalWF Δ`, `Fits`, freshness              | a Source may carry **commitments**; after provision its realization must carry evidence for them, and nothing in the profile supplies it                                                                                                                                                                                                                                                                      | `provision_wf` takes `hcomm` (evidence for each target's commitments on its new realization) and `ev.Monotone` (so the other declarations' evidence survives the refinement). A Source's commitments are obligations on the profile                                            |
| theorem 4: `MEv S Δ I … e v ↔ MEv S Δ' I' … e v` for `e` "not mentioning `r`"              | provable, but only with hypotheses the PRP did not state                                                                                                                                                                                                                                                                                                                                                      | `RawInput P I'` (the raw input is typed at `r` and closure-free), `NoMention Δ r` (true of every globally well-typed design, `NoMention.of_globalWF`), and a local environment whose closures avoid `r` (true of `[]`)                                                         |
| "`e` not mentioning `r`"                                                                   | two formulations tested; both hold                                                                                                                                                                                                                                                                                                                                                                            | syntactic `r ∉ e.refs` (`provision_transparent`) and by typing — any term typed in the abstract design cannot name `r` (`typed_avoids`, `provision_transparent_typed`); transitive references are covered by `NoMention`, i.e. by `GlobalWF`                                   |
| theorem 5: "when `tr` is surjective onto `rep`'s inhabitants the two trace sets are equal" | pointwise surjectivity is an `∃` per tick; building the raw input from it is a choice principle, outside this development's axiom base; and with a **shared raw reading** pointwise surjectivity of each channel is not enough (`no_joint_witness`: `id` and `succ` from one reading, abstract `(5, 9)` has no witness)                                                                                       | equality needs a **joint section**: a raw trace `sec : Nat → Value` every channel transfers to what the abstract input gives its target (`JointSection`, `provision_exact`). For one channel a pointwise right inverse on typed values is a joint section (`JointSection.one`) |
| theorem 6: "provisioning is idempotent per Source"                                         | after provision `s` is realized, `Source Δ' s` is false and `WF Θ Δ' P` fails (`r` not fresh) — the operation is not re-applicable. The equation `P(P Δ) = P Δ` _does_ hold for the total function (`provision_idem_total`) but only because the second pass overwrites every target with the same body; a second pass with a **different** term is not a refinement (`provision_reprovision_not_refinement`) | `provision_not_reapplicable`; `provision_source_role` (the Source role moves to `r`)                                                                                                                                                                                           |
| theorem 6: "provisioning two Sources commutes"                                             | true, and stronger than expected                                                                                                                                                                                                                                                                                                                                                                              | exact environment equality under: distinct `r`, neither `r` a target of the other, disjoint targets (`provision_comm`); for a shared raw reading the assignment is a set (`provision_perm`)                                                                                    |
| theorem 7 "`provision_indistinguishable` … `consumers_indistinguishable` lifted"           | `consumers_indistinguishable` is about `A -> 1` and has nothing to do with this; the client-side fact is theorem 4 itself                                                                                                                                                                                                                                                                                     | dropped; `provision_decl_transparent` is the client statement                                                                                                                                                                                                                  |
| "`r` is the **monomorphised** Source"                                                      | BDL has rank-1 polymorphism (Phase 9b); nothing here instantiates a scheme                                                                                                                                                                                                                                                                                                                                    | _abstract Source_ / _provisioned Source_; the raw declaration is the _environment-abstract_ input the deployment reads                                                                                                                                                         |
| "the affine-unit issue (ISS-0004) is on the same path"                                     | no theorem here depends on °C/°F being designer-facing; the thermistor example is a linear chart on counts and the design keeps kelvin                                                                                                                                                                                                                                                                        | dependency on ISS-0004 removed; a profile may calibrate raw data into canonical `Temperature` while the language presents kelvin only                                                                                                                                          |
| singleton `provision Δ Κ s P r` as the primitive                                           | the IMU case (one image, three Sources) is the realistic witness; the singleton is the one-target case of a shared-raw provision                                                                                                                                                                                                                                                                              | `Provision = ⟨r, clock, chan : DeclId → Option Channel⟩` is primitive; `Provision.one` is the singleton; every theorem is stated for the general form and instantiated (`provisionOne_transparent`, `WF.one`, `induced_one`)                                                   |

## 3. The construction, exactly

```text
Channel raw     = ⟨rep, tr, transfer, rep_semFree, rep_data, tr_pure, computes⟩
Channel.WF Θ ch = HasType Θ ∅ Grant.none [] ch.tr (arr raw ch.rep)
DeviceProfile   = ⟨raw, raw_semFree, raw_data, channels⟩          -- the catalog entry; no concept, no declaration
Provision raw   = ⟨r, clock, chan : DeclId → Option (Channel raw)⟩ -- the assignment

Fits Θ (sem c) ch  = (Θ c = some ch.rep)        Fits Θ τ ch = (τ = ch.rep)    (decidable)
realizeAt (sem c) tr r = mk c (app tr (declRef r))     realizeAt τ tr r = app tr (declRef r)

provision Δ P d = if d = r then ⟨r, ⟨raw, []⟩, none⟩
                  else match Δ d, chan d with
                       | some h, some ch => ⟨h.id, h.interface, some (realizeAt h.expectedType ch.tr r)⟩
                       | some h, none    => h
                       | none, _         => none
provisionΚ Κ P d = if d = r then clock else Κ d
induced Δ P I' d t = match chan d, tyView d with
                     | some ch, some τ => wrapAt τ (ch.transfer (I' r t))
                     | _ => I' d t

WF Θ Δ P = Δ r = none ∧ raw.SemFree ∧ raw.Data ∧
           ∀ s ch, chan s = some ch → ∃ h, Δ s = some h ∧ h.realization = none ∧ Fits Θ h.expectedType ch ∧ ch.WF Θ
ClockWF Κ P = ∀ s ch, chan s = some ch → Κ s = clock
RawInput P I' = (∀ t, TyVal raw (I' r t)) ∧ ∀ d t, (I' d t).NoClo
```

The raw declaration's kernel type is `raw`; its canonical type is `() -> raw`
(`raw_interface`, via Phase 12's `canonicalOfKernel_encode`). The distinction is
kept explicit: nothing in the kernel encoding is a unit.

## 4. Theorems

| claim                         | theorem                                                                                                               | hypotheses                                                                          |
| ----------------------------- | --------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------- |
| grant boundary                | `realization_checked_under_own_grant`, `grant_of_sem`, `channel_constructs_nothing`                                   | `GlobalWF`; `Channel.WF`                                                            |
| purity necessary              | `exD` (typed, impure, tick-dependent); `Channel.WF_refFree`; `pure_iff_delayFree_of_wf`                               | —                                                                                   |
| fitting decidable; negatives  | `instDecidableFits`; `exC`                                                                                            | —                                                                                   |
| refinement                    | `provision_envRefines`, `provision_tyView_eq`                                                                         | `WF`                                                                                |
| typing of the new realization | `realizeAt_typed`                                                                                                     | `WF`                                                                                |
| global well-formedness        | `provision_wf`                                                                                                        | `ev.Monotone`, `GlobalWF Δ`, `WF`, `hcomm`                                          |
| causality                     | `provision_causal`                                                                                                    | `WF`, `NoMention Δ r`, `Causal Δ`                                                   |
| clocks                        | `provision_wellClocked`                                                                                               | `WF`, `ClockWF`, `NoMention`, `WellClocked Κ Δ`                                     |
| induced input                 | `induced_target`, `induced_other`, `target_value`                                                                     | `WF`, `RawInput`                                                                    |
| transparency                  | `provision_transparent` (↔), `provision_transparent_typed`, `provision_decl_transparent`, `provision_physicalOutput`  | `WF`, `NoMention`, `RawInput`, `r ∉ e.refs` (or `HasType Θ Δ …`), `Avoids r` on `ρ` |
| trace abstraction             | `provision_abstracts`                                                                                                 | as above                                                                            |
| exactness                     | `provision_exact`, `JointSection.one`                                                                                 | + `JointSection`                                                                    |
| strict refinement witness     | `exE`, `sat_never_451`                                                                                                | —                                                                                   |
| re-application                | `provision_not_reapplicable`, `provision_idem_total`, `provision_reprovision_not_refinement`, `provision_source_role` | `WF`                                                                                |
| commutation / permutation     | `provision_comm`, `provision_perm`                                                                                    | independence; nodup keys                                                            |
| shared raw, several targets   | `exF`, `wfI`, `no_joint_witness`                                                                                      | —                                                                                   |
| singleton corollaries         | `WF.one`, `provisionOne_transparent`, `induced_one`                                                                   | —                                                                                   |

Supporting general results (reusable beyond provision): `Expr.Pure.refs_nil`,
`Expr.Pure.instRefs_nil`, `Expr.Pure.clocked`, `Value.All` with
`Prim.compute_all`/`applyPrim_all`, `MEv.of_ev_pure` (pure single-domain
derivations are multi-domain derivations), `Transduces.mev`, `simulate` (the
design-simulation lemma behind transparency), `input_congr`, `clockedB_congr`,
`TyVal.noClo`.

## 5. How the main proof goes

`simulate` is one induction over `MEv`: two designs evaluate every `r`-free term
alike when every declaration other than `r` is _simulated_ — a realized
declaration either has the same `r`-free body on both sides or its observations
are matched directly; an unresolved declaration's input is matched by an
observation on the other side. The invariant carried through closures is
`Avoids r` (no closure body inside a value mentions `r`), which is why the local
environment must avoid `r` and inputs must be closure-free. Transparency is two
instantiations (abstract→provisioned and back); `input_congr` is a third. The
provisioned target's value is obtained from `Transduces.mev`: a pure term's
canonical evaluation (empty design, constant input, top level) transfers to any
design, input, domain and tick, because `Ev.pure` makes the closure and body
derivations context-free and `MEv.of_ev_pure` moves them across the schedule.
Top level is exactly where `MEv.refRealized` evaluates a realization, which is
what makes the transfer environment-independent without a closure-equivalence
theorem.

## 6. Design results and verdicts

- **Provision is a deployment/surface construction over existing kernel terms,
  not a kernel construct.** KEEP IN SURFACE/DEPLOYMENT CONSTRUCTION. Nothing
  entered `Core`; every theorem is about `provision`, a function on `DeclEnv`.
- **The profile is generic in the concept.** A channel produces representation
  data; the Source's own signature grants `mk c`. No `ConceptId` in `Channel` or
  `DeviceProfile`.
- **Purity is the profile condition.** `tr.Pure` — equivalently, typed in the
  empty design and delay-free. A transducer with memory (debouncing, filtering)
  is a different object: not a function of the raw reading, and the transparency
  and exactness theorems are stated over functions. Recorded as the open
  extension, not smuggled in.
- **Shared raw reading is primitive**; the singleton is its special case. Trace
  equality for shared readings needs a joint section; deployment is in general a
  _strict_ refinement of the abstract environment even when each channel is
  onto.
- **Commitments are obligations on the profile.** `provision_wf` says so.
- **The output side** was left as a duality note here and is Phase 14's subject
  ([note](output-realization-by-device-encoders.md)): a lowering, not a
  provision. At the time of this phase no shared abstraction fell out that made
  it free (the drive edge's type equality `DriveWF` would need a new realized
  declaration in between, as REPORT §6.5 already asked; nothing here is reused
  for it beyond `simulate`).
- **Terminology**: abstract Source, provisioned Source, raw declaration,
  environment-abstract realization, device-specific provision. Not
  "monomorphised".

## 7. Open questions remaining

1. Memory in a transducer: stateful channels (`tr` with `delay`) and a
   transparency theorem over streams rather than functions.
2. A device clock: `Κ r ≠ Κ s` with a `sync` at deployment (Phase 5/8 cover the
   transport; the construction would add one declaration per target).
3. Commitment discharge: which commitments a Source may carry and how a
   profile's declared range discharges them (the `hcomm` hypothesis; ties to
   PRP-0001's "range facts").
4. Output provision (the dual): stated, not built.
5. Whether `computes` should be _checked_ by the compiler (it is a `∀` over raw
   values) or _trusted_ from the catalog with differential tests; the examples
   discharge it by hand.
6. Ill-typed raw inputs: transparency is stated for `RawInput`; what a
   deployment should do with an out-of-type reading (a stuck realization in the
   kernel) is a validation question.
