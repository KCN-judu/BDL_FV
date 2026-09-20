---
kind: report
phase: 13
area: surface
date: 2026-09-20
status: current
---

# Phase 13 — Source provision by device transducers (PRP-0001 audit)

Question (production PRP-0001, draft, `876005c`; ISS-0016): can a Source
`s : () -> C` be provisioned at deployment by a raw reading `r : () -> R` and a
device transducer `R -> rep(C)` as a construction over designs, with the design
unable to tell the difference — and are the proposal's seven claims true as
stated? The construction exists and is a surface/deployment construction; four
of the claims needed correction. Files: `BDL/Surface/Provision.lean`,
`BDL/Experiments/ProvisionExamples.lean`; note
`docs/notes/source-provision-by-device-transducers.md`.

**Definitions.**
`Channel raw = ⟨rep, tr, transfer, rep_semFree, rep_data, tr_pure, computes⟩`
with `computes : ∀ v, TyVal raw v → Transduces tr v (transfer v)` and
`Channel.WF Θ ch := HasType Θ ∅ Grant.none [] tr (arr raw rep)`;
`DeviceProfile = ⟨raw, …, channels⟩` (no concept);
`Provision raw = ⟨r, clock, chan : DeclId → Option Channel⟩` (shared raw,
several targets; `Provision.one` the singleton); `Fits` (decidable);
`realizeAt (sem c) tr r = mk c (app tr (declRef r))`, else `app tr (declRef r)`;
`provision Δ P`, `provisionΚ`, `induced Δ P I'`; `WF`, `ClockWF`, `RawInput`,
`NoMention`.

**Purity (§1).** Typing in the empty design excludes `declRef`
(`Channel.WF_refFree`) but not memory: `(λk. λn. k) (delay 0 1)` is typed at
`q0 -> q0` and maps `7` to `0` at tick 0 and `1` at tick 1 (`exD`). So the
profile condition is `tr.Pure`, equivalently `WF ∧ DelayFree`
(`pure_iff_delayFree_of_wf`). Purity gives `refs = []`, `instRefs = []`, clocked
everywhere (`Expr.Pure.refs_nil`, `instRefs_nil`, `clocked`), and context-free
evaluation through `Ev.pure` and the new `MEv.of_ev_pure` (`Transduces.mev`).

**Grant (§3).** `realization_checked_under_own_grant` (from `Satisfies`),
`grant_of_sem : Grant.of (sem c) s ↔ s = c`, `channel_constructs_nothing` (from
`constructs_granted`). `exC`: `λx. mk RoomTemp x` refused under `Grant.none`,
accepted under `Grant.of (sem RoomTemp)`.

**Structure.** `provision_envRefines`, `provision_tyView_eq`, `realizeAt_typed`,
`provision_wf` (needs `ev.Monotone` and evidence for each target's commitments —
a Source's commitments are obligations on the profile, a hypothesis the PRP
lacked), `provision_causal` (rank shifted by one, `r` at the bottom; purity
keeps the channel term edge-free), `provision_wellClocked` (`Κ r = Κ s`;
`clockedB_congr`).

**Transparency (§14–15).** One simulation lemma `simulate` (induction on `MEv`
with the closure invariant `Value.All (r ∉ ·.refs)`), instantiated three ways:
`provision_forward`, `provision_backward`, `input_congr`.
`provision_transparent : MEv S Δ (induced Δ P I') c t ρ e v ↔ MEv S (provision Δ P) I' c t ρ e v`
under `WF`, `NoMention Δ r` (true of every `GlobalWF` design), `RawInput P I'`,
`r ∉ e.refs`, `ρ` avoiding `r`. The boundary by typing: `typed_avoids`,
`provision_transparent_typed`. Corollaries `provision_decl_transparent`,
`provision_physicalOutput`, `provision_abstracts` (traces of the provisioned
design are traces of the abstract design under the induced input).

**Exactness (§17).** Pointwise surjectivity is an `∃` per tick; a raw input
built from it is a choice principle. With a shared reading it is also
insufficient (`no_joint_witness`: `id` and `succ` from one reading, abstract
`(5, 9)` has no witness). `provision_exact` needs a `JointSection` (a raw trace
every channel transfers to the abstract input); `JointSection.one` builds it
from a pointwise right inverse for one channel.

**Strict refinement (§18).** `exE`: the saturating ADC never yields 451 K
(`sat_never_451`); the abstract design observes `TempSensor = 451 K`, no
provisioned deployment does.

**Re-application (§19).** `provision_not_reapplicable` (no target is a Source
afterwards; `WF` fails since `r` is not fresh); `provision_idem_total` (the
total function overwrites with the same body);
`provision_reprovision_not_refinement` (a different term is an edit);
`provision_source_role` (the Source role moves to `r`). "Idempotent" is replaced
by _not re-applicable_.

**Commutation (§20).** `provision_comm`: exact environment equality for
independent provisions; `provision_perm`: the channel assignment is a set.

**Executed.** A GPIO identity channel on a `bool` Source; the thermistor
`T = 2n + 250 K` on `TempSensor` with `tooHot` computing the same truth values
from counts and from the induced temperature, plus `EnvRefines`, `Causal`,
`WellClocked` of the provisioned design; rejected profiles; the impure typed
term; the saturating ADC; one IMU image provisioning `pitch` and `roll` with
`level` reading both, and the permuted assignment equal.

**Terminology and dependencies.** "Monomorphised" dropped (Phase 9b owns the
word); _abstract / provisioned Source_, _raw declaration_, _environment-abstract
realization_. No dependency on exposing °C/°F (ISS-0004): the thermistor is a
linear chart on counts and the design keeps kelvin. Output provision stays a
duality note.

**Verdict.** KEEP IN SURFACE/DEPLOYMENT CONSTRUCTION: nothing entered `Core`;
provision is a function on `DeclEnv`. 92 theorems on `propext`/`Quot.sound`; no
`Classical.choice`. The PRP was revised in production (`docs/proposals/0001-…`),
status still _draft_.
