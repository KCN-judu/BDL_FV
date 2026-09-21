---
kind: kernel
area: core
status: current
---

# The kernel in one paragraph

The cumulative kernel after Phase 19 (unchanged since Phase 9b), as the reports
state it; the Lean sources under `BDL/` are the authority and this page is their
summary. Per-phase results are in [`../reports/`](../reports/README.md); the
construct-by-construct verdicts in [minimality.md](minimality.md); the file map
in [layout.md](layout.md).

```text
DeclEnv         maps DeclId ↦ DesignDecl
DesignDecl      = id : DeclId  ×  interface : DeclInterface  ×  realization : Option Expr
DeclInterface   = expectedType : Ty  ×  commitments : List PropertyId      (monotone, public)
Ty              = bool | nat | arr Ty Ty | sem SemanticId | q Dim | opt Ty | list Ty | prod Ty Ty
                                                                            (Phase 2: nominal concepts; Phase 3: quantities; Phase 9a: lists; 9b: products)
ConceptEnv Θ    maps SemanticId ↦ Option Ty                                 (Phase 3: representation binding, write-once, sem-free data)
Prim            registered operators; dimension algebra lives in Prim.ty     (Phase 3; Phase 4 adds bool/opt ops; 9a list ops; 9b pairs, eq on every data type; lt on quantities only — 9c)
declRef d       refers to a declaration by stable identity
rep e / mk s e  observe / construct a semantic value                        (Phase 3; mk only under a grant)
delay init e    the value of e at the previous activation of its own domain (Phase 4; = sync own)
sync c init e   the value of e at the last activation of domain c strictly before now, init if none
                                                                            (Phase 5: the one transport/state primitive)
fold f z l      the list recursor — the one term former that applies a function value (Phase 9b);
                every collection operation is a definition over it
ClockEnv Κ      maps DeclId ↦ Option ClockId; none = domain-agnostic pure mapping (Phase 5: interface-level, frozen)
Clocked Κ c e   the domain judgment: references stay in their domain unless through sync (Phase 5; typing unchanged)
Sched S         which domains activate at which global ticks; rates are validation data that induce a schedule
typing          HasType Θ Δ G Γ e τ: sees Δ.tyView, the binding Θ s = some R, and the grant G — nothing else
realizations    are typed under Grant.of their own signature: a value of sem s is built only inside a
                declaration that announces sem s
semantics       Ev Δ I t ρ e v (one domain) ⊂ MEv S Δ I c t ρ e v (many domains): tick-indexed evaluation;
                unresolved declarations are inputs; Ty unchanged (no Signal, no Event); executable iff Causal
OutputEnv Ω     maps OutputId ↦ (accepted Ty, ClockId): what each logical output carries (Phase 6: resource identity; Phase 14: realized by deployment)
DriveEnv β      maps DeclId ↦ Option OutputId: the drive edges; write-once               (Phase 6)
DriveWF         driver type = accepted type ∧ driver clock = sink clock; no coercion, no sync in the binding
SingleDriver β  at most one driver per logical output — global, not typing; CompleteOutputs: every required sink driven
validation      (Phase 7, outside the kernel) Hardware = resources with capabilities + per-capability units + sharing policy;
                Requirements from device bindings; ValidFor H R A decidable by an exhaustive solver (sound and complete);
                feasibility is a relation Design × Target and is not monotone under design refinement
validation      may rely on commitments and evidence (Satisfies, GlobalWF)
monotone refinement (DeclLeq / DeclRefines / EnvRefines)   preserves every earlier commitment
arbitrary edit  (retype, drop commitment, detach/replace realization, re-identify)
                is outside the refinement order and may invalidate dependents → recheck
```

"Hole" is no longer a kernel concept. An unresolved declaration is a declaration
whose `realization` is `none`; the word survives only as a surface/HCI metaphor
(FVD-0015).

A concept `sem s` is a nominal type, not a quantity with one producer: any
number of declarations may announce, construct (under their own grant) or be
Sources of one concept, no judgment counts them, and no term names a concept to
obtain a value — every reference is `declRef d`. Several candidates for one
concept are resolved by an ordinary declaration over their references (FVD-0159;
producer uniqueness is not a kernel invariant, FVD-0160).
