# BDL_FV — formal-design experiment for a Behavior Design Language kernel

A Lean 4 project that treats the BDL proposal as a *candidate* specification
and derives, by construction / counterexample / proof, what its kernel
actually needs.  No dependencies beyond core Lean.

```bash
lake build
```

* `paper/` — the BDL Design and Formalization Monograph (`paper/paper.md` is canonical; `paper/build.sh` regenerates `body.typ` and the PDF); `paper/archive/` keeps the 2026-09 conference manuscript
* `REPORT.md` — formal results per phase
* `DESIGN_DECISIONS.md` — every model choice and rejected alternative
* `MINIMALITY.md` — construct-by-construct kernel / surface / validation / remove table

Status: Phases 0–7, 8a/8b, 9a–9c, 10, 10b, 11, 12 and 13 complete (lifecycle/refinement; cross-declaration
preservation; semantic identity; representation binding + dimensions;
reactive core; clock domains + synchronization; physical outputs +
single-driver discipline; hardware constraint validation + resource
allocation; behaviour systems — reusable components, fresh instantiation,
port binding, hierarchical composition, flattening; behaviour grouping and
component extraction; list data and lossless buffered cross-domain events;
products, the list recursor and the polymorphic equation library;
capability audit — equality on data, ordering on quantities and
declared-ordered concepts only; unit coordinates and Formula-Composer
dimension inference as surface elaboration; affine charts — conversion
as a groupoid of affine isomorphisms over exact choice-free rationals,
point/delta downgraded to optional validation; natural binder and range
syntax as conservative desugaring; unit-domain normalization — the
canonical type `() -> B` as an interface normalization whose value is the
kernel type `B`, the source role as a realization state, `A -> ()` not a
sink; Source provision by device transducers — PRP-0001 audited as a
construction over designs with transparency, trace abstraction and the
corrected exactness/re-application claims).
Remaining: Phase 8c surface elaboration + executable semantics; final
minimality audit.

* `BDL/Behavior/` — Phase 8a: behaviour as a first-class design object
  (`BEHAVIOR_NOTE.md` is the design note; `BEHAVIOR_SYSTEM_REQUIREMENTS.md`
  the production requirements report); Phase 8b: grouping and extraction
  (`BEHAVIOR_GROUPING_NOTE.md`: design note and IDE implications)
* `BDL/Core/ListData.lean`, `BDL/Surface/Buffer.lean`,
  `BDL/Validation/Capacity.lean` — Phase 9a: `Ty.list` and the buffered
  cross-domain event transport as a proved surface elaboration
  (`BUFFERING_NOTE.md` is the design note)
* `BDL/Surface/Poly.lean`, `Stdlib.lean`, `Generic.lean` — Phase 9b:
  rank-1 schemes instantiated by matching, the definitional equation
  library with its typing/evaluation theorems, nominality through generics
  (`POLYMORPHIC_EQUATION_LANGUAGE_NOTE.md` is the design note, with the
  production guidance)
* `BDL/Surface/Units.lean`, `Composer.lean`, `Affine.lean` — Phase 10:
  unit coordinates (`inUnit`/`withUnit` as elaborated arithmetic, exact
  symbolic scales with π), typed holes with sound and complete local
  dimension inference, presentation invariance, affine counterexamples
  (`UNITS_NOTE.md` is the design note, with the production guidance)
* `BDL/Surface/Rational.lean`, `Charts.lean` — Phase 10b: a choice-free
  exact rational field; affine charts with the chart, groupoid and
  difference laws over any field; Celsius/Fahrenheit, ADC calibration and
  encoder offsets executed exactly (`UNITS_NOTE.md` §17)
* `BDL/Surface/Natural.lean` — Phase 11: `all/any/map/filter x in xs:`,
  `x in lo .. hi`, `x ?? d` desugared to the Phase-9 library; scoping,
  alpha-equivalence, typing, evaluation and clocks proved
  (`NATURAL_SYNTAX_NOTE.md` is the design note, with production guidance)
* `BDL/Surface/UnitDomain.lean` — Phase 12: canonical types with the empty
  product above the kernel, unit elimination as a computed normalization
  inverse to uncurrying, `f`/`f()`/`f(())` as one reference, the source
  role as environment provision, `A -> ()` shown unable to name a consumer
  (`UNIT_DOMAIN_NOTE.md` is the design note, with production guidance)
* `BDL/Surface/Provision.lean` — Phase 13: device channels (pure
  transducer + transfer function), shared-raw provision of Sources as an
  `EnvRefines` step, the simulation lemma, transparency in both directions,
  trace abstraction, joint-section exactness, non-reapplicability, exact
  commutation (`PROVISION_NOTE.md` is the audit of production PRP-0001)

Kernel in one line: `DeclEnv : DeclId → Option DesignDecl`, where a
`DesignDecl` is a stable id, a `DeclInterface` (expected type + monotone
public commitments), and an optional realization. Types include nominal
semantic concepts `Ty.sem SemanticId` (Phase 2) and quantities `Ty.q Dim`
(Phase 3). A write-once `ConceptEnv` binds concepts to sem-free
representations; `rep` observes freely, `mk s` constructs only inside a
realization whose own signature announces `sem s` (Phase 3). One temporal
primitive `delay init e` and a tick-indexed evaluation relation give the
single-domain reactive semantics: deterministic, total on causal designs, and
every designer-facing temporal operator derived (Phase 4). Nominal clock
domains with a schedule, a domain judgment, and one transport primitive
`sync src init e` (of which `delay` is the own-domain instance) give the
multi-domain semantics; the single-domain one embeds exactly (Phase 5).
Physical sinks are nominal resources with an accepted type and clock; a
write-once drive edge per declaration, checked by type and clock equality,
and one global invariant — at most one driver per sink — connect values to
hardware; all combination is ordinary computation (Phase 6). A separate
validation layer (`BDL/Validation/`) decides whether a design is realizable
on a declared target board — a finite resource/capability table with a
sound and complete solver — without the design ever depending on the board
(Phase 7). A behaviour is a template design behind an interface of
semantic ports and clock parameters; instantiation freshens every identity
the template owns, binding is a realization step, and a system flattens to
an ordinary design accepted by the same judgments — the kernel is unchanged
(Phase 8a). Ordinary list data `Ty.list τ` lets the Phase-5 event window
be written as five declarations over `delay` and `sync`, proved to
evaluate to exactly the window at every tick; capacity is a validation
obligation and `Event` is still not a type (Phase 9a). Products and one
list recursor complete the data core; every collection operation, range,
finite-set test and finite quantifier is a definition over them, generic
definitions are families of monomorphic terms instantiated by matching, and
the kernel never sees a type variable (Phase 9b). Typing sees only the
expected type; validation may rely on commitments and evidence; monotone
refinement preserves earlier commitments; anything else is an edit that
requires rechecking dependents.
