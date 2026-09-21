import BDL.Surface.SourceBoundary
import BDL.Experiments.ProducerUnique
import BDL.Surface.Stdlib
import BDL.Experiments.OutputAlternatives
import BDL.Experiments.BehaviorAlternatives
import BDL.Experiments.OutputRealizationExamples

/-!
# Phase 19 — May several declarations produce one concept?  Models A, B, C

The question: is `sem C` a nominal *type* whose values many declarations may
construct (A), the identity of *one* product-level quantity with one producing
relationship (B), or a type whose several candidate producers are admitted only
under an explicit resolution (C)?  This module does not decide by preference;
it states the current fact, defines the candidate invariants, and tests each
model against the constructions the development already has.

Definitions (experimental — nothing enters `Core`):

* `SigProduces Δ d C` — `d`'s *signature* announces `C` in result position:
  the grant.  `SigUnique Δ`: at most one such `d` per `C`.
* `MkProduces Δ d C` — `d` *originates* a `C`: its realization constructs `C`
  (`Expr.constructs`, a `mk`) or it is unresolved with `C` in result position
  (a Source).  A wire (`declRef`), a transport (`sync`), a memory (`delay`), a
  selection (`ite`) of `C` values is not an origin.  `MkUnique Δ`: at most one
  origin per `C`.  The decidable `constructsB` mirrors `Expr.constructs`.

Facts established (each a theorem or an executed witness):

* **The current fact** — `GlobalWF` admits two declarations of result type
  `sem C` (`x, y : C`, `f : A -> C`, `g : B -> C`), and Phase 6's own
  explicit-composition design carries five: `witness_two_values`,
  `witness_two_arrows`, `phase6_not_sigUnique`, `phase6_not_mkUnique`.
* **Two values, both deterministic** — at one tick `x` and `y` are two
  different values of `sem C` (`two_C_values_coexist`); evaluation is
  `Ev.det` regardless of how many producers exist.  "The value of concept `C`"
  has no denotation in the kernel; "the value of declaration `d`" has.
* **Consumers reference declarations, not concepts** — a second producer
  that no term references is invisible to every term
  (`second_producer_invisible`, from `update_transparent`); nothing in the
  kernel resolves a value by concept.
* **Signature-uniqueness is structurally refuted** — every component
  binding realizes a required port of type `sem C` beside the provided port
  that carries `C` (`binding_makes_second_signature`, on Phase 8a's `lamp`),
  and every named transport of a `C` value is a second declaration of type
  `sem C` (`transport_second_signature`).  A relay is not an origin: the
  origin-based notion `MkProduces` excludes both.
* **Origin-uniqueness (Model B) is preserved by refinement** — realizing
  declarations never adds an origin (`mkUnique_refine`); adding a second
  origin is an edit, never a refinement step.
* **Origin-uniqueness breaks ordinary composition** — two instances of one
  component sharing a provided concept are two origins
  (`lamp_two_origins`); with the concept instance-private the origins are of
  two concepts (`private_lamp_two_concepts`).  The checkable boundary rule
  is stated with the witness.
* **Every alternative-producer use has an explicit-resolution form** — Phase
  6's `selected`, `blended`, `maxed` are one declaration each over several
  `C`-typed inputs (existing constructs, no resolver), and the redundant
  sensors and the manual/automatic override rewrite with intermediate
  concepts and one resolver with the same downstream trace, executed
  (`sensors_rewriting_same_trace`, `override_rewriting_same_trace`); the
  rewritten designs are origin-unique (`sensorsC_mkUnique`).  No necessity
  witness for two *origins* of one concept was found; none is claimed
  impossible.
* **Origin is syntactic** — a Source beside a formula is two origins
  (`source_and_formula`); Phase 14's `light := mk Brightness (rep dial)`
  counts as a second origin of what `dial` supplies, and the wire
  `light := dial` does not (`rewrap_counts_as_origin`).  A uniqueness lint
  would decide by the shape of the term, not by what the design means.
* **The drive edge is independent of producers** — one origin of `C` may
  drive two outputs (`one_origin_two_outputs`), and a non-origin (a
  wire) may be the driver of an origin-unique design, so `β` cannot be
  derived from the origin (`driver_not_origin`).  `SingleDriver` and producer uniqueness are
  different invariants about different objects.
-/

namespace BDL.Experiments.Producers
open BDL BDL.Reactive BDL.Clock BDL.Output BDL.Stdlib BDL.Provision BDL.OutputWindow

/-! ## The candidate notions -/

/-- `d`'s signature announces `C` in result position — the grant reading. -/
def SigProduces (Δ : DeclEnv) (d : DeclId) (C : ConceptId) : Prop :=
  ∃ h, Δ d = some h ∧ C ∈ h.interface.expectedType.grant

/-- At most one declaration per concept announces it in result position. -/
def SigUnique (Δ : DeclEnv) : Prop :=
  ∀ C d₁ d₂, SigProduces Δ d₁ C → SigProduces Δ d₂ C → d₁ = d₂

def sigProducesB (Δ : DeclEnv) (d : DeclId) (C : ConceptId) : Bool :=
  match Δ d with
  | some h => decide (C ∈ h.interface.expectedType.grant)
  | none => false

theorem sigProducesB_iff (Δ : DeclEnv) (d : DeclId) (C : ConceptId) : sigProducesB Δ d C = true ↔ SigProduces Δ d C := by
  unfold sigProducesB SigProduces
  cases hd : Δ d with
  | none => simp
  | some h => simp

instance (Δ : DeclEnv) (d : DeclId) (C : ConceptId) : Decidable (SigProduces Δ d C) :=
  decidable_of_iff _ (sigProducesB_iff Δ d C)

/-- Phase 19's names for the notions Phase 20 moved into `Core/Producer`:
    `MkProduces` is `Produces` (an origin: a `mk C` in the body, or an
    unresolved announcer of `C`), `MkUnique` is `ProducerUnique`. -/
abbrev MkProduces := Produces
abbrev MkUnique := ProducerUnique

theorem SigUnique.toMkUnique {Θ : ConceptEnv} {ev : Evidence} {Δ : DeclEnv} (g : GlobalWF ev Θ Δ)
    (h : SigUnique Δ) : MkUnique Δ := by
  intro C d₁ d₂ h₁ h₂
  refine h C d₁ d₂ ?_ ?_
  · exact granted g h₁
  · exact granted g h₂
where
  granted {Θ : ConceptEnv} {ev : Evidence} {Δ : DeclEnv} (g : GlobalWF ev Θ Δ) {d : DeclId} {C : ConceptId}
      (h : Produces Δ d C) : SigProduces Δ d C := by
    obtain ⟨h, hd, hp⟩ := h
    refine ⟨h, hd, ?_⟩
    cases hr : h.realization with
    | none => simpa [DesignDecl.origins, hr] using hp
    | some b =>
      simp only [DesignDecl.origins, hr] at hp
      exact ((g.wellFormed hd) b hr).1.constructs_granted C (Expr.constructs_of_mem_originSet C b hp)

/-! ## The current fact: two declarations of one concept, well formed -/

def C : ConceptId := ⟨300⟩
def A : ConceptId := ⟨301⟩
def B : ConceptId := ⟨302⟩
def Q0 : Ty := .q Dim.zero
def Θ : ConceptEnv := fun s => if s = C ∨ s = A ∨ s = B then some Q0 else none
def lit (n : Nat) : Expr := .prim (.lit Dim.zero n)

def x : DeclId := ⟨0⟩
def y : DeclId := ⟨1⟩
def f : DeclId := ⟨2⟩
def g : DeclId := ⟨3⟩
def a : DeclId := ⟨4⟩
def b : DeclId := ⟨5⟩
def h : DeclId := ⟨6⟩

/-- `x : C := mk C 1`, `y : C := mk C 2`. -/
def Δxy : DeclEnv := .ofList [⟨x, ⟨.sem C, []⟩, some (.mk C (lit 1))⟩, ⟨y, ⟨.sem C, []⟩, some (.mk C (lit 2))⟩]

/-- `f : A -> C`, `g : B -> C`, both realized by a formula, and `a : A`,
    `b : B` Sources. -/
def Δfg : DeclEnv := .ofList [
  ⟨a, ⟨.sem A, []⟩, none⟩, ⟨b, ⟨.sem B, []⟩, none⟩,
  ⟨f, ⟨.arr (.sem A) (.sem C), []⟩, some (.lam (.sem A) (.mk C (.rep (.var 0))))⟩,
  ⟨g, ⟨.arr (.sem B) (.sem C), []⟩, some (.lam (.sem B) (.mk C (app2 (.prim (.add Dim.zero)) (.rep (.var 0)) (lit 1))))⟩]

theorem witness_two_values : GlobalWF (fun _ _ _ => True) Θ Δxy ∧ Causal Δxy ∧ ¬ SigUnique Δxy ∧ ¬ MkUnique Δxy := by
  refine ⟨GlobalWF.ofList (by decide), Causal.ofList (fun _ => 0) 1 (fun _ => Nat.zero_lt_one) (by decide), ?_, ?_⟩
  · intro hu
    have := hu C x y ⟨_, rfl, by decide⟩ ⟨_, rfl, by decide⟩
    exact absurd this (by decide)
  · intro hu
    have := hu C x y (by decide) (by decide)
    exact absurd this (by decide)

theorem witness_two_arrows : GlobalWF (fun _ _ _ => True) Θ Δfg ∧ ¬ SigUnique Δfg := by
  refine ⟨GlobalWF.ofList (by decide), fun hu => ?_⟩
  have := hu C f g ⟨_, rfl, by decide⟩ ⟨_, rfl, by decide⟩
  exact absurd this (by decide)

/-- **Two values of one concept coexist at one tick**, both well typed,
    both deterministic (`Ev.det`), different at the representation level:
    concept identity alone does not identify one runtime value. -/
theorem two_C_values_coexist :
    (evalF Δxy (fun _ _ => .nat 0) 16 0 [] (.declRef x)).bind (fun v => match v with | .sem s (.nat n) => some (s.n, n) | _ => none)
      = some (300, 1) ∧
    (evalF Δxy (fun _ _ => .nat 0) 16 0 [] (.declRef y)).bind (fun v => match v with | .sem s (.nat n) => some (s.n, n) | _ => none)
      = some (300, 2) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Phase 6's explicit composition — `base, corr, final : MotorAngle` — is
    the design Phase 6 calls correct, and it has three signatures and three
    origins of one concept. -/
theorem phase6_not_sigUnique : ¬ SigUnique BDL.Experiments.Output.ΔB := by
  intro hu
  have := hu BDL.Experiments.Semantic.cMotor BDL.Experiments.Output.baseAngle BDL.Experiments.Output.corrAngle
    ⟨_, rfl, by decide⟩ ⟨_, rfl, by decide⟩
  exact absurd this (by decide)

theorem phase6_not_mkUnique : ¬ MkUnique BDL.Experiments.Output.ΔB := by
  intro hu
  have := hu BDL.Experiments.Semantic.cMotor BDL.Experiments.Output.baseAngle BDL.Experiments.Output.finalAngle
    (by decide) (by decide)
  exact absurd this (by decide)

/-! ## Consumers reference declarations -/

/-- A consumer `h : C -> bool` reads `x`; adding the second producer `y`
    changes nothing it evaluates — a second producer is invisible unless
    referenced (`update_transparent`). -/
def Δx : DeclEnv := .ofList [⟨x, ⟨.sem C, []⟩, some (.mk C (lit 1))⟩,
  ⟨h, ⟨.bool, []⟩, some (ltE Dim.zero (.rep (.declRef x)) (lit 5))⟩]
def yDecl : DesignDecl := ⟨y, ⟨.sem C, []⟩, some (.mk C (lit 2))⟩

theorem second_producer_invisible {S : Sched} {I : Input} (hI : ∀ d t, Avoids y (I d t))
    {c : ClockId} {t : Nat} {v : Value} :
    MEv S Δx I c t [] (.declRef h) v ↔ MEv S (Δx.update yDecl) I c t [] (.declRef h) v :=
  update_transparent (h := yDecl) (NoMention.of_globalWF (GlobalWF.ofList (ev := fun _ _ _ => True) (Θ := Θ) (by decide)) rfl)
    hI (by simp [Expr.refs]; decide) (fun _ hw => by simp at hw)

/-! ## Signature-uniqueness is structurally refuted -/

open BDL.Experiments.Behavior in
/-- Phase 8a's lamp after flattening: the source's provided port and both
    dimmers' bound required ports are three declarations of type
    `sem Tilt`; the two dimmers' provided ports are two of `sem Bright`. -/
theorem binding_makes_second_signature :
    lamp.flattenΔ.tyView (lamp.declOf 0 outP) = some (.sem Tilt) ∧
    lamp.flattenΔ.tyView (lamp.declOf 1 inP) = some (.sem Tilt) ∧
    lamp.flattenΔ.tyView (lamp.declOf 2 inP) = some (.sem Tilt) ∧
    lamp.flattenΔ.tyView (lamp.declOf 1 outP) = some (.sem Bright) ∧
    lamp.flattenΔ.tyView (lamp.declOf 2 outP) = some (.sem Bright) ∧
    ¬ SigUnique lamp.flattenΔ := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, fun hu => ?_⟩
  have := hu Tilt (lamp.declOf 0 outP) (lamp.declOf 1 inP) (by decide) (by decide)
  exact absurd this (by decide)

def c1 : ClockId := ⟨1⟩
def c2 : ClockId := ⟨2⟩
def xS : DeclId := ⟨7⟩
/-- `x : C` in `c1`, `xS : C := sync c1 (mk C 0) x` in `c2`: the named transport
    is a second declaration of type `sem C`, well clocked, and it originates
    nothing. -/
def Δsync : DeclEnv := .ofList [⟨x, ⟨.sem C, []⟩, some (.mk C (lit 1))⟩,
  ⟨xS, ⟨.sem C, []⟩, some (.sync c1 (.mk C (lit 0)) (.declRef x))⟩]
def Κsync : ClockEnv := fun d => if d = x then some c1 else some c2

theorem transport_second_signature :
    WellClocked Κsync Δsync ∧ ¬ SigUnique Δsync ∧ MkProduces Δsync x C ∧
    -- the transport's body constructs only its initial value's concept — the same `C`, from the init
    (Expr.constructs C (.sync c1 (.mk C (lit 0)) (.declRef x))) ∧
    ¬ Expr.constructs C (.sync c1 (lit 0) (.declRef x)) := by
  refine ⟨WellClocked.ofList (by decide), fun hu => ?_, by decide, by decide, by decide⟩
  have := hu C x xS ⟨_, rfl, by decide⟩ ⟨_, rfl, by decide⟩
  exact absurd this (by decide)

/-! ## Model B under refinement -/

/-- Realizing declarations (the same domain, each declaration refined) never
    adds an origin: a declaration that becomes realized was an unresolved
    announcer of every concept its new body may construct (the grant), and
    is therefore counted already.  `MkUnique` is preserved by every
    refinement that adds no declaration. -/
theorem mkUnique_refine {Θ : ConceptEnv} {ev : Evidence} {Δ₁ Δ₂ : DeclEnv} (g₂ : GlobalWF ev Θ Δ₂)
    (er : EnvRefines Δ₁ Δ₂) (dom : ∀ d, Δ₂ d ≠ none → Δ₁ d ≠ none) (hu : MkUnique Δ₁) : MkUnique Δ₂ :=
  ProducerUnique.refine g₂ er dom hu

/-! ## Model B under composition -/

open BDL.Experiments.Behavior in
/-- Two instances of one component with a *shared* provided concept are
    two origins of it after flattening: `MkUnique` fails on ordinary reuse. -/
theorem lamp_two_origins :
    MkProduces lamp.flattenΔ (lamp.declOf 1 outP) Bright ∧ MkProduces lamp.flattenΔ (lamp.declOf 2 outP) Bright ∧
    ¬ MkUnique lamp.flattenΔ := by
  refine ⟨by decide, by decide, fun hu => ?_⟩
  have := hu Bright (lamp.declOf 1 outP) (lamp.declOf 2 outP) (by decide) (by decide)
  exact absurd this (by decide)

open BDL.Experiments.Behavior in
/-- With the concept instance-private, the two instances originate two
    *different* concepts (`inst_concept_disjoint`): the boundary rule under
    which flattening keeps origin-uniqueness is that a shared concept is
    provided by at most one instance, or is private. -/
def privateLamp : BehaviorSystem := { lamp with insts := [⟨source, κfast⟩, ⟨privateDimmer, κfast⟩, ⟨privateDimmer, κfast⟩] }

open BDL.Experiments.Behavior in
theorem private_lamp_two_concepts :
    (Ren.inst privateDimmer W 1 κfast).s Bright ≠ (Ren.inst privateDimmer W 2 κfast).s Bright ∧
    MkProduces privateLamp.flattenΔ (privateLamp.declOf 1 outP) ((Ren.inst privateDimmer W 1 κfast).s Bright) ∧
    ¬ MkProduces privateLamp.flattenΔ (privateLamp.declOf 2 outP) ((Ren.inst privateDimmer W 1 κfast).s Bright) ∧
    MkProduces privateLamp.flattenΔ (privateLamp.declOf 2 outP) ((Ren.inst privateDimmer W 2 κfast).s Bright) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## Sources and re-wrapping -/

/-- A Source of `C` beside a formula producing `C`: two origins, two values. -/
def src : DeclId := ⟨8⟩
def Δsf : DeclEnv := .ofList [⟨src, ⟨.sem C, []⟩, none⟩, ⟨a, ⟨.sem A, []⟩, none⟩,
  ⟨f, ⟨.sem C, []⟩, some (.mk C (app2 (.prim (.add Dim.zero)) (.rep (.declRef a)) (lit 1)))⟩]

theorem source_and_formula : GlobalWF (fun _ _ _ => True) Θ Δsf ∧ MkProduces Δsf src C ∧ MkProduces Δsf f C ∧ ¬ MkUnique Δsf := by
  refine ⟨GlobalWF.ofList (by decide), by decide, by decide, fun hu => ?_⟩
  have := hu C src f (by decide) (by decide)
  exact absurd this (by decide)

/-- Phase 14's own design — `dial : () -> Brightness` a Source and
    `light : Brightness := mk Brightness (rep dial)` its driver — has two
    origins by the syntactic count, although `light` only re-wraps `dial`;
    written as the wire `light := dial` it has one.  Origin is a syntactic
    notion; the identity re-wrap is not an origin the design means. -/
theorem rewrap_counts_as_origin :
    let P := BDL.Experiments.OutputRealizationEx.Δ
    let B := BDL.Experiments.OutputRealizationEx.Brightness
    let dial := BDL.Experiments.OutputRealizationEx.dial
    let light := BDL.Experiments.OutputRealizationEx.light
    MkProduces P dial B ∧ MkProduces P light B ∧ ¬ MkUnique P ∧
    ¬ MkProduces (P.update ⟨light, ⟨.sem B, []⟩, some (.declRef dial)⟩) light B := by
  intro P B dial light
  refine ⟨by decide, by decide, fun hu => ?_, by decide⟩
  have := hu B dial light (by decide) (by decide)
  exact absurd this (by decide)

/-! ## Model C — explicit resolution with intermediate concepts, executed -/

def Temperature : ConceptId := ⟨310⟩
def SensorA : ConceptId := ⟨311⟩
def SensorB : ConceptId := ⟨312⟩
def Θt : ConceptEnv := fun s => if s = Temperature ∨ s = SensorA ∨ s = SensorB then some Q0 else none
def tA : DeclId := ⟨20⟩
def tB : DeclId := ⟨21⟩
def availA : DeclId := ⟨22⟩
def temp : DeclId := ⟨23⟩
def hot : DeclId := ⟨24⟩

/-- Model A: both sensors are `Temperature`; the selection is a
    declaration of `Temperature` over two `Temperature` inputs. -/
def ΔsensA : DeclEnv := .ofList [
  ⟨tA, ⟨.sem Temperature, []⟩, none⟩, ⟨tB, ⟨.sem Temperature, []⟩, none⟩, ⟨availA, ⟨.bool, []⟩, none⟩,
  ⟨temp, ⟨.sem Temperature, []⟩, some (iteE (.sem Temperature) (.declRef availA) (.declRef tA) (.declRef tB))⟩,
  ⟨hot, ⟨.bool, []⟩, some (ltE Dim.zero (lit 300) (.rep (.declRef temp)))⟩]
/-- Model C: each sensor is its own concept; one resolver originates
    `Temperature`. -/
def ΔsensC : DeclEnv := .ofList [
  ⟨tA, ⟨.sem SensorA, []⟩, none⟩, ⟨tB, ⟨.sem SensorB, []⟩, none⟩, ⟨availA, ⟨.bool, []⟩, none⟩,
  ⟨temp, ⟨.sem Temperature, []⟩, some (.mk Temperature (iteE Q0 (.declRef availA) (.rep (.declRef tA)) (.rep (.declRef tB))))⟩,
  ⟨hot, ⟨.bool, []⟩, some (ltE Dim.zero (lit 300) (.rep (.declRef temp)))⟩]

def IsA : Input := fun d t => if d = tA then .sem Temperature (.nat 310) else if d = tB then .sem Temperature (.nat 290)
  else if d = availA then .bool (t < 2) else .nat 0
def IsC : Input := fun d t => if d = tA then .sem SensorA (.nat 310) else if d = tB then .sem SensorB (.nat 290)
  else if d = availA then .bool (t < 2) else .nat 0

def readB (Δ : DeclEnv) (I : Input) (d : DeclId) (t : Nat) : Option Bool := (evalF Δ I 32 t [] (.declRef d)).bind Value.toBool?

/-- **The rewriting preserves the downstream trace**: sensor A while
    available (hot), sensor B after (not hot), in both models; Model A has
    two origins of `Temperature`, Model C one. -/
theorem sensors_rewriting_same_trace :
    (∀ t ∈ [0, 1, 2, 3], readB ΔsensA IsA hot t = readB ΔsensC IsC hot t) ∧
    readB ΔsensA IsA hot 1 = some true ∧ readB ΔsensA IsA hot 2 = some false ∧
    GlobalWF (fun _ _ _ => True) Θt ΔsensA ∧ GlobalWF (fun _ _ _ => True) Θt ΔsensC ∧
    ¬ MkUnique ΔsensA ∧
    -- Model C: exactly one origin of each concept
    MkProduces ΔsensC temp Temperature ∧ ¬ MkProduces ΔsensC tA Temperature ∧ ¬ MkProduces ΔsensC tB Temperature := by
  refine ⟨by decide, by decide, by decide, GlobalWF.ofList (by decide), GlobalWF.ofList (by decide), fun hu => ?_,
    by decide, by decide, by decide⟩
  have := hu Temperature tA tB (by decide) (by decide)
  exact absurd this (by decide)

/-- Model C's sensor design is origin-unique: every origin of any concept is
    the one declaration that announces it. -/
theorem sensorsC_mkUnique : MkUnique ΔsensC := ProducerUnique.ofList (by decide)

/-- Manual/automatic override — Model A with one `Brightness` for both
    and Model C with `ManualBrightness`, `AutoBrightness` and one resolver. -/
def Brightness : ConceptId := ⟨320⟩
def ManualB : ConceptId := ⟨321⟩
def AutoB : ConceptId := ⟨322⟩
def Θb : ConceptEnv := fun s => if s = Brightness ∨ s = ManualB ∨ s = AutoB then some Q0 else none
def knob : DeclId := ⟨30⟩
def ambient : DeclId := ⟨31⟩
def manual : DeclId := ⟨32⟩
def auto : DeclId := ⟨33⟩
def mode : DeclId := ⟨34⟩
def bright : DeclId := ⟨35⟩
def ΔovA : DeclEnv := .ofList [
  ⟨knob, ⟨Q0, []⟩, none⟩, ⟨ambient, ⟨Q0, []⟩, none⟩, ⟨mode, ⟨.bool, []⟩, none⟩,
  ⟨manual, ⟨.sem Brightness, []⟩, some (.mk Brightness (.declRef knob))⟩,
  ⟨auto, ⟨.sem Brightness, []⟩, some (.mk Brightness (app2 (.prim (.sub Dim.zero)) (lit 100) (.declRef ambient)))⟩,
  ⟨bright, ⟨.sem Brightness, []⟩, some (iteE (.sem Brightness) (.declRef mode) (.declRef manual) (.declRef auto))⟩]
def ΔovC : DeclEnv := .ofList [
  ⟨knob, ⟨Q0, []⟩, none⟩, ⟨ambient, ⟨Q0, []⟩, none⟩, ⟨mode, ⟨.bool, []⟩, none⟩,
  ⟨manual, ⟨.sem ManualB, []⟩, some (.mk ManualB (.declRef knob))⟩,
  ⟨auto, ⟨.sem AutoB, []⟩, some (.mk AutoB (app2 (.prim (.sub Dim.zero)) (lit 100) (.declRef ambient)))⟩,
  ⟨bright, ⟨.sem Brightness, []⟩, some (.mk Brightness (iteE Q0 (.declRef mode) (.rep (.declRef manual)) (.rep (.declRef auto))))⟩]
def Iov : Input := fun d t => if d = knob then .nat 70 else if d = ambient then .nat 40 else if d = mode then .bool (t % 2 = 0) else .nat 0
def readSem (Δ : DeclEnv) (d : DeclId) (t : Nat) : Option Nat :=
  (evalF Δ Iov 32 t [] (.declRef d)).bind fun v => match v with | .sem _ (.nat n) => some n | _ => none

theorem override_rewriting_same_trace :
    (∀ t ∈ [0, 1, 2], readSem ΔovA bright t = readSem ΔovC bright t) ∧
    readSem ΔovA bright 0 = some 70 ∧ readSem ΔovA bright 1 = some 60 ∧
    GlobalWF (fun _ _ _ => True) Θb ΔovA ∧ GlobalWF (fun _ _ _ => True) Θb ΔovC ∧
    ¬ MkUnique ΔovA ∧ MkProduces ΔovC bright Brightness ∧ ¬ MkProduces ΔovC manual Brightness := by
  refine ⟨by decide, by decide, by decide, GlobalWF.ofList (by decide), GlobalWF.ofList (by decide), fun hu => ?_,
    by decide, by decide⟩
  have := hu Brightness manual auto (by decide) (by decide)
  exact absurd this (by decide)

/-! ## The drive edge is independent of producers -/

def oL : OutputId := ⟨0⟩
def oR : OutputId := ⟨1⟩
def xl : DeclId := ⟨40⟩
def xr : DeclId := ⟨41⟩
def c0 : ClockId := ⟨0⟩
/-- One origin `x : C`, two wires `xl := x`, `xr := x`, two outputs. -/
def Δ2out : DeclEnv := .ofList [⟨x, ⟨.sem C, []⟩, some (.mk C (lit 1))⟩,
  ⟨xl, ⟨.sem C, []⟩, some (.declRef x)⟩, ⟨xr, ⟨.sem C, []⟩, some (.declRef x)⟩]
def Ω2 : OutputEnv := .ofList [(oL, ⟨.sem C, c0⟩), (oR, ⟨.sem C, c0⟩)]
def β2 : DriveEnv := .ofList [(xl, oL), (xr, oR)]
def Κ2 : ClockEnv := fun _ => some c0

/-- **One origin, two outputs, two non-origin drivers**: the design is
    origin-unique, drive-well-formed and single-driver, and neither driver
    originates `C` — so the drive edge cannot be derived from the origin,
    and `SingleDriver` constrains a different object than producer
    uniqueness does. -/
theorem one_origin_two_outputs :
    GlobalWF (fun _ _ _ => True) Θ Δ2out ∧ DriveWF Ω2 Κ2 Δ2out β2 ∧ SingleDriver β2 ∧
    MkProduces Δ2out x C ∧ ¬ MkProduces Δ2out xl C ∧ ¬ MkProduces Δ2out xr C ∧
    β2 x = none ∧ β2 xl = some oL ∧ β2 xr = some oR := by
  refine ⟨GlobalWF.ofList (by decide), DriveWF.ofList (by decide), SingleDriver.ofList (by decide),
    by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem driver_not_origin : MkUnique Δ2out := ProducerUnique.ofList (by decide)

end BDL.Experiments.Producers
