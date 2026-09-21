import BDL.Surface.Sem
import BDL.Experiments.ProducerAlternatives

/-!
# Phase 21 — the Sem-block reading on the development's designs

* `lamp_picture` — the canvas of the brief: a Source Sem `pressed : Pressed`,
  a rule `lit : Pressed -> Lit`, and the Sem block `Lit := lit(pressed)`;
  the mapping block is `Lit`'s realization, its read edges are `pressed`
  and the rule, and `Lit` is on when `pressed` is.
* `rule_template` — one rule, two mapping blocks, two Sem blocks of `Lit`:
  a rule is to mapping blocks what a concept is to Sem blocks.
* `sensors_natural` — Phase 19's redundant sensors in their natural form:
  three Sem blocks of `Temperature`, two provided by the environment and
  one produced by a selection; `hot` reads the selection; the trace is the
  one Phase 19 executed.  No intermediate concept.
* `judgment_optional` — the natural form is well formed and not
  `ProducerUnique`; Phase 19's intermediate-concept form is.  Phase 20's
  invariant is a choice a design may make, not a condition it must meet.
-/

namespace BDL.Experiments.Sem
open BDL BDL.Reactive BDL.Clock BDL.Stdlib BDL.Sem

def Pressed : ConceptId := ⟨501⟩
def Lit : ConceptId := ⟨502⟩
def Θpl : ConceptEnv := fun s => if s = Pressed ∨ s = Lit then some .bool else none
def pressed : DeclId := ⟨50⟩
def lit : DeclId := ⟨51⟩
def litV : DeclId := ⟨52⟩
def pressedB : DeclId := ⟨53⟩
def litB : DeclId := ⟨54⟩

/-- The rule: `lit : Pressed -> Lit := λ p. mk Lit (rep p)`. -/
def litRule : Expr := .lam (.sem Pressed) (.mk Lit (.rep (.var 0)))
/-- The mapping block: the rule applied to the Sem block `pressed`. -/
def litMapping : Expr := .app (.declRef lit) (.declRef pressed)

def Δpl : DeclEnv := .ofList [
  ⟨pressed, ⟨.sem Pressed, []⟩, none⟩,
  ⟨lit, ⟨.arr (.sem Pressed) (.sem Lit), []⟩, some litRule⟩,
  ⟨litV, ⟨.sem Lit, []⟩, some litMapping⟩]

def Ipl (b : Bool) : Input := fun d _ => if d = pressed then .sem Pressed (.bool b) else .nat 0

def readLit (Δ : DeclEnv) (I : Input) (d : DeclId) : Option Bool :=
  (evalF Δ I 16 0 [] (.declRef d)).bind fun v => match v with | .sem _ (.bool b) => some b | _ => none

/-- **The picture.**  `pressed` is a Sem block of `Pressed` with no
    producer (the environment's); `lit` is a rule; `Lit` is a Sem block whose
    producer is the mapping `lit(pressed)`, which reads `pressed` and the
    rule; the light follows the button. -/
theorem lamp_picture :
    GlobalWF (fun _ _ _ => True) Θpl Δpl ∧ Causal Δpl ∧
    IsSem Δpl pressed Pressed ∧ Δpl.realizationOf pressed = none ∧
    IsRule Δpl lit ∧ IsSem Δpl litV Lit ∧ ProducedBy Δpl litV litMapping ∧
    Reads Δpl litV pressed ∧ Reads Δpl litV lit ∧ ¬ Reads Δpl litV litV ∧
    readLit Δpl (Ipl true) litV = some true ∧ readLit Δpl (Ipl false) litV = some false := by
  refine ⟨GlobalWF.ofList (by decide),
    Causal.ofList (fun d => if d = litV then 1 else 0) 2 (by intro d; split <;> omega) (by decide),
    by decide, by decide, ⟨.sem Pressed, .sem Lit, by decide⟩, by decide, by decide,
    (reads_iff_dependsOn _ _ _).mpr (by decide), (reads_iff_dependsOn _ _ _).mpr (by decide),
    fun h => absurd ((reads_iff_dependsOn _ _ _).mp h) (by decide), by decide, by decide⟩

def Δ2 : DeclEnv := .ofList [
  ⟨pressed, ⟨.sem Pressed, []⟩, none⟩, ⟨pressedB, ⟨.sem Pressed, []⟩, none⟩,
  ⟨lit, ⟨.arr (.sem Pressed) (.sem Lit), []⟩, some litRule⟩,
  ⟨litV, ⟨.sem Lit, []⟩, some litMapping⟩,
  ⟨litB, ⟨.sem Lit, []⟩, some (.app (.declRef lit) (.declRef pressedB))⟩]

/-- **A rule is a template**: applied twice it makes two mapping blocks
    producing two Sem blocks of `Lit`, each with its one producer. -/
theorem rule_template :
    GlobalWF (fun _ _ _ => True) Θpl Δ2 ∧
    Instances [pressed, pressedB, lit, litV, litB] Δ2 Lit = [litV, litB] ∧
    Instances [pressed, pressedB, lit, litV, litB] Δ2 Pressed = [pressed, pressedB] ∧
    ProducedBy Δ2 litV litMapping ∧ ProducedBy Δ2 litB (.app (.declRef lit) (.declRef pressedB)) := by
  refine ⟨GlobalWF.ofList (by decide), by decide, by decide, by decide, by decide⟩

open BDL.Experiments.Producers in
/-- **Redundant sensors, natural form** (Phase 19's `ΔsensA`): three Sem
    blocks of `Temperature`, the third produced by a selection over the
    first two; `hot` reads it; the executed trace of Phase 19. -/
theorem sensors_natural :
    Instances [tA, tB, availA, temp, hot] ΔsensA Temperature = [tA, tB, temp] ∧
    ΔsensA.realizationOf tA = none ∧ ΔsensA.realizationOf tB = none ∧
    ProducedBy ΔsensA temp (iteE (.sem Temperature) (.declRef availA) (.declRef tA) (.declRef tB)) ∧
    Reads ΔsensA hot temp ∧ Reads ΔsensA temp tA ∧ Reads ΔsensA temp tB ∧
    readB ΔsensA IsA hot 1 = some true ∧ readB ΔsensA IsA hot 2 = some false := by
  refine ⟨by decide, by decide, by decide, by decide,
    (reads_iff_dependsOn _ _ _).mpr (by decide), (reads_iff_dependsOn _ _ _).mpr (by decide),
    (reads_iff_dependsOn _ _ _).mpr (by decide), by decide, by decide⟩

open BDL.Experiments.Producers in
/-- **Phase 20's invariant is optional**: the natural form is well formed
    and has three origins of `Temperature`; the intermediate-concept form
    has one.  A design chooses. -/
theorem judgment_optional :
    GlobalWF (fun _ _ _ => True) Θt ΔsensA ∧ ¬ ProducerUnique ΔsensA ∧ ProducerUnique ΔsensC :=
  ⟨GlobalWF.ofList (by decide), sensors_rewriting_same_trace.2.2.2.2.2.1, sensorsC_mkUnique⟩

end BDL.Experiments.Sem
