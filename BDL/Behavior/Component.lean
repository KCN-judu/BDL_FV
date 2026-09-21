import BDL.Behavior.Interface

/-!
# Component — a reusable behaviour is a template over local identities

A `BehaviorComponent` is an interface together with an ordinary BDL design
over *local* identities, all below `width`.  It is not a kernel term: it is
a surface object that elaborates, by renaming (instantiation), into ordinary
declarations.  `Realizes` is the predicate that the internal design realizes
the interface — checked once, for the template; every instance inherits it
(`Preservation.lean`).

Three kinds of identity inside a template are *internal* and are freshened
at every instantiation: all of its declarations, the concepts it
flags as private, and the physical sinks it flags as private.  Everything
else is *global*: shared concepts (`Tilt`), external sinks, and the clock
parameters, which the composer maps to system domains.
-/

namespace BDL
open BDL.Output (OutputId OutputSpec)
open BDL.Clock (ClockEnv)

structure BehaviorComponent where
  iface  : BehaviorInterface
  design : Design
  /-- Every local identity of the template is below `width`. -/
  width  : Nat
  /-- Concepts private to the behaviour (freshened per instance).  All others
      are shared with the system and are never renamed. -/
  internalConcept : ConceptId → Bool
  /-- Sinks private to the behaviour (freshened per instance).  All others
      are external and may be driven by at most one instance in a system. -/
  internalOut : OutputId → Bool

namespace BehaviorComponent

/-- A clock is internal to the template unless it is a declared parameter. -/
def internalClock (C : BehaviorComponent) (c : ClockId) : Bool :=
  !(C.iface.clockParams.contains c)

/-- The port of the interface with identity `d`, if any, among a port list. -/
def findPort (ps : List Port) (d : DeclId) : Option Port := ps.find? (·.id = d)

/-- **A component realizes its interface.**  Everything a composer will rely
    on, stated on the template alone (no instance identity appears):

    * the internal design is structurally well formed (Phases 1–6);
    * every identity the template owns is below `width`, so that instance
      renaming is injective and decodable;
    * concepts bound by the template are its own; shared concepts are left
      to the system (and must agree with it, see `ComposeWF`);
    * every port is a declaration of the design with exactly the public
      interface and clock the port advertises; required ports and
      parameters are unresolved; parameters are data-typed and agnostic. -/
structure Realizes (ev : Evidence) (C : BehaviorComponent) : Prop where
  wf : C.design.WF ev
  declBound : ∀ d h, C.design.Δ d = some h → d.n < C.width
  clockBound : ∀ d c, C.design.Κ d = some c → C.internalClock c = true → c.n < C.width
  clockDeclared : ∀ d c, C.design.Κ d = some c → ∃ h, C.design.Δ d = some h
  conceptBound : ∀ s R, C.design.Θ s = some R → C.internalConcept s = true → s.n < C.width
  outBound : ∀ o spec, C.design.Ω o = some spec → C.internalOut o = true → o.n < C.width
  driveDeclared : ∀ d o, C.design.β d = some o → ∃ h, C.design.Δ d = some h
  required : ∀ p ∈ C.iface.required, C.design.Δ p.id = some ⟨p.id, p.iface, none⟩ ∧ C.design.Κ p.id = p.clock
  provided : ∀ p ∈ C.iface.provided, (∃ h, C.design.Δ p.id = some h ∧ h.interface = p.iface) ∧ C.design.Κ p.id = p.clock
  params : ∀ p ∈ C.iface.params, C.design.Δ p.id = some ⟨p.id, p.iface, none⟩ ∧ C.design.Κ p.id = p.clock ∧ p.clock = none ∧ p.iface.expectedType.Data

end BehaviorComponent

end BDL
