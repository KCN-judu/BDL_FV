import BDL.Behavior.Rename
import BDL.Core.Dependency
import BDL.Core.Reactive

/-!
# Interface — designs, ports, and the public boundary of a behaviour

A **design** bundles the five kernel environments of Phases 1–6.  Nothing
new: it is the record a flattened system produces and the record a
component template contains.

A **behaviour interface** is what must be visible to compose a behaviour:
its required and provided semantic ports (declarations, by identity, with
their public `DeclInterface` and clock), its clock parameters, and its
elaboration-time parameters.  Internal declarations are not part of it.
Physical sinks are deliberately *not* ports (§8 of the brief): a port
connects behaviours; a sink connects a behaviour to the world.
-/

namespace BDL
open BDL.Output (OutputId OutputSpec OutputEnv DriveEnv DriveWF SingleDriver CompleteOutputs)
open BDL.Clock (ClockEnv Clocked WellClocked)

/-- A finite BDL design: the kernel environments of Phases 1–6 together. -/
structure Design where
  Δ : DeclEnv
  Θ : ConceptEnv
  Κ : ClockEnv
  Ω : OutputEnv
  β : DriveEnv

/-- **Structural well-formedness** of a design: exactly the Phase 1–6
    acceptance conditions, no more.  Required sinks are not part of it
    (openness is allowed); see `Design.Executable`. -/
structure Design.WF (ev : Evidence) (D : Design) : Prop where
  global  : GlobalWF ev D.Θ D.Δ
  concepts : D.Θ.WF
  clocked : WellClocked D.Κ D.Δ
  causal  : Causal D.Δ
  drives  : DriveWF D.Ω D.Κ D.Δ D.β
  single  : SingleDriver D.β

/-- The declarations of a design that are unresolved (inputs / open ports). -/
def Design.Open (D : Design) (d : DeclId) : Prop :=
  ∃ h, D.Δ d = some h ∧ h.realization = none

/-- **Executable closed system**: structurally well formed, every required
    sink driven, and every declaration realized except those listed as the
    system's external inputs. -/
structure Design.Executable (ev : Evidence) (D : Design) (inputs : List DeclId) (req : List OutputId) : Prop where
  wf : D.WF ev
  complete : CompleteOutputs D.β req
  closed : ∀ d, D.Open d → d ∈ inputs

/-! ## Ports and interfaces -/

/-- A semantic port: a declaration of the component, by local identity, with
    the public part of its interface and its (parameter) clock. -/
structure Port where
  id    : DeclId
  iface : DeclInterface
  clock : Option ClockId
  deriving DecidableEq, Repr

/-- The public boundary of a reusable behaviour. -/
structure BehaviorInterface where
  /-- Ports the behaviour needs: unresolved declarations to be bound by a composer. -/
  required : List Port
  /-- Ports the behaviour offers to others. -/
  provided : List Port
  /-- Elaboration-time parameters: unresolved data-typed declarations to be
      bound to closed constants at instantiation. -/
  params : List Port
  /-- Clock parameters: the domains the behaviour is written against, to be
      mapped to system domains at instantiation. -/
  clockParams : List ClockId
  deriving Repr

/-- Interface refinement for substitutability (§22).  `B` may replace `A` when
    every port `A` provides, `B` provides with the same type and clock and at
    least the same commitments; every port `A` requires, `B` still requires
    with the same type and clock and at most the same commitments (so any
    binding that satisfied `A`'s need satisfies `B`'s); parameters likewise;
    and the clock parameters coincide.  `B` may require *additional* ports:
    they stay open. -/
structure IfaceRefines (A B : BehaviorInterface) : Prop where
  provided : ∀ p ∈ A.provided, ∃ p' ∈ B.provided,
    p'.id = p.id ∧ p'.iface.expectedType = p.iface.expectedType ∧
    p.iface.commitments ⊆ p'.iface.commitments ∧ p'.clock = p.clock
  required : ∀ p ∈ A.required, ∃ p' ∈ B.required,
    p'.id = p.id ∧ p'.iface.expectedType = p.iface.expectedType ∧
    p'.iface.commitments ⊆ p.iface.commitments ∧ p'.clock = p.clock
  params : ∀ p ∈ A.params, ∃ p' ∈ B.params,
    p'.id = p.id ∧ p'.iface.expectedType = p.iface.expectedType ∧
    p'.iface.commitments ⊆ p.iface.commitments ∧ p'.clock = p.clock
  clocks : A.clockParams = B.clockParams

theorem IfaceRefines.refl (A : BehaviorInterface) : IfaceRefines A A :=
  ⟨fun p hp => ⟨p, hp, rfl, rfl, List.Subset.refl _, rfl⟩,
   fun p hp => ⟨p, hp, rfl, rfl, List.Subset.refl _, rfl⟩,
   fun p hp => ⟨p, hp, rfl, rfl, List.Subset.refl _, rfl⟩, rfl⟩

end BDL
