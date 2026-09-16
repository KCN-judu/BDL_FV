import BDL.Behavior.Group
import BDL.Behavior.Component

/-!
# Boundary — projections of a group and boundary inference (Phase 8b)

Everything here is *derived* from the design and a member list, using the
existing declaration-based dependency relation `DependsOn` (Phase 1).  No
socket, aggregate input, or aggregate output is a declaration; each is a
list computed from the members' bodies.

A finite design is enumerated by a list `ids` of its declared identities.
-/

namespace BDL
open BDL.Output (OutputId)

/-- `ids` enumerates exactly the declared identities of `D`. -/
def Design.Enumerates (D : Design) (ids : List DeclId) : Prop :=
  ids.Nodup ∧ ∀ d, (∃ h, D.Δ d = some h) ↔ d ∈ ids

namespace Boundary

variable (D : Design) (ids G : List DeclId)

/-- Non-members among the enumerated declarations. -/
def outside : List DeclId := ids.filter fun d => !G.contains d

/-- **Crossing-in**: non-members some member depends on.  These are the
    external inputs of the group as a *projection*, not a port. -/
def crossIn : List DeclId :=
  (outside ids G).filter fun r => G.any fun m => dependsOn D.Δ m r

/-- **Crossing-out**: members some non-member depends on. -/
def crossOut : List DeclId :=
  G.filter fun p => (outside ids G).any fun u => dependsOn D.Δ u p

/-- Members with no realization (the group's open inputs). -/
def openMembers : List DeclId :=
  G.filter fun m => decide (D.Δ.realizationOf m = none)

/-- Members that drive a physical sink. -/
def drivenMembers : List DeclId :=
  G.filter fun m => decide (D.β m ≠ none)

/-- Internal edges: producer and consumer both in the group. -/
def InternalEdge (a b : DeclId) : Prop := a ∈ G ∧ b ∈ G ∧ DependsOn D.Δ a b

/-- Members neither exported nor driving a sink: private candidates. -/
def privateMembers : List DeclId :=
  G.filter fun m => !(crossOut D ids G).contains m && decide (D.β m = none)

/-- The externally visible input summary: crossing-in declarations and open
    members.  A view, not a declaration. -/
def externalInputs : List DeclId := crossIn D ids G ++ openMembers D G

/-- The externally visible output summary: crossing-out declarations.
    Physical sinks are reported separately (`drivenMembers`) and are never
    turned into semantic ports. -/
def externalOutputs : List DeclId := crossOut D ids G

/-- Clocks used by the enumerated declarations: the clock-parameter
    candidates.  Under extraction *every* used clock becomes a parameter; a
    group owns no domain. -/
def clocksOf : List ClockId := ids.filterMap D.Κ

/-! ## Characterizations (Theorems I–L, projection level) -/

theorem mem_outside {d : DeclId} : d ∈ outside ids G ↔ d ∈ ids ∧ d ∉ G := by
  simp [outside, List.mem_filter]

/-- **Theorem I / K.**  A declaration is crossing-in exactly when it is a
    non-member that some member depends on. -/
theorem mem_crossIn {r : DeclId} :
    r ∈ crossIn D ids G ↔ r ∈ ids ∧ r ∉ G ∧ ∃ m ∈ G, DependsOn D.Δ m r := by
  simp [crossIn, List.mem_filter, mem_outside, List.any_eq_true, DependsOn, and_assoc]

/-- **Theorem I / L.**  A declaration is crossing-out exactly when it is a
    member that some non-member depends on. -/
theorem mem_crossOut {p : DeclId} :
    p ∈ crossOut D ids G ↔ p ∈ G ∧ ∃ u, u ∈ ids ∧ u ∉ G ∧ DependsOn D.Δ u p := by
  simp [crossOut, List.mem_filter, mem_outside, List.any_eq_true, DependsOn, and_assoc]

/-- **Theorem J (projection level).**  An internal edge never makes its
    producer crossing-in: internal dependencies are not required inputs. -/
theorem internal_not_crossIn {a b : DeclId} (h : InternalEdge D G a b) : b ∉ crossIn D ids G := by
  intro hb
  exact ((mem_crossIn D ids G).mp hb).2.1 h.2.1

/-- A member all of whose consumers are members is private (given it
    drives no sink): it is not crossing-out. -/
theorem internal_only_not_crossOut {p : DeclId}
    (hint : ∀ u, DependsOn D.Δ u p → u ∈ G) : p ∉ crossOut D ids G := by
  intro h
  obtain ⟨-, u, -, hu, hdep⟩ := (mem_crossOut D ids G).mp h
  exact hu (hint u hdep)

theorem mem_privateMembers {p : DeclId} :
    p ∈ privateMembers D ids G ↔ p ∈ G ∧ p ∉ crossOut D ids G ∧ D.β p = none := by
  simp [privateMembers, List.mem_filter]

/-- Crossing lists are sublists of nodup lists, hence nodup. -/
theorem crossIn_nodup (h : ids.Nodup) : (crossIn D ids G).Nodup :=
  (h.filter _).filter _

theorem crossOut_nodup (h : G.Nodup) : (crossOut D ids G).Nodup := h.filter _

/-- **Theorem H.**  Aggregate sockets add no dependency: membership of `r`
    in the input socket says only that *some* member depends on `r`; it
    does not make any other member depend on `r`.  The dependency relation
    is the design's own and is untouched. -/
theorem socket_no_fanout {r m : DeclId} (hr : r ∈ crossIn D ids G)
    (hnot : ¬ DependsOn D.Δ m r) : ¬ DependsOn D.Δ m r ∧ ∃ m' ∈ G, DependsOn D.Δ m' r :=
  ⟨hnot, ((mem_crossIn D ids G).mp hr).2.2⟩

end Boundary
end BDL
