import BDL.Behavior.Interface

/-!
# Group — behaviour grouping is authoring metadata (Phase 8b)

A `BehaviorGroup` records that a designer has gathered some declarations
into one cognitive unit.  It carries an identity and a member list and
nothing else: no types, formulas, clocks, outputs, or semantics — those
remain properties of the member declarations.

A `GroupedDesign` is an ordinary `Design` together with a list of groups.
`eraseGroups` forgets the groups.  Every group operation (group, ungroup,
add/remove member, move, merge, split) changes the group list only, so
every kernel judgment — typing, satisfaction, causality, clocks, outputs,
evaluation — is *literally* the judgment of the underlying design.  The
theorems below are therefore reuses, not re-proofs: that is the content of
"grouping is semantically transparent".
-/

namespace BDL
open BDL.Output (OutputId DriveWF SingleDriver CompleteOutputs)
open BDL.Clock (WellClocked)

structure GroupId where
  n : Nat
  deriving DecidableEq, Repr

/-- An authoring group: an identity and its members.  Nothing semantic. -/
structure BehaviorGroup where
  id : GroupId
  members : List DeclId
  deriving DecidableEq, Repr

/-- A design with authoring groups laid over it. -/
structure GroupedDesign where
  design : Design
  groups : List BehaviorGroup

namespace GroupedDesign

/-- Forget the groups. -/
def eraseGroups (GD : GroupedDesign) : Design := GD.design

/-! ## Group operations — all act on `groups` only -/

/-- Group some declarations under a fresh group identity. -/
def group (GD : GroupedDesign) (g : GroupId) (members : List DeclId) : GroupedDesign :=
  { GD with groups := ⟨g, members⟩ :: GD.groups }

/-- Dissolve a group. -/
def ungroup (GD : GroupedDesign) (g : GroupId) : GroupedDesign :=
  { GD with groups := GD.groups.filter (·.id ≠ g) }

def addMember (GD : GroupedDesign) (g : GroupId) (d : DeclId) : GroupedDesign :=
  { GD with groups := GD.groups.map fun G => if G.id = g then { G with members := d :: G.members } else G }

def removeMember (GD : GroupedDesign) (g : GroupId) (d : DeclId) : GroupedDesign :=
  { GD with groups := GD.groups.map fun G => if G.id = g then { G with members := G.members.filter (· ≠ d) } else G }

/-- Move a declaration from one group to another (either may be absent:
    ungrouped → grouped, grouped → ungrouped). -/
def move (GD : GroupedDesign) (src dst : GroupId) (d : DeclId) : GroupedDesign :=
  (GD.removeMember src d).addMember dst d

/-- Merge two groups into the first (authoring set union). -/
def merge (GD : GroupedDesign) (g₁ g₂ : GroupId) : GroupedDesign :=
  let m₂ := ((GD.groups.filter (·.id = g₂)).map (·.members)).flatten
  { GD with groups := (GD.groups.filter (·.id ≠ g₂)).map fun G =>
      if G.id = g₁ then { G with members := G.members ++ m₂ } else G }

/-- Split a group: members satisfying `p` move to a fresh group `g'`. -/
def split (GD : GroupedDesign) (g g' : GroupId) (p : DeclId → Bool) : GroupedDesign :=
  let moved := ((GD.groups.filter (·.id = g)).map fun G => G.members.filter p).flatten
  { GD with groups := ⟨g', moved⟩ :: GD.groups.map fun G =>
      if G.id = g then { G with members := G.members.filter (fun d => !p d) } else G }

/-! ## Theorem A — grouping erasure, and the round trips -/

@[simp] theorem eraseGroups_group (GD : GroupedDesign) (g : GroupId) (m : List DeclId) :
    (GD.group g m).eraseGroups = GD.eraseGroups := rfl
@[simp] theorem eraseGroups_ungroup (GD : GroupedDesign) (g : GroupId) :
    (GD.ungroup g).eraseGroups = GD.eraseGroups := rfl
@[simp] theorem eraseGroups_addMember (GD : GroupedDesign) (g : GroupId) (d : DeclId) :
    (GD.addMember g d).eraseGroups = GD.eraseGroups := rfl
@[simp] theorem eraseGroups_removeMember (GD : GroupedDesign) (g : GroupId) (d : DeclId) :
    (GD.removeMember g d).eraseGroups = GD.eraseGroups := rfl
@[simp] theorem eraseGroups_move (GD : GroupedDesign) (s t : GroupId) (d : DeclId) :
    (GD.move s t d).eraseGroups = GD.eraseGroups := rfl
@[simp] theorem eraseGroups_merge (GD : GroupedDesign) (g₁ g₂ : GroupId) :
    (GD.merge g₁ g₂).eraseGroups = GD.eraseGroups := rfl
@[simp] theorem eraseGroups_split (GD : GroupedDesign) (g g' : GroupId) (p : DeclId → Bool) :
    (GD.split g g' p).eraseGroups = GD.eraseGroups := rfl

/-- **Theorem A.**  `eraseGroups (group D G) = D`. -/
theorem erase_group (D : Design) (g : GroupId) (m : List DeclId) :
    (GroupedDesign.group ⟨D, []⟩ g m).eraseGroups = D := rfl

/-- **Theorem B.**  Group then ungroup: the design is unchanged; and, at the
    metadata level, a group with a fresh identity is removed exactly. -/
theorem erase_ungroup_group (GD : GroupedDesign) (g : GroupId) (m : List DeclId) :
    ((GD.group g m).ungroup g).eraseGroups = GD.eraseGroups := rfl

theorem ungroup_group_groups (GD : GroupedDesign) (g : GroupId) (m : List DeclId)
    (hfresh : ∀ G ∈ GD.groups, G.id ≠ g) : ((GD.group g m).ungroup g).groups = GD.groups := by
  simp only [group, ungroup, List.filter_cons, decide_not, decide_true, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  exact List.filter_eq_self.mpr fun G hG => by simp [hfresh G hG]

/-- **Theorem C.**  Moving a declaration between groups (in either
    direction, including to or from "ungrouped") is a semantic no-op. -/
theorem move_erase (GD : GroupedDesign) (s t : GroupId) (d : DeclId) :
    (GD.move s t d).eraseGroups = GD.eraseGroups := rfl

/-! ## Theorems D–G — transparency to every kernel judgment

Each is the judgment on the erased design; the statements say that the
*same* proposition holds before and after any group operation.  They are
`Iff.rfl` because the operations do not touch `design`. -/

/-- The kernel judgments of a grouped design, bundled. -/
structure Judgments (ev : Evidence) (D : Design) : Prop where
  typed   : GlobalWF ev D.Θ D.Δ
  causal  : Causal D.Δ
  clocked : WellClocked D.Κ D.Δ
  drives  : DriveWF D.Ω D.Κ D.Δ D.β
  single  : SingleDriver D.β

theorem judgments_group (ev : Evidence) (GD : GroupedDesign) (g : GroupId) (m : List DeclId) :
    Judgments ev (GD.group g m).eraseGroups ↔ Judgments ev GD.eraseGroups := Iff.rfl
theorem judgments_move (ev : Evidence) (GD : GroupedDesign) (s t : GroupId) (d : DeclId) :
    Judgments ev (GD.move s t d).eraseGroups ↔ Judgments ev GD.eraseGroups := Iff.rfl
theorem judgments_merge (ev : Evidence) (GD : GroupedDesign) (g₁ g₂ : GroupId) :
    Judgments ev (GD.merge g₁ g₂).eraseGroups ↔ Judgments ev GD.eraseGroups := Iff.rfl
theorem judgments_split (ev : Evidence) (GD : GroupedDesign) (g g' : GroupId) (p : DeclId → Bool) :
    Judgments ev (GD.split g g' p).eraseGroups ↔ Judgments ev GD.eraseGroups := Iff.rfl

/-- **Theorem D (typing).** -/
theorem typing_group (ev : Evidence) (GD : GroupedDesign) (g : GroupId) (m : List DeclId) :
    GlobalWF ev (GD.group g m).design.Θ (GD.group g m).design.Δ ↔ GlobalWF ev GD.design.Θ GD.design.Δ := Iff.rfl
/-- **Theorem E (causality).** -/
theorem causal_group (GD : GroupedDesign) (g : GroupId) (m : List DeclId) :
    Causal (GD.group g m).design.Δ ↔ Causal GD.design.Δ := Iff.rfl
/-- **Theorem F (clocks).** -/
theorem clocked_group (GD : GroupedDesign) (g : GroupId) (m : List DeclId) :
    WellClocked (GD.group g m).design.Κ (GD.group g m).design.Δ ↔ WellClocked GD.design.Κ GD.design.Δ := Iff.rfl
/-- **Theorem G (outputs).** -/
theorem outputs_group (GD : GroupedDesign) (g : GroupId) (m : List DeclId) (req : List OutputId) :
    (DriveWF (GD.group g m).design.Ω (GD.group g m).design.Κ (GD.group g m).design.Δ (GD.group g m).design.β ∧
      SingleDriver (GD.group g m).design.β ∧ CompleteOutputs (GD.group g m).design.β req) ↔
    (DriveWF GD.design.Ω GD.design.Κ GD.design.Δ GD.design.β ∧ SingleDriver GD.design.β ∧
      CompleteOutputs GD.design.β req) := Iff.rfl

/-- Dependency edges are untouched by grouping (the *only* dependency
    notion in BDL is declaration-based; a group adds none). -/
theorem dependsOn_group (GD : GroupedDesign) (g : GroupId) (m : List DeclId) (a b : DeclId) :
    DependsOn (GD.group g m).design.Δ a b ↔ DependsOn GD.design.Δ a b := Iff.rfl
theorem instDependsOn_group (GD : GroupedDesign) (g : GroupId) (m : List DeclId) (a b : DeclId) :
    InstDependsOn (GD.group g m).design.Δ a b ↔ InstDependsOn GD.design.Δ a b := Iff.rfl

/-! ## Invalidation classification

Phase 1 distinguishes *refinement* (preserves everything), *edit*
(may invalidate dependents), and validation-only changes.  Grouping is a
fourth, trivial kind: it changes no component of the design at all, so it
is not even a validation-only change.  Formally: every group operation is
the identity on `design`, hence on `EnvRefines`, `ConceptRefines`, the
clock and output projections, and any evaluation. -/

theorem group_is_identity_on_design (GD : GroupedDesign) (g : GroupId) (m : List DeclId) :
    (GD.group g m).design = GD.design ∧ (GD.ungroup g).design = GD.design ∧
    (∀ d, (GD.addMember g d).design = GD.design ∧ (GD.removeMember g d).design = GD.design) ∧
    (∀ g₂, (GD.merge g g₂).design = GD.design) ∧
    (∀ g' p, (GD.split g g' p).design = GD.design) :=
  ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ _ => rfl⟩

theorem group_envRefines (GD : GroupedDesign) (g : GroupId) (m : List DeclId) :
    EnvRefines GD.design.Δ (GD.group g m).design.Δ ∧ EnvRefines (GD.group g m).design.Δ GD.design.Δ :=
  ⟨EnvRefines.refl _, EnvRefines.refl _⟩

/-! ## Nested groups

A nested visual group is a group whose members are members of another
group.  No recursive structure is needed: nesting is a relation on the
flat group list, and it carries no kernel significance because no group
does. -/

def NestedIn (G H : BehaviorGroup) : Prop := ∀ d ∈ G.members, d ∈ H.members

theorem nested_no_semantics (GD : GroupedDesign) (G H : BehaviorGroup) (_ : NestedIn G H) :
    GD.eraseGroups = GD.design := rfl

end GroupedDesign
end BDL
