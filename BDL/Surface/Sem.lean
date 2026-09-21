import BDL.Surface.OutputWindow

/-!
# Sem blocks and mapping blocks — the design objects (Phase 21)

The generational reading of the kernel's one object.  A `DesignDecl` of
type `sem C` is a **Sem block**: an instance of the concept `C`, holding one
value per tick.  Its `interface` is the block; its `realization`, when
present, is the **mapping block** attached to it — the one producer of its
value — and when absent the environment provides the value (a Source).  A
**Concept** is the type template Sem blocks are created from
(`SemanticId`, its representation in `Θ`); a **rule** — an arrow-typed
declaration — is the template mapping blocks apply.  Several Sem blocks of
one concept are ordinary (`sensorA, sensorB, roomTemp : Temperature`);
each has its one producer by construction, and no invariant counts them.

The canvas is the bipartite projection of `Δ`: an edge from the mapping
block into its Sem block (the realization, `produces`), and edges from the
Sem blocks a mapping reads into it (`reads`, the kernel's `DependsOn`).
Nothing here adds to the kernel; every theorem is a restatement of Phase
0–1 (write-once realization), Phase 1 (references by identity), Phase 5
(determinism) and Phase 13 (transparency of an unreferenced declaration).

* `IsSem`, `IsRule`, `Instances` — the classification.
* `ProducedBy` (a Sem's producer) — functional (`producedBy_unique`), write-once
  under refinement (`producedBy_refine`), never added by a refinement that
  the design did not make (`producedBy_of_refine`).
* `Reads` = `DependsOn` (`reads_iff_dependsOn`).
* `new_sem_transparent` — creating a Sem block of any concept, unreferenced,
  changes no value in the design.
* `sem_value_det` — a Sem block has one value per tick.
-/

namespace BDL.Sem
open BDL BDL.Reactive BDL.Clock BDL.Provision BDL.OutputWindow

/-- `s` is a Sem block of concept `C`: a declaration whose type is `sem C`. -/
def IsSem (Δ : DeclEnv) (s : DeclId) (C : SemanticId) : Prop := Δ.tyView s = some (.sem C)

instance (Δ : DeclEnv) (s : DeclId) (C : SemanticId) : Decidable (IsSem Δ s C) :=
  inferInstanceAs (Decidable (Δ.tyView s = some (.sem C)))

/-- `r` is a rule: an arrow-typed declaration, the template of mapping blocks. -/
def IsRule (Δ : DeclEnv) (r : DeclId) : Prop := ∃ a b, Δ.tyView r = some (.arr a b)

/-- The Sem blocks of concept `C` among `ids` — its instances. -/
def Instances (ids : List DeclId) (Δ : DeclEnv) (C : SemanticId) : List DeclId :=
  ids.filter fun s => decide (Δ.tyView s = some (.sem C))

theorem mem_instances {ids : List DeclId} {Δ : DeclEnv} {C : SemanticId} {s : DeclId} :
    s ∈ Instances ids Δ C ↔ s ∈ ids ∧ IsSem Δ s C := by
  simp [Instances, IsSem]

/-- The mapping block attached to Sem block `s`: its realization. -/
def ProducedBy (Δ : DeclEnv) (s : DeclId) (m : Expr) : Prop := Δ.realizationOf s = some m

instance (Δ : DeclEnv) (s : DeclId) (m : Expr) : Decidable (ProducedBy Δ s m) :=
  inferInstanceAs (Decidable (Δ.realizationOf s = some m))

/-- **One producer per Sem block** — functional by construction. -/
theorem producedBy_unique {Δ : DeclEnv} {s : DeclId} {m₁ m₂ : Expr}
    (h₁ : ProducedBy Δ s m₁) (h₂ : ProducedBy Δ s m₂) : m₁ = m₂ := by
  unfold ProducedBy at h₁ h₂; rw [h₁] at h₂; exact Option.some.inj h₂

/-- The producer is write-once: a refinement keeps it (FVD-0007). -/
theorem producedBy_refine {Δ₁ Δ₂ : DeclEnv} (er : EnvRefines Δ₁ Δ₂) {s : DeclId} {m : Expr}
    (h : ProducedBy Δ₁ s m) : ProducedBy Δ₂ s m := by
  unfold ProducedBy DeclEnv.realizationOf at h ⊢
  simp only [Option.bind_eq_some_iff] at h ⊢
  obtain ⟨h₁, hd, hr⟩ := h
  obtain ⟨h₂, hd₂, hle⟩ := er s h₁ hd
  exact ⟨h₂, hd₂, hle.2.2 m hr⟩

/-- A Sem block that has a producer after a refinement either had it
    before or received it in the refinement (a `realize` step) — never
    from elsewhere. -/
theorem producedBy_of_refine {Δ₁ Δ₂ : DeclEnv} (er : EnvRefines Δ₁ Δ₂) {s : DeclId} {m : Expr}
    (h : ProducedBy Δ₂ s m) :
    ProducedBy Δ₁ s m ∨ Δ₁.realizationOf s = none := by
  cases hr : Δ₁.realizationOf s with
  | none => exact Or.inr rfl
  | some m₁ =>
    have := producedBy_refine er (s := s) (m := m₁) hr
    exact Or.inl (by rw [producedBy_unique this h] at hr; exact hr)

/-- The Sem blocks (and rules) a mapping block reads: the references of the
    realization it is. -/
def Reads (Δ : DeclEnv) (s d : DeclId) : Prop := ∃ m, ProducedBy Δ s m ∧ d ∈ m.refs

/-- The read edges are the kernel's dependency relation (FVD-0005). -/
theorem reads_iff_dependsOn (Δ : DeclEnv) (s d : DeclId) : Reads Δ s d ↔ DependsOn Δ s d := by
  unfold Reads ProducedBy DependsOn dependsOn
  cases hr : Δ.realizationOf s <;> simp

/-- **Creating a Sem block is transparent**: a new declaration of any
    concept, referenced by nothing, changes no value of any term (Phase 13's
    `update_transparent`).  Several Sem blocks of one concept coexist
    without interaction until a mapping reads them. -/
theorem new_sem_transparent {ev : Evidence} {Θ : ConceptEnv} {S : Sched} {Δ : DeclEnv} {I : Input}
    (g : GlobalWF ev Θ Δ) {s : DeclId} (fresh : Δ s = none) {C : SemanticId} {m : Option Expr}
    (hI : ∀ d t, Avoids s (I d t)) {c : ClockId} {t : Nat} {ex : Expr} {v : Value} (he : s ∉ ex.refs) :
    MEv S Δ I c t [] ex v ↔ MEv S (Δ.update ⟨s, ⟨.sem C, []⟩, m⟩) I c t [] ex v :=
  update_transparent (h := ⟨s, ⟨.sem C, []⟩, m⟩) (NoMention.of_globalWF g fresh) hI he (fun _ hw => by simp at hw)

/-- A Sem block has one value per tick (`MEv.det`). -/
theorem sem_value_det {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat} {s : DeclId} {v₁ v₂ : Value}
    (h₁ : MEv S Δ I c t [] (.declRef s) v₁) (h₂ : MEv S Δ I c t [] (.declRef s) v₂) : v₁ = v₂ :=
  MEv.det h₁ h₂

end BDL.Sem
