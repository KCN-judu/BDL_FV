import BDL.Core.Output

/-!
# Hardware — declarative resource model, constraint validity, and a solver (Phase 7)

This is a **validation layer**: nothing here enters `Ty`, `HasType`, the
reactive semantics, or the drive edges.  Feasibility is a relation between a
design's *requirements* and a *target's* resources.

* `ResourceId`, `Resource`   — what a board provides: capabilities, and a
                               *unit* tag per capability (timer, peripheral).
* `Hardware`                 — a finite list of resources plus a
                               capability-specific sharing policy.
* `RequirementId`, `Requirement` — what a design needs: one capability,
                               optionally a fixed resource, optionally a
                               unit relation to other requirements.
* `Assignment`               — pairs (requirement, resource).
* `PartialValid` / `ValidFor`— validity: every entry supported (capability,
                               fixed choice) and every pair compatible
                               (exclusive vs shared; same-unit or distinct-unit).
* `solve`                    — exhaustive DFS; `solve_sound`, `solve_complete`,
                               hence `HardwareSatisfiable` is decidable.
* `Hardware.Extends`         — monotone hardware refinement preserves validity.
* `diagnose`                 — a structured first-dead-end explanation.

The board description carries every board-specific fact; the solver never
mentions a pin or a protocol.
-/

namespace BDL.Hardware

/-! ## Vocabulary -/

/-- Capabilities a resource may offer / a requirement may ask for.  A shared
    vocabulary between board descriptions and device descriptions; the
    solver treats it as an opaque decidable type. -/
inductive Capability where
  | digitalIn | digitalOut | pwm | analogIn | interrupt
  | i2cSDA | i2cSCL | spiMOSI | spiMISO | spiSCK | spiSS | uartTX | uartRX
  deriving DecidableEq, Repr

structure ResourceId where
  n : Nat
  deriving DecidableEq, Repr

/-- A resource: its capabilities and, per capability, the *unit* that
    capability is backed by (a timer, a peripheral controller).  `unit` is
    what grouped and independent requirements are about. -/
structure Resource where
  id    : ResourceId
  caps  : List Capability
  units : List (Capability × Nat) := []
  deriving DecidableEq, Repr

def Resource.unitOf (r : Resource) (c : Capability) : Option Nat :=
  (r.units.find? fun p => p.1 = c).map Prod.snd

/-- A target: its resources and which capabilities may be shared by several
    requirements (buses) — everything else is exclusive. -/
structure Hardware where
  resources : List Resource
  shareable : List Capability := []
  deriving DecidableEq, Repr

def Hardware.find (H : Hardware) (r : ResourceId) : Option Resource :=
  H.resources.find? fun res => res.id = r

def Hardware.unitOf (H : Hardware) (r : ResourceId) (c : Capability) : Option Nat :=
  (H.find r).bind fun res => res.unitOf c

/-- `Supports H r c`: resource `r` offers capability `c` — a board fact. -/
def Supports (H : Hardware) (r : ResourceId) (c : Capability) : Prop :=
  ∃ res, H.find r = some res ∧ c ∈ res.caps

instance (H : Hardware) (r : ResourceId) (c : Capability) : Decidable (Supports H r c) := by
  unfold Supports
  cases H.find r with
  | none => exact isFalse (by simp)
  | some res => exact decidable_of_iff (c ∈ res.caps) (by simp)

/-! ## Requirements -/

structure RequirementId where
  n : Nat
  deriving DecidableEq, Repr

/-- A relation between requirements about the *unit* backing them. -/
inductive UnitRel where
  | same       -- e.g. TX and RX of one UART
  | distinct   -- e.g. PWM channels that need independent timers
  deriving DecidableEq, Repr

/-- What a design needs: one capability; optionally a fixed resource (manual
    pin choice); optionally membership in a unit-relation group. -/
structure Requirement where
  id    : RequirementId
  cap   : Capability
  fixed : Option ResourceId := none
  group : Option (Nat × UnitRel) := none
  deriving DecidableEq, Repr

abbrev Requirements := List Requirement

/-- Unary validity of one entry. -/
def ReqOK (H : Hardware) (req : Requirement) (r : ResourceId) : Prop :=
  Supports H r req.cap ∧ ∀ f, req.fixed = some f → f = r

instance (H : Hardware) (req : Requirement) (r : ResourceId) : Decidable (ReqOK H req r) := by
  unfold ReqOK
  cases hf : req.fixed with
  | none => exact decidable_of_iff (Supports H r req.cap) (by simp)
  | some f => exact decidable_of_iff (Supports H r req.cap ∧ f = r) (by simp)

/-- Binary compatibility of two entries.
    * Same resource: only if both ask the same capability and it is shareable.
    * Same unit-group: `same` ⇒ equal units; `distinct` ⇒ different units. -/
def Compatible (H : Hardware) (a b : Requirement × ResourceId) : Prop :=
  (a.2 = b.2 → a.1.cap = b.1.cap ∧ a.1.cap ∈ H.shareable) ∧
  (∀ g rel, a.1.group = some (g, rel) → b.1.group = some (g, rel) →
    match rel with
    | .same => H.unitOf a.2 a.1.cap = H.unitOf b.2 b.1.cap
    | .distinct => H.unitOf a.2 a.1.cap ≠ H.unitOf b.2 b.1.cap)

instance (H : Hardware) (a b : Requirement × ResourceId) : Decidable (Compatible H a b) := by
  unfold Compatible
  refine @instDecidableAnd _ _ ?_ ?_
  · exact inferInstance
  · cases ha : a.1.group with
    | none => exact isTrue (fun _ _ h => by simp at h)
    | some p =>
      cases hb : b.1.group with
      | none => exact isTrue (fun _ _ _ h => by simp at h)
      | some q =>
        by_cases hpq : p = q
        · subst hpq
          obtain ⟨g, rel⟩ := p
          cases rel with
          | same =>
            exact decidable_of_iff (H.unitOf a.2 a.1.cap = H.unitOf b.2 b.1.cap)
              ⟨fun h _ _ h₁ h₂ => by cases h₁; cases h₂; exact h, fun h => h g .same rfl rfl⟩
          | distinct =>
            exact decidable_of_iff (H.unitOf a.2 a.1.cap ≠ H.unitOf b.2 b.1.cap)
              ⟨fun h _ _ h₁ h₂ => by cases h₁; cases h₂; exact h, fun h => h g .distinct rfl rfl⟩
        · exact isTrue (fun _ _ h₁ h₂ => by cases h₁; cases h₂; exact absurd rfl hpq)

theorem Compatible.symm {H : Hardware} {a b : Requirement × ResourceId} (h : Compatible H a b) : Compatible H b a := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨fun e => ?_, fun g rel hb ha => ?_⟩
  · obtain ⟨hc, hs⟩ := h₁ e.symm; exact ⟨hc.symm, hc ▸ hs⟩
  · have := h₂ g rel ha hb
    cases rel with
    | same => exact this.symm
    | distinct => exact fun e => this e.symm

/-! ## Assignments and validity -/

abbrev Assignment := List (Requirement × ResourceId)

/-- Every entry is supported and every two entries are compatible.  No
    coverage requirement: partial designs may leave requirements unassigned. -/
def PartialValid (H : Hardware) (A : Assignment) : Prop :=
  (∀ e ∈ A, ReqOK H e.1 e.2) ∧ A.Pairwise (Compatible H)

instance (H : Hardware) (A : Assignment) : Decidable (PartialValid H A) :=
  inferInstanceAs (Decidable ((∀ e ∈ A, ReqOK H e.1 e.2) ∧ A.Pairwise (Compatible H)))

/-- A complete assignment *for* `R`: partial-valid and covering exactly `R`. -/
def ValidFor (H : Hardware) (R : Requirements) (A : Assignment) : Prop :=
  PartialValid H A ∧ A.map Prod.fst = R

def HardwareSatisfiable (H : Hardware) (R : Requirements) : Prop :=
  ∃ A, ValidFor H R A

/-- Two direct consequences of validity. -/
theorem valid_assignment_implies_capabilities_satisfied {H : Hardware} {R : Requirements} {A : Assignment}
    (h : ValidFor H R A) : ∀ e ∈ A, Supports H e.2 e.1.cap :=
  fun e he => (h.1.1 e he).1

theorem exclusive_resources_not_double_allocated {H : Hardware} {A : Assignment} (h : PartialValid H A)
    {a b : Requirement × ResourceId} (hab : A.Pairwise (fun x y => x = a → y = b → False) → False)
    (hr : a.2 = b.2) (hex : a.1.cap ∉ H.shareable) : False := by
  -- `hab` says the ordered pair (a, b) occurs in A; then Compatible forbids the shared resource
  apply hab
  refine List.Pairwise.imp ?_ h.2
  intro x y hxy rfl rfl
  exact hex ((hxy.1 hr).2)

/-! ## Solver: exhaustive depth-first search -/

def firstSome {α β : Type} : List α → (α → Option β) → Option β
  | [], _ => none
  | x :: xs, g => match g x with
    | some y => some y
    | none => firstSome xs g

theorem firstSome_none {α β : Type} {l : List α} {g : α → Option β} (h : firstSome l g = none) :
    ∀ x ∈ l, g x = none := by
  induction l with
  | nil => intro x hx; simp at hx
  | cons a l ih =>
    intro x hx
    simp only [firstSome] at h
    cases hg : g a with
    | some y => rw [hg] at h; exact nomatch h
    | none =>
      rw [hg] at h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hg
      · exact ih h x hx'

theorem firstSome_some {α β : Type} {l : List α} {g : α → Option β} {y : β} (h : firstSome l g = some y) :
    ∃ x ∈ l, g x = some y := by
  induction l with
  | nil => simp [firstSome] at h
  | cons a l ih =>
    simp only [firstSome] at h
    cases hg : g a with
    | some y' => rw [hg] at h; cases h; exact ⟨a, List.mem_cons_self, hg⟩
    | none =>
      rw [hg] at h
      obtain ⟨x, hx, hgx⟩ := ih h
      exact ⟨x, List.mem_cons_of_mem _ hx, hgx⟩

/-- Candidate resources for a requirement: those that satisfy the unary check. -/
def candidates (H : Hardware) (req : Requirement) : List ResourceId :=
  (H.resources.map Resource.id).filter fun r => decide (ReqOK H req r)

theorem mem_candidates {H : Hardware} {req : Requirement} {r : ResourceId} :
    r ∈ candidates H req ↔ (r ∈ H.resources.map Resource.id ∧ ReqOK H req r) := by
  simp [candidates]

theorem supports_mem_resources {H : Hardware} {r : ResourceId} {c : Capability} (h : Supports H r c) :
    r ∈ H.resources.map Resource.id := by
  obtain ⟨res, hf, _⟩ := h
  have hm := List.mem_of_find?_eq_some hf
  have hid : res.id = r := by simpa using List.find?_some hf
  exact hid ▸ List.mem_map_of_mem hm

/-- DFS: place each remaining requirement on a candidate compatible with
    everything placed so far. -/
def solveAux (H : Hardware) : List Requirement → Assignment → Option Assignment
  | [], acc => some acc
  | req :: rest, acc =>
    firstSome (candidates H req) fun r =>
      if acc.all (fun e => decide (Compatible H e (req, r))) then
        solveAux H rest (acc ++ [(req, r)])
      else none

def solve (H : Hardware) (R : Requirements) : Option Assignment := solveAux H R []

/-- **Soundness.** -/
theorem solveAux_sound {H : Hardware} : ∀ (rest : List Requirement) (acc A : Assignment),
    PartialValid H acc → solveAux H rest acc = some A → ValidFor H (acc.map Prod.fst ++ rest) A
  | [], acc, A, hacc, h => by
    simp only [solveAux] at h; cases h; exact ⟨hacc, by simp⟩
  | req :: rest, acc, A, hacc, h => by
    simp only [solveAux] at h
    obtain ⟨r, hr, hg⟩ := firstSome_some h
    split at hg
    · rename_i hall
      have hacc' : PartialValid H (acc ++ [(req, r)]) := by
        refine ⟨?_, ?_⟩
        · intro e he
          rcases List.mem_append.mp he with he | he
          · exact hacc.1 e he
          · simp at he; subst he; exact (mem_candidates.mp hr).2
        · rw [List.pairwise_append]
          refine ⟨hacc.2, List.pairwise_singleton _ _, ?_⟩
          intro a ha b hb
          simp at hb; subst hb
          exact of_decide_eq_true ((List.all_eq_true.mp hall) a ha)
      have := solveAux_sound rest (acc ++ [(req, r)]) A hacc' hg
      simpa using this
    · exact nomatch hg

theorem solve_sound {H : Hardware} {R : Requirements} {A : Assignment} (h : solve H R = some A) :
    ValidFor H R A := by
  have := solveAux_sound (H := H) R [] A ⟨fun _ h => by simp at h, List.Pairwise.nil⟩ h
  simpa using this

/-- **Completeness.**  If some valid assignment for the whole list extends
    the current prefix, the search does not fail. -/
theorem solveAux_complete {H : Hardware} : ∀ (rest : List Requirement) (acc : Assignment) (B : Assignment),
    ValidFor H (acc.map Prod.fst ++ rest) (acc ++ B) → B.map Prod.fst = rest →
    solveAux H rest acc ≠ none
  | [], acc, B, _, _, h => by simp [solveAux] at h
  | req :: rest, acc, B, hv, hB, h => by
    cases B with
    | nil => simp at hB
    | cons e B' =>
      simp only [List.map_cons, List.cons.injEq] at hB
      obtain ⟨rfl, hB'⟩ := hB
      simp only [solveAux] at h
      have hall := firstSome_none h e.2
      -- e.2 is a candidate …
      have hok : ReqOK H e.1 e.2 := hv.1.1 e (by simp)
      have hc : e.2 ∈ candidates H e.1 :=
        mem_candidates.mpr ⟨supports_mem_resources hok.1, hok⟩
      have := hall hc
      -- … compatible with the prefix …
      have hcompat : acc.all (fun x => decide (Compatible H x (e.1, e.2))) = true := by
        rw [List.all_eq_true]
        intro x hx
        have hp := hv.1.2
        rw [List.pairwise_append] at hp
        exact decide_eq_true (hp.2.2 x hx e (by simp))
      rw [if_pos hcompat] at this
      -- … and the recursive call cannot fail either.
      refine solveAux_complete rest (acc ++ [(e.1, e.2)]) B' ?_ hB' this
      refine ⟨by simpa using hv.1, ?_⟩
      have := hv.2
      simpa using this

theorem solve_complete {H : Hardware} {R : Requirements} (h : HardwareSatisfiable H R) :
    ∃ A, solve H R = some A := by
  obtain ⟨B, hB⟩ := h
  have hne : solveAux H R [] ≠ none :=
    solveAux_complete (H := H) R [] B (by simpa using hB) hB.2
  cases hs : solve H R with
  | none => exact absurd hs hne
  | some A => exact ⟨A, rfl⟩

/-- Satisfiability of a finite instance is decided by the solver. -/
theorem satisfiable_iff_solve {H : Hardware} {R : Requirements} :
    HardwareSatisfiable H R ↔ (solve H R).isSome := by
  constructor
  · intro h; obtain ⟨A, hA⟩ := solve_complete h; simp [hA]
  · intro h
    cases hs : solve H R with
    | none => rw [hs] at h; simp at h
    | some A => exact ⟨A, solve_sound hs⟩

instance (H : Hardware) (R : Requirements) : Decidable (HardwareSatisfiable H R) :=
  decidable_of_iff _ satisfiable_iff_solve.symm

/-! ## Partial vs complete -/

theorem partial_assignment_accepted {H : Hardware} {A : Assignment} (h : PartialValid H A)
    {A' : Assignment} (hpre : A' <+: A) : PartialValid H A' :=
  ⟨fun e he => h.1 e (hpre.subset he), h.2.sublist hpre.sublist⟩

theorem complete_assignment_covers_requirements {H : Hardware} {R : Requirements} {A : Assignment}
    (h : ValidFor H R A) : ∀ req ∈ R, ∃ r, (req, r) ∈ A := by
  intro req hreq
  rw [← h.2] at hreq
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hreq
  exact ⟨e.2, he⟩

/-! ## Hardware refinement -/

/-- `H₁.Extends H₂`: every resource of `H₁` is in `H₂` with at least its
    capabilities and the same units; sharing policy only grows. -/
def Hardware.Extends (H₁ H₂ : Hardware) : Prop :=
  (∀ res₁ ∈ H₁.resources, ∃ res₂ ∈ H₂.resources, res₂.id = res₁.id ∧ res₁.caps ⊆ res₂.caps ∧ res₁.units = res₂.units ∧
      H₂.find res₁.id = some res₂) ∧
  H₁.shareable ⊆ H₂.shareable

theorem Hardware.Extends.supports {H₁ H₂ : Hardware} (h : H₁.Extends H₂) {r : ResourceId} {c : Capability}
    (hs : Supports H₁ r c) : Supports H₂ r c := by
  obtain ⟨res, hf, hc⟩ := hs
  have hm := List.mem_of_find?_eq_some hf
  have hid : res.id = r := by simpa using List.find?_some hf
  obtain ⟨res₂, _, _, hcaps, _, hf₂⟩ := h.1 res hm
  exact ⟨res₂, hid ▸ hf₂, hcaps hc⟩

theorem Hardware.Extends.unitOf {H₁ H₂ : Hardware} (h : H₁.Extends H₂) {r : ResourceId} {c : Capability}
    {res : Resource} (hf : H₁.find r = some res) : H₂.unitOf r c = H₁.unitOf r c := by
  have hm := List.mem_of_find?_eq_some hf
  have hid : res.id = r := by simpa using List.find?_some hf
  obtain ⟨res₂, _, _, _, hu, hf₂⟩ := h.1 res hm
  simp [Hardware.unitOf, hid ▸ hf₂, hf, Resource.unitOf, hu]

/-- **`hardware_extension_preserves_satisfiability`**: a valid assignment on
    a smaller board is valid on any extension. -/
theorem hardware_extension_preserves_validity {H₁ H₂ : Hardware} (h : H₁.Extends H₂)
    {A : Assignment} (hv : PartialValid H₁ A) : PartialValid H₂ A := by
  refine ⟨fun e he => ⟨h.supports (hv.1 e he).1, (hv.1 e he).2⟩, ?_⟩
  refine List.Pairwise.imp_of_mem ?_ hv.2
  intro a b ha hb hab
  have ua : ∃ res, H₁.find a.2 = some res := by
    obtain ⟨res, hf, _⟩ := (hv.1 a ha).1; exact ⟨res, hf⟩
  have ub : ∃ res, H₁.find b.2 = some res := by
    obtain ⟨res, hf, _⟩ := (hv.1 b hb).1; exact ⟨res, hf⟩
  obtain ⟨ra, hra⟩ := ua
  obtain ⟨rb, hrb⟩ := ub
  refine ⟨fun e => ⟨(hab.1 e).1, h.2 (hab.1 e).2⟩, fun g rel hga hgb => ?_⟩
  have := hab.2 g rel hga hgb
  cases rel with
  | same => simpa [h.unitOf hra, h.unitOf hrb] using this
  | distinct => simpa [h.unitOf hra, h.unitOf hrb] using this

theorem hardware_extension_preserves_satisfiability {H₁ H₂ : Hardware} (h : H₁.Extends H₂) {R : Requirements}
    (hs : HardwareSatisfiable H₁ R) : HardwareSatisfiable H₂ R := by
  obtain ⟨A, hA⟩ := hs
  exact ⟨A, hardware_extension_preserves_validity h hA.1, hA.2⟩

/-! ## Explanation: the first dead end of the search -/

/-- Structured failure data for one requirement that cannot be placed given
    a prefix: either nothing on the board supports it, or every candidate
    is blocked by some already-placed requirement. -/
inductive Explanation where
  | noCapableResource (req : Requirement)
  | blocked (req : Requirement) (blockers : List (ResourceId × RequirementId))
  deriving Repr

/-- Greedy placement with the first dead end reported.  This is *a* conflict
    under the greedy prefix, not a minimal unsat core: `diagnose` may report
    a dead end even though backtracking would have succeeded, so its result
    is only meaningful when `solve` returned `none`. -/
def diagnoseAux (H : Hardware) : List Requirement → Assignment → Option Explanation
  | [], _ => none
  | req :: rest, acc =>
    match candidates H req with
    | [] => some (.noCapableResource req)
    | cs =>
      match firstSome cs (fun r => if acc.all (fun e => decide (Compatible H e (req, r))) then some r else none) with
      | some r => diagnoseAux H rest (acc ++ [(req, r)])
      | none =>
        some (.blocked req (cs.filterMap fun r =>
          (acc.find? fun e => ¬ decide (Compatible H e (req, r))).map fun e => (r, e.1.id)))

def diagnose (H : Hardware) (R : Requirements) : Option Explanation := diagnoseAux H R []

end BDL.Hardware
