import BDL.Core.Clock
import BDL.Core.Output

/-!
# Rename — identity renaming (Phase 8, behaviour systems)

A reusable behaviour is a *template* over local identities.  Instantiating
it renames every nominal identity it mentions — declarations, semantic
concepts, clock domains, physical sinks — through a `Ren`.  Nothing in the
kernel changes: a renamed design is an ordinary design, and every kernel
judgment is preserved by renaming under the obvious agreement conditions
between the environments before and after.

Renaming is **meta-level** (elaboration machinery, MINIMALITY: surface /
elaboration).  No kernel construct is added here.
-/

namespace BDL
open BDL.Output (OutputId)
open BDL.Clock (ClockEnv clockedB Clocked)

/-- A renaming of the four sorts of nominal identity. -/
structure Ren where
  d : DeclId → DeclId
  s : SemanticId → SemanticId
  c : ClockId → ClockId
  o : OutputId → OutputId

def Ren.id : Ren := ⟨fun d => d, fun s => s, fun c => c, fun o => o⟩

/-! ## Types and primitives -/

def Ty.rename (σ : SemanticId → SemanticId) : Ty → Ty
  | .bool => .bool
  | .nat => .nat
  | .arr a b => .arr (a.rename σ) (b.rename σ)
  | .sem s => .sem (σ s)
  | .q d => .q d
  | .opt τ => .opt (τ.rename σ)

theorem Ty.rename_data (σ : SemanticId → SemanticId) : ∀ τ : Ty, τ.Data → (τ.rename σ).Data
  | .bool, h | .nat, h | .q _, h | .sem _, h => h
  | .opt τ, h => Ty.rename_data σ τ h
  | .arr _ _, h => h.elim

theorem Ty.rename_data_iff (σ : SemanticId → SemanticId) : ∀ τ : Ty, (τ.rename σ).Data ↔ τ.Data
  | .bool | .nat | .q _ | .sem _ => Iff.rfl
  | .opt τ => Ty.rename_data_iff σ τ
  | .arr _ _ => Iff.rfl

theorem Ty.rename_semFree (σ : SemanticId → SemanticId) : ∀ τ : Ty, (τ.rename σ).SemFree ↔ τ.SemFree
  | .bool | .nat | .q _ => Iff.rfl
  | .sem _ => Iff.rfl
  | .opt τ => Ty.rename_semFree σ τ
  | .arr a b => by
    simp only [Ty.rename, Ty.SemFree]
    exact and_congr (Ty.rename_semFree σ a) (Ty.rename_semFree σ b)

/-- A sem-free type is fixed by every renaming. -/
theorem Ty.rename_of_semFree (σ : SemanticId → SemanticId) : ∀ τ : Ty, τ.SemFree → τ.rename σ = τ
  | .bool, _ | .nat, _ | .q _, _ => rfl
  | .sem _, h => h.elim
  | .opt τ, h => by simp [Ty.rename, Ty.rename_of_semFree σ τ h]
  | .arr a b, h => by simp [Ty.rename, Ty.rename_of_semFree σ a h.1, Ty.rename_of_semFree σ b h.2]

theorem Ty.rename_grant (σ : SemanticId → SemanticId) : ∀ τ : Ty, (τ.rename σ).grant = τ.grant.map σ
  | .bool | .nat | .q _ | .opt _ => rfl
  | .sem _ => rfl
  | .arr _ b => Ty.rename_grant σ b

theorem Ty.rename_comp (σ₁ σ₂ : SemanticId → SemanticId) : ∀ τ : Ty, (τ.rename σ₁).rename σ₂ = τ.rename (σ₂ ∘ σ₁)
  | .bool | .nat | .q _ | .sem _ => rfl
  | .opt τ => by simp [Ty.rename, Ty.rename_comp σ₁ σ₂ τ]
  | .arr a b => by simp [Ty.rename, Ty.rename_comp σ₁ σ₂ a, Ty.rename_comp σ₁ σ₂ b]

theorem Ty.rename_id : ∀ τ : Ty, τ.rename (fun s => s) = τ
  | .bool | .nat | .q _ | .sem _ => rfl
  | .opt τ => by simp [Ty.rename, Ty.rename_id τ]
  | .arr a b => by simp [Ty.rename, Ty.rename_id a, Ty.rename_id b]

def Prim.rename (σ : SemanticId → SemanticId) : Prim → Prim
  | .lit d n => .lit d n
  | .add d => .add d
  | .sub d => .sub d
  | .mul d₁ d₂ => .mul d₁ d₂
  | .div d₁ d₂ => .div d₁ d₂
  | .lt d => .lt d
  | .eq d => .eq d
  | .not => .not
  | .and => .and
  | .or => .or
  | .ite τ => .ite (τ.rename σ)
  | .none τ => .none (τ.rename σ)
  | .some τ => .some (τ.rename σ)
  | .isSome τ => .isSome (τ.rename σ)
  | .getD τ => .getD (τ.rename σ)

/-- Dimension algebra is untouched by renaming: the type of a renamed
    primitive is the renamed type. -/
theorem Prim.rename_ty (σ : SemanticId → SemanticId) : ∀ p : Prim, (p.rename σ).ty = p.ty.rename σ
  | .lit _ _ | .add _ | .sub _ | .mul _ _ | .div _ _ | .lt _ | .eq _ | .not | .and | .or => rfl
  | .ite _ | .none _ | .some _ | .isSome _ | .getD _ => rfl

/-! ## Terms -/

def Expr.rename (r : Ren) : Expr → Expr
  | .var i => .var i
  | .boolLit b => .boolLit b
  | .natLit n => .natLit n
  | .lam dom body => .lam (dom.rename r.s) (body.rename r)
  | .app f a => .app (f.rename r) (a.rename r)
  | .declRef d => .declRef (r.d d)
  | .rep e => .rep (e.rename r)
  | .mk s e => .mk (r.s s) (e.rename r)
  | .prim p => .prim (p.rename r.s)
  | .delay i e => .delay (i.rename r) (e.rename r)
  | .sync c i e => .sync (r.c c) (i.rename r) (e.rename r)

theorem Expr.rename_refs (r : Ren) : ∀ e : Expr, (e.rename r).refs = e.refs.map r.d
  | .var _ | .boolLit _ | .natLit _ | .prim _ => rfl
  | .declRef _ => rfl
  | .lam _ b => Expr.rename_refs r b
  | .app f a => by simp [Expr.rename, Expr.refs, Expr.rename_refs r f, Expr.rename_refs r a]
  | .rep e => Expr.rename_refs r e
  | .mk _ e => Expr.rename_refs r e
  | .delay i e => by simp [Expr.rename, Expr.refs, Expr.rename_refs r i, Expr.rename_refs r e]
  | .sync _ i e => by simp [Expr.rename, Expr.refs, Expr.rename_refs r i, Expr.rename_refs r e]

theorem Expr.rename_instRefs (r : Ren) : ∀ e : Expr, (e.rename r).instRefs = e.instRefs.map r.d
  | .var _ | .boolLit _ | .natLit _ | .prim _ => rfl
  | .declRef _ => rfl
  | .lam _ b => Expr.rename_instRefs r b
  | .app f a => by simp [Expr.rename, Expr.instRefs, Expr.rename_instRefs r f, Expr.rename_instRefs r a]
  | .rep e => Expr.rename_instRefs r e
  | .mk _ e => Expr.rename_instRefs r e
  | .delay i _ => Expr.rename_instRefs r i
  | .sync _ i _ => Expr.rename_instRefs r i

theorem Expr.rename_delayFree (r : Ren) : ∀ e : Expr, (e.rename r).DelayFree ↔ e.DelayFree
  | .var _ | .boolLit _ | .natLit _ | .prim _ | .declRef _ => Iff.rfl
  | .lam _ b => Expr.rename_delayFree r b
  | .app f a => by
    simp only [Expr.rename, Expr.DelayFree]
    exact and_congr (Expr.rename_delayFree r f) (Expr.rename_delayFree r a)
  | .rep e => Expr.rename_delayFree r e
  | .mk _ e => Expr.rename_delayFree r e
  | .delay _ _ => Iff.rfl
  | .sync _ _ _ => Iff.rfl

theorem Expr.rename_refFree {r : Ren} {e : Expr} (h : e.RefFree) : (e.rename r).RefFree := by
  unfold Expr.RefFree at *
  rw [Expr.rename_refs, h]; rfl

/-! ## Declarations and environments -/

def DeclInterface.rename (σ : SemanticId → SemanticId) (S : DeclInterface) : DeclInterface :=
  { expectedType := S.expectedType.rename σ, commitments := S.commitments }

def DesignDecl.rename (r : Ren) (h : DesignDecl) : DesignDecl :=
  ⟨r.d h.id, h.interface.rename r.s, h.realization.map (Expr.rename r)⟩

/-- `Δ'` is the renaming of `Δ` by `r` on the image: every declaration of
    `Δ` reappears, renamed, under its renamed identity. -/
def DeclEnv.RenamedBy (r : Ren) (Δ Δ' : DeclEnv) : Prop :=
  ∀ d h, Δ d = some h → Δ' (r.d d) = some (h.rename r)

theorem DeclEnv.RenamedBy.tyView {r : Ren} {Δ Δ' : DeclEnv} (hr : Δ.RenamedBy r Δ')
    {d : DeclId} {τ : Ty} (h : Δ.tyView d = some τ) : Δ'.tyView (r.d d) = some (τ.rename r.s) := by
  simp only [DeclEnv.tyView, Option.map_eq_some_iff] at h ⊢
  obtain ⟨dh, hdh, rfl⟩ := h
  exact ⟨dh.rename r, hr d dh hdh, rfl⟩

theorem DeclEnv.RenamedBy.realizationOf {r : Ren} {Δ Δ' : DeclEnv} (hr : Δ.RenamedBy r Δ')
    {d : DeclId} {e : Expr} (h : Δ.realizationOf d = some e) : Δ'.realizationOf (r.d d) = some (e.rename r) := by
  simp only [DeclEnv.realizationOf, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨dh, hdh, hre⟩ := h
  exact ⟨dh.rename r, hr d dh hdh, by simp [DesignDecl.rename, hre]⟩

/-- `Θ'` agrees with `Θ` on the renamed concepts. -/
def ConceptEnv.RenamedBy (σ : SemanticId → SemanticId) (Θ Θ' : ConceptEnv) : Prop :=
  ∀ s R, Θ s = some R → Θ' (σ s) = some (R.rename σ)

/-- `Κ'` agrees with `Κ` on the renamed declarations satisfying `P`
    (including agnosticity: `none` maps to `none`).  `P` is normally
    "declared in the template"; a term only refers to declared identities. -/
def ClockEnv.RenamedBy (P : DeclId → Prop) (r : Ren) (Κ Κ' : ClockEnv) : Prop :=
  ∀ d, P d → Κ' (r.d d) = (Κ d).map r.c

/-! ## Theorem B — freshening (renaming) preserves typing -/

/-- Renaming preserves typing, given agreement of the three environments on
    the image of the renaming.  No injectivity is needed. -/
theorem HasType.rename {r : Ren} {Θ Θ' : ConceptEnv} {Δ Δ' : DeclEnv} {G G' : Grant}
    (hΘ : Θ.RenamedBy r.s Θ') (hΔ : Δ.RenamedBy r Δ') (hG : ∀ s, G s → G' (r.s s))
    {Γ : Ctx} {e : Expr} {τ : Ty} (h : HasType Θ Δ G Γ e τ) :
    HasType Θ' Δ' G' (Γ.map (Ty.rename r.s)) (e.rename r) (τ.rename r.s) := by
  induction h with
  | var h => exact .var (by simp [h])
  | boolLit => exact .boolLit
  | natLit => exact .natLit
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha
  | declRef h => exact .declRef (hΔ.tyView h)
  | rep hΘs _ ih => exact .rep (hΘ _ _ hΘs) ih
  | mk hg hΘs _ ih => exact .mk (hG _ hg) (hΘ _ _ hΘs) ih
  | prim => rw [← Prim.rename_ty]; exact .prim
  | delay hd _ _ ihi ihe => exact .delay (Ty.rename_data _ _ hd) ihi ihe
  | sync hd _ _ ihi ihe => exact .sync (Ty.rename_data _ _ hd) ihi ihe

/-- The grant of a renamed signature is the renamed grant. -/
theorem Grant.of_rename (σ : SemanticId → SemanticId) (τ : Ty) (s : SemanticId) :
    Grant.of τ s → Grant.of (τ.rename σ) (σ s) := by
  intro h
  unfold Grant.of at *
  rw [Ty.rename_grant]
  exact List.mem_map_of_mem h

/-- Evidence that is invariant under renaming: a commitment discharged for
    `e` in `Δ` is discharged for the renamed `e` in the renamed `Δ`.  This is
    the condition under which a component's validity does not depend on the
    identities of one particular instance (§20). -/
def Evidence.Equivariant (ev : Evidence) : Prop :=
  ∀ (r : Ren) (Δ Δ' : DeclEnv), Δ.RenamedBy r Δ' → ∀ e p, ev Δ e p → ev Δ' (e.rename r) p

theorem Evidence.Equivariant.of_const (f : Expr → PropertyId → Prop)
    (hf : ∀ r e p, f e p → f (e.rename r) p) : Evidence.Equivariant (fun _ e p => f e p) :=
  fun r _ _ _ e p h => hf r e p h

/-- Satisfaction is preserved by renaming. -/
theorem Satisfies.rename {ev : Evidence} (eq : ev.Equivariant) {r : Ren} {Θ Θ' : ConceptEnv}
    {Δ Δ' : DeclEnv} (hΘ : Θ.RenamedBy r.s Θ') (hΔ : Δ.RenamedBy r Δ')
    {Γ : Ctx} {e : Expr} {S : DeclInterface} (hs : Satisfies ev Θ Δ Γ e S) :
    Satisfies ev Θ' Δ' (Γ.map (Ty.rename r.s)) (e.rename r) (S.rename r.s) :=
  ⟨hs.1.rename hΘ hΔ (Grant.of_rename r.s S.expectedType),
   fun p hp => eq r Δ Δ' hΔ e p (hs.2 p hp)⟩

theorem WellFormedDecl.rename {ev : Evidence} (eq : ev.Equivariant) {r : Ren} {Θ Θ' : ConceptEnv}
    {Δ Δ' : DeclEnv} (hΘ : Θ.RenamedBy r.s Θ') (hΔ : Δ.RenamedBy r Δ')
    {h : DesignDecl} (wf : WellFormedDecl ev Θ Δ [] h) : WellFormedDecl ev Θ' Δ' [] (h.rename r) := by
  intro e' he'
  simp only [DesignDecl.rename, Option.map_eq_some_iff] at he'
  obtain ⟨e, he, rfl⟩ := he'
  simpa [DesignDecl.rename] using (wf e he).rename eq hΘ hΔ

/-! ## Theorem G (local half) — renaming preserves the domain judgment -/

open BDL.Clock in
theorem Clock.clockedB_rename {P : DeclId → Prop} {r : Ren} {Κ Κ' : ClockEnv} (hK : ClockEnv.RenamedBy P r Κ Κ') :
    ∀ (c : Option ClockId) (e : Expr), (∀ d ∈ e.refs, P d) →
      clockedB Κ c e = true → clockedB Κ' (c.map r.c) (e.rename r) = true
  | c, .lam _ b, hP, h => Clock.clockedB_rename hK c b hP h
  | c, .app f a, hP, h => by
    simp only [clockedB, Expr.rename, Bool.and_eq_true] at h ⊢
    simp only [Expr.refs, List.mem_append] at hP
    exact ⟨Clock.clockedB_rename hK c f (fun d hd => hP d (Or.inl hd)) h.1,
           Clock.clockedB_rename hK c a (fun d hd => hP d (Or.inr hd)) h.2⟩
  | c, .declRef d, hP, h => by
    simp only [clockedB, Expr.rename, decide_eq_true_eq] at h ⊢
    rw [hK d (hP d (by simp [Expr.refs]))]
    rcases h with h | h
    · left; simp [h]
    · right; simp [h]
  | c, .rep e, hP, h => Clock.clockedB_rename hK c e hP h
  | c, .mk _ e, hP, h => Clock.clockedB_rename hK c e hP h
  | some c, .delay i e, hP, h => by
    simp only [clockedB, Expr.rename, Option.map_some, Bool.and_eq_true] at h ⊢
    simp only [Expr.refs, List.mem_append] at hP
    exact ⟨Clock.clockedB_rename hK (some c) i (fun d hd => hP d (Or.inl hd)) h.1,
           Clock.clockedB_rename hK (some c) e (fun d hd => hP d (Or.inr hd)) h.2⟩
  | none, .delay _ _, _, h => by simp [clockedB] at h
  | some c, .sync c' i e, hP, h => by
    simp only [clockedB, Expr.rename, Option.map_some, Bool.and_eq_true] at h ⊢
    simp only [Expr.refs, List.mem_append] at hP
    exact ⟨Clock.clockedB_rename hK (some c) i (fun d hd => hP d (Or.inl hd)) h.1,
           Clock.clockedB_rename hK (some c') e (fun d hd => hP d (Or.inr hd)) h.2⟩
  | none, .sync _ _ _, _, h => by simp [clockedB] at h
  | _, .var _, _, _ | _, .boolLit _, _, _ | _, .natLit _, _, _ | _, .prim _, _, _ => by simp [clockedB, Expr.rename]

theorem Clock.Clocked.rename {P : DeclId → Prop} {r : Ren} {Κ Κ' : ClockEnv} (hK : ClockEnv.RenamedBy P r Κ Κ')
    {c : Option ClockId} {e : Expr} (hP : ∀ d ∈ e.refs, P d) (h : Clock.Clocked Κ c e) :
    Clock.Clocked Κ' (c.map r.c) (e.rename r) :=
  Clock.clockedB_rename hK c e hP h

open BDL.Clock in
/-- A closed, delay-free, reference-free term is clocked in every domain
    (used for constant parameters and transport initial values). -/
theorem Clock.clockedB_of_closed : ∀ (e : Expr), e.RefFree → e.DelayFree → ∀ c, clockedB Κ c e = true
  | .var _, _, _, _ | .boolLit _, _, _, _ | .natLit _, _, _, _ | .prim _, _, _, _ => by simp [clockedB]
  | .declRef _, hf, _, _ => by simp [Expr.RefFree, Expr.refs] at hf
  | .lam _ b, hf, hd, c => Clock.clockedB_of_closed b hf hd c
  | .app f a, hf, hd, c => by
    simp only [clockedB, Bool.and_eq_true]
    exact ⟨Clock.clockedB_of_closed f hf.app_left hd.1 c, Clock.clockedB_of_closed a hf.app_right hd.2 c⟩
  | .rep e, hf, hd, c => Clock.clockedB_of_closed e hf hd c
  | .mk _ e, hf, hd, c => Clock.clockedB_of_closed e hf hd c
  | .delay _ _, _, hd, _ => hd.elim
  | .sync _ _ _, _, hd, _ => hd.elim

end BDL
