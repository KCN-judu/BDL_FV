import BDL.Core.Clock

/-!
# Poly — rank-1 schemes as type patterns (Phase 9b)

The kernel type language is monomorphic.  A *generic* definition is a
family of kernel terms indexed by types (and dimensions): `id τ`, `min τ`,
`map τ σ`.  What the elaborator sees is a **scheme**: a type pattern with
type variables and dimension variables.  Instantiating a scheme is
substitution; finding the instance at a use site is first-order *matching*
of the pattern against the (already inferred, monomorphic) argument types.

Matching is decidable, and when it succeeds it returns the unique
substitution on the pattern's variables (`matchTy_sound`,
`matchTy_complete`).  There is no unification of two open types, no
generalization inside expressions, and no principal-type search: a use site
always has closed argument types, because every declaration's type is
frozen and closed (Phase 1).  That is the entire inference problem for
rank-1 definitional polymorphism in BDL.
-/

namespace BDL.Poly
open BDL

/-- Dimension patterns: a constant, or a dimension variable. -/
inductive PDim where
  | const (d : Dim)
  | dvar (n : Nat)
  deriving DecidableEq, Repr

/-- Type patterns: the kernel's type formers over type variables. -/
inductive PTy where
  | tvar (n : Nat)
  | bool
  | nat
  | arr (a b : PTy)
  | sem (s : ConceptId)
  | q (d : PDim)
  | opt (τ : PTy)
  | list (τ : PTy)
  | prod (a b : PTy)
  deriving DecidableEq, Repr

/-- A substitution: type variables to closed types, dimension variables to dimensions. -/
structure Subst where
  ty : Nat → Ty
  dim : Nat → Dim

def PDim.inst (σ : Subst) : PDim → Dim
  | .const d => d
  | .dvar n => σ.dim n

def PTy.inst (σ : Subst) : PTy → Ty
  | .tvar n => σ.ty n
  | .bool => .bool
  | .nat => .nat
  | .arr a b => .arr (a.inst σ) (b.inst σ)
  | .sem s => .sem s
  | .q d => .q (d.inst σ)
  | .opt τ => .opt (τ.inst σ)
  | .list τ => .list (τ.inst σ)
  | .prod a b => .prod (a.inst σ) (b.inst σ)

/-- Embedding closed types as patterns. -/
def PTy.ofTy : Ty → PTy
  | .bool => .bool
  | .nat => .nat
  | .arr a b => .arr (ofTy a) (ofTy b)
  | .sem s => .sem s
  | .q d => .q (.const d)
  | .opt τ => .opt (ofTy τ)
  | .list τ => .list (ofTy τ)
  | .prod a b => .prod (ofTy a) (ofTy b)

theorem PTy.inst_ofTy (σ : Subst) : ∀ τ : Ty, (PTy.ofTy τ).inst σ = τ
  | .bool | .nat | .sem _ | .q _ => rfl
  | .arr a b => by simp [PTy.ofTy, PTy.inst, PTy.inst_ofTy σ a, PTy.inst_ofTy σ b]
  | .opt τ => by simp [PTy.ofTy, PTy.inst, PTy.inst_ofTy σ τ]
  | .list τ => by simp [PTy.ofTy, PTy.inst, PTy.inst_ofTy σ τ]
  | .prod a b => by simp [PTy.ofTy, PTy.inst, PTy.inst_ofTy σ a, PTy.inst_ofTy σ b]

/-! ## Matching: the use-site inference problem -/

theorem Nat.beq_self' (n : Nat) : (n == n) = true := decide_eq_true rfl

theorem lookup_cons_self' {β : Type} (n : Nat) (b : β) (l : List (Nat × β)) : ((n, b) :: l).lookup n = some b := by
  show (match n == n with | true => some b | false => List.lookup n l) = some b
  rw [Nat.beq_self']

/-- Partial substitutions accumulated during matching. -/
structure PSubst where
  ty : List (Nat × Ty)
  dim : List (Nat × Dim)
  deriving Repr

def PSubst.empty : PSubst := ⟨[], []⟩

def PSubst.bindTy (ps : PSubst) (n : Nat) (τ : Ty) : Option PSubst :=
  match ps.ty.lookup n with
  | some τ' => if τ' = τ then some ps else none
  | none => some { ps with ty := (n, τ) :: ps.ty }

def PSubst.bindDim (ps : PSubst) (n : Nat) (d : Dim) : Option PSubst :=
  match ps.dim.lookup n with
  | some d' => if d' = d then some ps else none
  | none => some { ps with dim := (n, d) :: ps.dim }

def matchDim (p : PDim) (d : Dim) (ps : PSubst) : Option PSubst :=
  match p with
  | .const d' => if d' = d then some ps else none
  | .dvar n => ps.bindDim n d

/-- First-order matching of a pattern against a closed type. -/
def matchTy : PTy → Ty → PSubst → Option PSubst
  | .tvar n, τ, ps => ps.bindTy n τ
  | .bool, .bool, ps => some ps
  | .nat, .nat, ps => some ps
  | .arr a b, .arr a' b', ps => (matchTy a a' ps).bind (matchTy b b')
  | .sem s, .sem s', ps => if s = s' then some ps else none
  | .q d, .q d', ps => matchDim d d' ps
  | .opt τ, .opt τ', ps => matchTy τ τ' ps
  | .list τ, .list τ', ps => matchTy τ τ' ps
  | .prod a b, .prod a' b', ps => (matchTy a a' ps).bind (matchTy b b')
  | _, _, _ => none

/-- Read a partial substitution as a total one (unbound variables default). -/
def PSubst.toSubst (ps : PSubst) : Subst :=
  ⟨fun n => (ps.ty.lookup n).getD .bool, fun n => (ps.dim.lookup n).getD Dim.zero⟩

/-- `ps'` extends `ps`: every binding of `ps` is a binding of `ps'`. -/
def PSubst.Extends (ps ps' : PSubst) : Prop :=
  (∀ n τ, ps.ty.lookup n = some τ → ps'.ty.lookup n = some τ) ∧
  (∀ n d, ps.dim.lookup n = some d → ps'.dim.lookup n = some d)

theorem PSubst.Extends.refl (ps : PSubst) : ps.Extends ps := ⟨fun _ _ h => h, fun _ _ h => h⟩
theorem PSubst.Extends.trans {a b c : PSubst} (h₁ : a.Extends b) (h₂ : b.Extends c) : a.Extends c :=
  ⟨fun n τ h => h₂.1 n τ (h₁.1 n τ h), fun n d h => h₂.2 n d (h₁.2 n d h)⟩

theorem PSubst.bindTy_extends {ps ps' : PSubst} {n : Nat} {τ : Ty} (h : ps.bindTy n τ = some ps') :
    ps.Extends ps' ∧ ps'.ty.lookup n = some τ := by
  unfold PSubst.bindTy at h
  cases hl : ps.ty.lookup n with
  | some τ' =>
    rw [hl] at h
    by_cases he : τ' = τ
    · subst he; simp only at h; cases h; exact ⟨PSubst.Extends.refl _, hl⟩
    · simp only [if_neg he] at h; exact nomatch h
  | none =>
    rw [hl] at h
    cases h
    refine ⟨⟨fun m τ'' hm => ?_, fun _ _ hm => hm⟩, lookup_cons_self' _ _ _⟩
    simp only [List.lookup]
    by_cases hmn : m = n
    · subst hmn; rw [hl] at hm; exact nomatch hm
    · rw [beq_eq_false_iff_ne.mpr hmn]; exact hm

theorem PSubst.bindDim_extends {ps ps' : PSubst} {n : Nat} {d : Dim} (h : ps.bindDim n d = some ps') :
    ps.Extends ps' ∧ ps'.dim.lookup n = some d := by
  unfold PSubst.bindDim at h
  cases hl : ps.dim.lookup n with
  | some d' =>
    rw [hl] at h
    by_cases he : d' = d
    · subst he; simp only at h; cases h; exact ⟨PSubst.Extends.refl _, hl⟩
    · simp only [if_neg he] at h; exact nomatch h
  | none =>
    rw [hl] at h
    cases h
    refine ⟨⟨fun _ _ hm => hm, fun m d'' hm => ?_⟩, lookup_cons_self' _ _ _⟩
    simp only [List.lookup]
    by_cases hmn : m = n
    · subst hmn; rw [hl] at hm; exact nomatch hm
    · rw [beq_eq_false_iff_ne.mpr hmn]; exact hm

theorem matchDim_extends {p : PDim} {d : Dim} {ps ps' : PSubst} (h : matchDim p d ps = some ps') :
    ps.Extends ps' := by
  cases p with
  | const d' =>
    simp only [matchDim] at h
    split at h
    · cases h; exact PSubst.Extends.refl _
    · exact nomatch h
  | dvar n => exact (PSubst.bindDim_extends h).1

theorem matchTy_extends : ∀ {p : PTy} {τ : Ty} {ps ps' : PSubst}, matchTy p τ ps = some ps' → ps.Extends ps'
  | .tvar _, _, _, _, h => (PSubst.bindTy_extends h).1
  | .bool, .bool, _, _, h => by cases h; exact PSubst.Extends.refl _
  | .nat, .nat, _, _, h => by cases h; exact PSubst.Extends.refl _
  | .sem _, .sem _, _, _, h => by
    simp only [matchTy] at h; split at h
    · cases h; exact PSubst.Extends.refl _
    · exact nomatch h
  | .q _, .q _, _, _, h => matchDim_extends h
  | .opt τ, .opt _, _, _, h => matchTy_extends (p := τ) h
  | .list τ, .list _, _, _, h => matchTy_extends (p := τ) h
  | .arr a b, .arr _ _, _, _, h => by
    simp only [matchTy, Option.bind_eq_some_iff] at h
    obtain ⟨ps₁, h₁, h₂⟩ := h
    exact (matchTy_extends (p := a) h₁).trans (matchTy_extends (p := b) h₂)
  | .prod a b, .prod _ _, _, _, h => by
    simp only [matchTy, Option.bind_eq_some_iff] at h
    obtain ⟨ps₁, h₁, h₂⟩ := h
    exact (matchTy_extends (p := a) h₁).trans (matchTy_extends (p := b) h₂)
  | .bool, .nat, _, _, h | .bool, .arr _ _, _, _, h | .bool, .sem _, _, _, h | .bool, .q _, _, _, h
  | .bool, .opt _, _, _, h | .bool, .list _, _, _, h | .bool, .prod _ _, _, _, h => nomatch h
  | .nat, .bool, _, _, h | .nat, .arr _ _, _, _, h | .nat, .sem _, _, _, h | .nat, .q _, _, _, h
  | .nat, .opt _, _, _, h | .nat, .list _, _, _, h | .nat, .prod _ _, _, _, h => nomatch h
  | .arr _ _, .bool, _, _, h | .arr _ _, .nat, _, _, h | .arr _ _, .sem _, _, _, h | .arr _ _, .q _, _, _, h
  | .arr _ _, .opt _, _, _, h | .arr _ _, .list _, _, _, h | .arr _ _, .prod _ _, _, _, h => nomatch h
  | .sem _, .bool, _, _, h | .sem _, .nat, _, _, h | .sem _, .arr _ _, _, _, h | .sem _, .q _, _, _, h
  | .sem _, .opt _, _, _, h | .sem _, .list _, _, _, h | .sem _, .prod _ _, _, _, h => nomatch h
  | .q _, .bool, _, _, h | .q _, .nat, _, _, h | .q _, .arr _ _, _, _, h | .q _, .sem _, _, _, h
  | .q _, .opt _, _, _, h | .q _, .list _, _, _, h | .q _, .prod _ _, _, _, h => nomatch h
  | .opt _, .bool, _, _, h | .opt _, .nat, _, _, h | .opt _, .arr _ _, _, _, h | .opt _, .sem _, _, _, h
  | .opt _, .q _, _, _, h | .opt _, .list _, _, _, h | .opt _, .prod _ _, _, _, h => nomatch h
  | .list _, .bool, _, _, h | .list _, .nat, _, _, h | .list _, .arr _ _, _, _, h | .list _, .sem _, _, _, h
  | .list _, .q _, _, _, h | .list _, .opt _, _, _, h | .list _, .prod _ _, _, _, h => nomatch h
  | .prod _ _, .bool, _, _, h | .prod _ _, .nat, _, _, h | .prod _ _, .arr _ _, _, _, h | .prod _ _, .sem _, _, _, h
  | .prod _ _, .q _, _, _, h | .prod _ _, .opt _, _, _, h | .prod _ _, .list _, _, _, h => nomatch h

/-- The variables a pattern mentions are bound after a successful match. -/
def PTy.tvars : PTy → List Nat
  | .tvar n => [n]
  | .arr a b => a.tvars ++ b.tvars
  | .opt τ => τ.tvars
  | .list τ => τ.tvars
  | .prod a b => a.tvars ++ b.tvars
  | _ => []

def PDim.dvars : PDim → List Nat
  | .const _ => []
  | .dvar n => [n]

def PTy.dvars : PTy → List Nat
  | .arr a b => a.dvars ++ b.dvars
  | .q d => d.dvars
  | .opt τ => τ.dvars
  | .list τ => τ.dvars
  | .prod a b => a.dvars ++ b.dvars
  | _ => []

/-- Instantiation depends only on the variables the pattern mentions. -/
theorem PTy.inst_congr {σ σ' : Subst} : ∀ {p : PTy},
    (∀ n ∈ p.tvars, σ.ty n = σ'.ty n) → (∀ n ∈ p.dvars, σ.dim n = σ'.dim n) → p.inst σ = p.inst σ'
  | .tvar n, ht, _ => ht n (by simp [PTy.tvars])
  | .bool, _, _ | .nat, _, _ | .sem _, _, _ => rfl
  | .q (.const _), _, _ => rfl
  | .q (.dvar n), _, hd => by simp [PTy.inst, PDim.inst, hd n (by simp [PTy.dvars, PDim.dvars])]
  | .opt τ, ht, hd => by simp [PTy.inst, PTy.inst_congr (p := τ) ht hd]
  | .list τ, ht, hd => by simp [PTy.inst, PTy.inst_congr (p := τ) ht hd]
  | .arr a b, ht, hd => by
    simp only [PTy.tvars, PTy.dvars, List.mem_append] at ht hd
    simp [PTy.inst, PTy.inst_congr (p := a) (fun n hn => ht n (Or.inl hn)) (fun n hn => hd n (Or.inl hn)),
      PTy.inst_congr (p := b) (fun n hn => ht n (Or.inr hn)) (fun n hn => hd n (Or.inr hn))]
  | .prod a b, ht, hd => by
    simp only [PTy.tvars, PTy.dvars, List.mem_append] at ht hd
    simp [PTy.inst, PTy.inst_congr (p := a) (fun n hn => ht n (Or.inl hn)) (fun n hn => hd n (Or.inl hn)),
      PTy.inst_congr (p := b) (fun n hn => ht n (Or.inr hn)) (fun n hn => hd n (Or.inr hn))]

/-- **Soundness of matching.**  A successful match instantiates the pattern
    to the type — under the resulting substitution *and* under any extension
    of it (so later arguments cannot invalidate earlier ones). -/
theorem matchTy_sound : ∀ {p : PTy} {τ : Ty} {ps ps' : PSubst}, matchTy p τ ps = some ps' →
    ∀ ps'', ps'.Extends ps'' → p.inst ps''.toSubst = τ
  | .tvar n, τ, ps, ps', h, ps'', hext => by
    have hb := (PSubst.bindTy_extends h).2
    simp [PTy.inst, PSubst.toSubst, hext.1 n τ hb]
  | .bool, .bool, _, _, h, _, _ => rfl
  | .nat, .nat, _, _, h, _, _ => rfl
  | .sem s, .sem s', _, _, h, _, _ => by
    simp only [matchTy] at h; split at h
    · rename_i he; subst he; rfl
    · exact nomatch h
  | .q (.const d), .q d', _, _, h, _, _ => by
    simp only [matchTy, matchDim] at h; split at h
    · rename_i he; subst he; rfl
    · exact nomatch h
  | .q (.dvar n), .q d', _, _, h, ps'', hext => by
    have hb := (PSubst.bindDim_extends h).2
    simp [PTy.inst, PDim.inst, PSubst.toSubst, hext.2 n d' hb]
  | .opt τ, .opt τ', _, _, h, ps'', hext => by simp [PTy.inst, matchTy_sound (p := τ) h ps'' hext]
  | .list τ, .list τ', _, _, h, ps'', hext => by simp [PTy.inst, matchTy_sound (p := τ) h ps'' hext]
  | .arr a b, .arr a' b', _, _, h, ps'', hext => by
    simp only [matchTy, Option.bind_eq_some_iff] at h
    obtain ⟨ps₁, h₁, h₂⟩ := h
    simp [PTy.inst, matchTy_sound (p := a) h₁ ps'' ((matchTy_extends h₂).trans hext),
      matchTy_sound (p := b) h₂ ps'' hext]
  | .prod a b, .prod a' b', _, _, h, ps'', hext => by
    simp only [matchTy, Option.bind_eq_some_iff] at h
    obtain ⟨ps₁, h₁, h₂⟩ := h
    simp [PTy.inst, matchTy_sound (p := a) h₁ ps'' ((matchTy_extends h₂).trans hext),
      matchTy_sound (p := b) h₂ ps'' hext]
  | .bool, .nat, _, _, h, _, _ | .bool, .arr _ _, _, _, h, _, _ | .bool, .sem _, _, _, h, _, _ | .bool, .q _, _, _, h, _, _
  | .bool, .opt _, _, _, h, _, _ | .bool, .list _, _, _, h, _, _ | .bool, .prod _ _, _, _, h, _, _ => nomatch h
  | .nat, .bool, _, _, h, _, _ | .nat, .arr _ _, _, _, h, _, _ | .nat, .sem _, _, _, h, _, _ | .nat, .q _, _, _, h, _, _
  | .nat, .opt _, _, _, h, _, _ | .nat, .list _, _, _, h, _, _ | .nat, .prod _ _, _, _, h, _, _ => nomatch h
  | .arr _ _, .bool, _, _, h, _, _ | .arr _ _, .nat, _, _, h, _, _ | .arr _ _, .sem _, _, _, h, _, _ | .arr _ _, .q _, _, _, h, _, _
  | .arr _ _, .opt _, _, _, h, _, _ | .arr _ _, .list _, _, _, h, _, _ | .arr _ _, .prod _ _, _, _, h, _, _ => nomatch h
  | .sem _, .bool, _, _, h, _, _ | .sem _, .nat, _, _, h, _, _ | .sem _, .arr _ _, _, _, h, _, _ | .sem _, .q _, _, _, h, _, _
  | .sem _, .opt _, _, _, h, _, _ | .sem _, .list _, _, _, h, _, _ | .sem _, .prod _ _, _, _, h, _, _ => nomatch h
  | .q _, .bool, _, _, h, _, _ | .q _, .nat, _, _, h, _, _ | .q _, .arr _ _, _, _, h, _, _ | .q _, .sem _, _, _, h, _, _
  | .q _, .opt _, _, _, h, _, _ | .q _, .list _, _, _, h, _, _ | .q _, .prod _ _, _, _, h, _, _ => nomatch h
  | .opt _, .bool, _, _, h, _, _ | .opt _, .nat, _, _, h, _, _ | .opt _, .arr _ _, _, _, h, _, _ | .opt _, .sem _, _, _, h, _, _
  | .opt _, .q _, _, _, h, _, _ | .opt _, .list _, _, _, h, _, _ | .opt _, .prod _ _, _, _, h, _, _ => nomatch h
  | .list _, .bool, _, _, h, _, _ | .list _, .nat, _, _, h, _, _ | .list _, .arr _ _, _, _, h, _, _ | .list _, .sem _, _, _, h, _, _
  | .list _, .q _, _, _, h, _, _ | .list _, .opt _, _, _, h, _, _ | .list _, .prod _ _, _, _, h, _, _ => nomatch h
  | .prod _ _, .bool, _, _, h, _, _ | .prod _ _, .nat, _, _, h, _, _ | .prod _ _, .arr _ _, _, _, h, _, _ | .prod _ _, .sem _, _, _, h, _, _
  | .prod _ _, .q _, _, _, h, _, _ | .prod _ _, .opt _, _, _, h, _, _ | .prod _ _, .list _, _, _, h, _, _ => nomatch h

/-- A partial substitution *agrees with* a total one on its bindings. -/
def PSubst.AgreesWith (ps : PSubst) (σ : Subst) : Prop :=
  (∀ n τ, ps.ty.lookup n = some τ → σ.ty n = τ) ∧ (∀ n d, ps.dim.lookup n = some d → σ.dim n = d)

theorem PSubst.bindTy_complete {ps : PSubst} {σ : Subst} (h : ps.AgreesWith σ) (n : Nat) :
    ∃ ps', ps.bindTy n (σ.ty n) = some ps' ∧ ps'.AgreesWith σ := by
  unfold PSubst.bindTy
  cases hl : ps.ty.lookup n with
  | some τ' => exact ⟨ps, by simp only [h.1 n τ' hl, ite_true], h⟩
  | none =>
    refine ⟨_, rfl, ⟨fun m τ hm => ?_, h.2⟩⟩
    simp only [List.lookup] at hm
    by_cases hmn : m = n
    · subst hmn; rw [Nat.beq_self'] at hm; exact Option.some.inj hm
    · rw [beq_eq_false_iff_ne.mpr hmn] at hm; exact h.1 m τ hm

theorem PSubst.bindDim_complete {ps : PSubst} {σ : Subst} (h : ps.AgreesWith σ) (n : Nat) :
    ∃ ps', ps.bindDim n (σ.dim n) = some ps' ∧ ps'.AgreesWith σ := by
  unfold PSubst.bindDim
  cases hl : ps.dim.lookup n with
  | some d' => exact ⟨ps, by simp only [h.2 n d' hl, ite_true], h⟩
  | none =>
    refine ⟨_, rfl, ⟨h.1, fun m d hm => ?_⟩⟩
    simp only [List.lookup] at hm
    by_cases hmn : m = n
    · subst hmn; rw [Nat.beq_self'] at hm; exact Option.some.inj hm
    · rw [beq_eq_false_iff_ne.mpr hmn] at hm; exact h.2 m d hm

/-- **Completeness of matching.**  If the pattern has *some* instance equal
    to the type, matching finds a substitution agreeing with it — so the
    result is unique on the pattern's variables (most general = only). -/
theorem matchTy_complete : ∀ (p : PTy) (σ : Subst) {ps : PSubst}, ps.AgreesWith σ →
    ∃ ps', matchTy p (p.inst σ) ps = some ps' ∧ ps'.AgreesWith σ
  | .tvar n, σ, ps, h => PSubst.bindTy_complete h n
  | .bool, σ, ps, h => ⟨ps, rfl, h⟩
  | .nat, σ, ps, h => ⟨ps, rfl, h⟩
  | .sem s, σ, ps, h => ⟨ps, by simp [PTy.inst, matchTy], h⟩
  | .q (.const d), σ, ps, h => ⟨ps, by simp [PTy.inst, PDim.inst, matchTy, matchDim], h⟩
  | .q (.dvar n), σ, ps, h => PSubst.bindDim_complete h n
  | .opt τ, σ, ps, h => matchTy_complete τ σ h
  | .list τ, σ, ps, h => matchTy_complete τ σ h
  | .arr a b, σ, ps, h => by
    obtain ⟨ps₁, h₁, ha⟩ := matchTy_complete a σ h
    obtain ⟨ps₂, h₂, hb⟩ := matchTy_complete b σ ha
    exact ⟨ps₂, by simp [PTy.inst, matchTy, h₁, h₂], hb⟩
  | .prod a b, σ, ps, h => by
    obtain ⟨ps₁, h₁, ha⟩ := matchTy_complete a σ h
    obtain ⟨ps₂, h₂, hb⟩ := matchTy_complete b σ ha
    exact ⟨ps₂, by simp [PTy.inst, matchTy, h₁, h₂], hb⟩

/-! ## Schemes with the closed capability vocabulary (Phase 9c) -/

/-- The closed capability vocabulary.  `data`: may be delayed/transported
    (and, extensionally on this type grammar, compared for equality);
    `eq`: has structural equality — coincides with `data`, kept as a
    separate name because it answers a different question and is what
    diagnostics say; `ord`: has a designer-meaningful order — a quantity, or
    a concept *declared* ordered and represented by a quantity.  Nothing
    is user-definable; there is no instance search and no superclass
    relation (a variable simply lists what it needs). -/
inductive Cap where
  | data
  | eq
  | ord
  deriving DecidableEq, Repr

/-- The ordering declarations of the design: which concepts the designer
    marked as ordered.  Surface metadata, like display names. -/
abbrev OrdDecl := ConceptId → Bool

/-- `ordB O Θ τ`: `τ` has a designer-meaningful order.  Quantities, and
    ordered concepts represented by quantities; never booleans, options,
    lists, pairs or undeclared concepts. -/
def Ty.ordB (O : OrdDecl) (Θ : ConceptEnv) : Ty → Bool
  | .q _ => true
  | .sem s => O s && (match Θ s with | some (.q _) => true | _ => false)
  | _ => false

def Cap.holds (O : OrdDecl) (Θ : ConceptEnv) : Cap → Ty → Prop
  | .data, τ => τ.Data
  | .eq, τ => τ.Data
  | .ord, τ => Ty.ordB O Θ τ = true

instance (O : OrdDecl) (Θ : ConceptEnv) (c : Cap) (τ : Ty) : Decidable (Cap.holds O Θ c τ) := by
  cases c <;> simp only [Cap.holds] <;> infer_instance

/-- **`eq_is_data`**: on the current type grammar the equality capability
    is extensionally the data capability — a proved coincidence, not a
    definition; a future type that is data without equality would separate
    them. -/
theorem Cap.eq_iff_data (O : OrdDecl) (Θ : ConceptEnv) (τ : Ty) : Cap.holds O Θ .eq τ ↔ Cap.holds O Θ .data τ := Iff.rfl

/-- **`ord_implies_data`**: everything ordered is data; the converse fails
    (`ord_not_data_converse`). -/
theorem Cap.ord_data (O : OrdDecl) (Θ : ConceptEnv) : ∀ τ, Cap.holds O Θ .ord τ → Cap.holds O Θ .data τ
  | .q _, _ => trivial
  | .sem _, _ => trivial
  | .bool, h | .nat, h | .arr _ _, h | .opt _, h | .list _, h | .prod _ _, h => by simp [Cap.holds, Ty.ordB] at h

theorem Cap.ord_not_data_converse (O : OrdDecl) (Θ : ConceptEnv) :
    ¬ Cap.holds O Θ .ord .bool ∧ ¬ Cap.holds O Θ .ord (.opt (.q Dim.zero)) ∧
    ¬ Cap.holds O Θ .ord (.list (.q Dim.zero)) ∧ ¬ Cap.holds O Θ .ord (.prod (.q Dim.zero) (.q Dim.zero)) := by
  simp [Cap.holds, Ty.ordB]

/-- A scheme: a pattern whose type variables carry capability requirements. -/
structure Scheme where
  pattern : PTy
  caps : List (Nat × Cap)
  deriving Repr

/-- A substitution admissible for a scheme under the design's declarations. -/
def Scheme.Admits (S : Scheme) (O : OrdDecl) (Θ : ConceptEnv) (σ : Subst) : Prop :=
  ∀ p ∈ S.caps, Cap.holds O Θ p.2 (σ.ty p.1)

instance (S : Scheme) (O : OrdDecl) (Θ : ConceptEnv) (σ : Subst) : Decidable (S.Admits O Θ σ) :=
  inferInstanceAs (Decidable (∀ p ∈ S.caps, Cap.holds O Θ p.2 (σ.ty p.1)))

/-- Use-site elaboration: match, then check the capabilities.  Decidable
    and deterministic; the diagnostics are the two failure points: *no
    instance* (the argument's type does not fit the pattern) and
    *capability failed* (which variable, which capability, which type —
    e.g. "Mode values can be compared for equality, but they have no
    default order"). -/
def Scheme.instantiate (S : Scheme) (O : OrdDecl) (Θ : ConceptEnv) (τ : Ty) : Option Subst :=
  match matchTy S.pattern τ PSubst.empty with
  | some ps => if S.Admits O Θ ps.toSubst then some ps.toSubst else none
  | none => none

theorem Scheme.instantiate_sound {S : Scheme} {O : OrdDecl} {Θ : ConceptEnv} {τ : Ty} {σ : Subst}
    (h : S.instantiate O Θ τ = some σ) : S.pattern.inst σ = τ ∧ S.Admits O Θ σ := by
  unfold Scheme.instantiate at h
  cases hm : matchTy S.pattern τ PSubst.empty with
  | none => rw [hm] at h; exact nomatch h
  | some ps =>
    rw [hm] at h
    by_cases ha : S.Admits O Θ ps.toSubst
    · simp only [ha, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨matchTy_sound hm ps (PSubst.Extends.refl ps), ha⟩
    · simp [ha] at h

end BDL.Poly
