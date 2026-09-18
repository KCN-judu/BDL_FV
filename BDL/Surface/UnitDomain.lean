import BDL.Core.Clock
import BDL.Core.Output
import BDL.Core.Satisfaction

/-!
# Phase 12 — Unit-domain normalization and the source boundary

Production (ADR-0029, `bdl_ir::ty`) gives every relationship one *canonical
type* `domain(inputs) -> B`, where the domain of no inputs is the empty
product `()`, and encodes it into the kernel by currying and unit
elimination: `() -> B` is `B`, `(A, B) -> C` is `A -> B -> C`.  The kernel
(`Base.lean`) has no unit type, and this module does not add one.  It
places the canonical types *above* the kernel, as an interface-normalization
layer, and proves that the encoding is exact:

* `CTy` is production's `Ty` with `Unit`: the canonical type language.
  `canonical s = domainOf s.inputs -> B`.
* `encode s = A₁ -> … -> Aₙ -> B` is the kernel interface type
  (`Ty::kernel_of_signature`, Lean's `expectedType`);
  `canonicalOfKernel` is `Ty::canonical_mapping_ty`.
* **`decode_encode`**, **`canonicalOfKernel_encode`**, **`encode_injective`**:
  the two encodings are inverse over signatures whose output is not an arrow
  (every concept signature).  **`elim_canonical`**: `encode` *is* unit
  elimination and currying applied to the canonical type — the normalization
  is a function on `CTy`, and the kernel type is its value.
* **`zero_input_obligation`**, **`lams_typed`**: a realization of `() -> B`
  is checked at `B` in the empty context — no binder is introduced; a
  realization of `(A₁, …, Aₙ) -> B` is `n` binders around a body checked in
  the context of its inputs.
* **`delay_not_under_binder`**: the literal alternative — a unit binder in
  the kernel — cannot hold memory, because `delay`/`sync` are typed only in
  the empty context.  This is why the unit is eliminated *before* Core.
* **`Ev.declRef_env_irrelevant`**, **`refForms_agree`**, **`same_tick_same_value`**:
  `f`, `f()` and `f(())` are one kernel term, its value at a tick is
  independent of the local environment (the unique argument carries nothing),
  and two readings in one tick agree — there is no repeated call.
* **`Clocked.refForms`**: no clock judgment changes.
* **`source_value`**, **`resolved_not_source`**: a *source* is an unresolved
  declaration; its value is `I d t`, environment provision, whatever the shape
  of its type.  A resolved unit-domain declaration is not a source.
* **`transport_needs_unit_domain`**, **`driver_is_unit_domain`**: the two
  production consequences of the unit domain ("may be transported", "may
  drive an output") are theorems of the existing typing and drive rules.
* **`unit_codomain_collapse`**, **`homUnit`** (in the denotational remark at
  the end): `1 -> B ≅ B`, and every `A -> 1` is one function — `A -> ()`
  cannot name a physical consumer; the drive edge (`Output.lean`) can.
-/

namespace BDL.UnitDomain
open BDL BDL.Reactive BDL.Clock BDL.Output

/-! ## Signatures and canonical types -/

/-- A relationship's signature as production keeps it (`Signature`): the
    input types in order, and the output type.  Production's inputs are
    concept ids, i.e. `sem` types; the results below need only that the
    output is not an arrow. -/
structure Sig where
  inputs : List Ty
  output : Ty
  deriving DecidableEq, Repr

/-- Canonical (interface) types: production's `bdl_ir::Ty` with `Unit`.
    `k τ` embeds a kernel type; `unit` is the empty product; `prod` here is
    a *domain* product (several inputs), distinct from a single input of the
    kernel pair type `k (Ty.prod a b)`.  Never the type of a kernel term. -/
inductive CTy where
  | unit
  | k (τ : Ty)
  | arr (dom cod : CTy)
  | prod (a b : CTy)
  deriving DecidableEq, Repr

/-- `domain([]) = ()`, `domain([A]) = A`, `domain([A, B, …]) = A × (B × …)`
    (`Ty::domain_of`). -/
def domainOf : List Ty → CTy
  | [] => .unit
  | [a] => .k a
  | a :: rest => .prod (.k a) (domainOf rest)

/-- The canonical type `domain(inputs) -> B` (`Ty::of_signature`). -/
def canonical (s : Sig) : CTy := .arr (domainOf s.inputs) (.k s.output)

/-- The kernel encoding `A₁ -> … -> Aₙ -> B`, and `B` for no inputs
    (`Ty::kernel_of_signature`; `DeclInterface.expectedType`). -/
def encode (s : Sig) : Ty := s.inputs.foldr Ty.arr s.output

/-- `a₁ -> … -> aₙ -> b` as `([a₁, …, aₙ], b)` (`Ty::uncurry`). -/
def uncurry : Ty → List Ty × Ty
  | .arr a b => ((uncurry b).1.cons a, (uncurry b).2)
  | τ => ([], τ)

def decode (τ : Ty) : Sig := ⟨(uncurry τ).1, (uncurry τ).2⟩

/-- `Ty::canonical_mapping_ty`: the canonical type back from a kernel one. -/
def canonicalOfKernel (τ : Ty) : CTy := canonical (decode τ)

def Ty.IsArr : Ty → Prop
  | .arr _ _ => True
  | _ => False

instance : ∀ τ : Ty, Decidable (Ty.IsArr τ)
  | .arr _ _ => inferInstanceAs (Decidable True)
  | .bool | .nat | .sem _ | .q _ | .opt _ | .list _ | .prod _ _ => inferInstanceAs (Decidable False)

theorem Ty.sem_not_arr (s : SemanticId) : ¬ Ty.IsArr (.sem s) := fun h => h

/-- A signature over concepts, as production's are. -/
def Sig.Concept (s : Sig) : Prop :=
  (∀ a ∈ s.inputs, ∃ c, a = .sem c) ∧ ∃ c, s.output = .sem c

theorem Sig.Concept.output_not_arr {s : Sig} (h : s.Concept) : ¬ Ty.IsArr s.output := by
  obtain ⟨c, hc⟩ := h.2; rw [hc]; exact Ty.sem_not_arr c

theorem uncurry_of_not_arr {τ : Ty} (h : ¬ Ty.IsArr τ) : uncurry τ = ([], τ) := by
  cases τ <;> first | rfl | exact (h trivial).elim

@[simp] theorem encode_nil (B : Ty) : encode ⟨[], B⟩ = B := rfl
@[simp] theorem encode_cons (a : Ty) (rest : List Ty) (B : Ty) :
    encode ⟨a :: rest, B⟩ = .arr a (encode ⟨rest, B⟩) := rfl

/-- **`encode_decode`**: decoding then encoding is the identity on every
    kernel type — the kernel side loses nothing. -/
theorem encode_decode : ∀ τ : Ty, encode (decode τ) = τ
  | .arr a b => by
    have ih := encode_decode b
    simp only [decode, uncurry, encode, List.foldr_cons] at *
    rw [ih]
  | .bool | .nat | .sem _ | .q _ | .opt _ | .list _ | .prod _ _ => rfl

/-- **`decode_encode`**: encoding then decoding is the identity on every
    signature whose output is not an arrow — so on every concept signature.
    (With an arrow output the last input and the output would be re-split;
    production never has one.) -/
theorem decode_encode (s : Sig) (h : ¬ Ty.IsArr s.output) : decode (encode s) = s := by
  obtain ⟨is, B⟩ := s
  induction is with
  | nil => simp [decode, encode, uncurry_of_not_arr h]
  | cons a rest ih =>
    have ih' := ih h
    simp only [encode, List.foldr_cons, decode, uncurry] at *
    simp only [Sig.mk.injEq] at ih' ⊢
    exact ⟨by rw [ih'.1], ih'.2⟩

/-- **`canonicalOfKernel_encode`**: `Ty::canonical_mapping_ty ∘
    Ty::kernel_of_signature = Ty::of_signature` over concept signatures —
    the production test `…_the_encodings_are_inverse`, for every signature. -/
theorem canonicalOfKernel_encode (s : Sig) (h : ¬ Ty.IsArr s.output) :
    canonicalOfKernel (encode s) = canonical s := by
  unfold canonicalOfKernel; rw [decode_encode s h]

theorem encode_injective {s₁ s₂ : Sig} (h₁ : ¬ Ty.IsArr s₁.output) (h₂ : ¬ Ty.IsArr s₂.output)
    (h : encode s₁ = encode s₂) : s₁ = s₂ := by
  have := congrArg decode h
  rwa [decode_encode s₁ h₁, decode_encode s₂ h₂] at this

theorem domainOf_injective : ∀ {l₁ l₂ : List Ty}, domainOf l₁ = domainOf l₂ → l₁ = l₂
  | [], [], _ => rfl
  | [], [_], h => by simp [domainOf] at h
  | [], _ :: _ :: _, h => by simp [domainOf] at h
  | [_], [], h => by simp [domainOf] at h
  | [a], [b], h => by simp [domainOf] at h; rw [h]
  | [_], _ :: _ :: _, h => by simp [domainOf] at h
  | _ :: _ :: _, [], h => by simp [domainOf] at h
  | _ :: _ :: _, [_], h => by simp [domainOf] at h
  | a :: b :: r, a' :: b' :: r', h => by
    simp only [domainOf, CTy.prod.injEq, CTy.k.injEq] at h
    have := domainOf_injective (l₁ := b :: r) (l₂ := b' :: r') h.2
    rw [h.1, this]

/-- **`canonical_injective`**: the canonical type determines the signature. -/
theorem canonical_injective {s₁ s₂ : Sig} (h : canonical s₁ = canonical s₂) : s₁ = s₂ := by
  simp only [canonical, CTy.arr.injEq, CTy.k.injEq] at h
  obtain ⟨is₁, B₁⟩ := s₁; obtain ⟨is₂, B₂⟩ := s₂
  simp only at h
  rw [domainOf_injective h.1, h.2]

/-! ## Unit elimination as a function on canonical types -/

/-- Measure for `elim`: a domain product weighs twice, so currying
    `(A × B) -> C ↦ A -> (B -> C)` and unit elimination `() -> B ↦ B` both
    decrease it. -/
def CTy.weight : CTy → Nat
  | .unit => 1
  | .k _ => 1
  | .arr d c => 2 * d.weight + c.weight + 1
  | .prod a b => a.weight + b.weight + 1

theorem CTy.weight_pos (t : CTy) : 0 < t.weight := by
  cases t <;> simp [CTy.weight] <;> omega

/-- Unit elimination and currying, as a normalization of canonical types
    into kernel types.  `unit` alone has no kernel type (it is never a
    value's type); `() -> B` is `B`; `(A × B) -> C` is `A -> B -> C`; a
    value-level product stays a kernel `prod`. -/
def elim : CTy → Option Ty
  | .unit => none
  | .k τ => some τ
  | .arr .unit c => elim c
  | .arr (.prod a b) c => elim (.arr a (.arr b c))
  | .arr (.k τ) c => (elim c).map (Ty.arr τ)
  | .arr (.arr a b) c =>
    (elim (.arr a b)).bind fun d => (elim c).map (Ty.arr d)
  | .prod a b => (elim a).bind fun a' => (elim b).map (Ty.prod a')
termination_by t => t.weight
decreasing_by all_goals simp_wf <;> simp [CTy.weight] <;> omega

theorem elim_domain_arrow : ∀ (is : List Ty) (B : Ty),
    elim (.arr (domainOf is) (.k B)) = some (encode ⟨is, B⟩)
  | [], B => by simp [domainOf, elim, encode]
  | [a], B => by simp [domainOf, elim, encode]
  | a :: b :: rest, B => by
    have ih := elim_domain_arrow (b :: rest) B
    simp only [domainOf] at ih ⊢
    rw [elim, elim, ih]
    rfl

/-- **`elim_canonical`**: the kernel encoding *is* unit elimination and
    currying applied to the canonical type.  What production calls two
    isomorphisms is one normalization function, and `expectedType` is its
    value.  In particular `elim (() -> B) = B`. -/
theorem elim_canonical (s : Sig) : elim (canonical s) = some (encode s) :=
  elim_domain_arrow s.inputs s.output

theorem elim_unit_arrow (B : Ty) : elim (.arr .unit (.k B)) = some B := by simp [elim]

/-- The unit itself has no kernel type: it is never the type of a value. -/
theorem elim_unit : elim .unit = none := by simp [elim]

/-! ## Typing: the realization obligation of `() -> B` -/

/-- A realization of a signature is checked at the kernel encoding in the
    empty context, like every realization (`Satisfaction.lean`). -/
def RealizesSig (Θ : ConceptEnv) (Δ : DeclEnv) (G : Grant) (s : Sig) (e : Expr) : Prop :=
  HasType Θ Δ G [] e (encode s)

/-- **`zero_input_obligation`**: the typing obligation of the canonical
    `() -> B` is exactly that of `B` — the same judgment, the same context,
    no binder. -/
theorem zero_input_obligation (Θ : ConceptEnv) (Δ : DeclEnv) (G : Grant) (B : Ty) (e : Expr) :
    RealizesSig Θ Δ G ⟨[], B⟩ e ↔ HasType Θ Δ G [] e B := Iff.rfl

/-- The binders a formula over `inputs` elaborates to (de Bruijn: the last
    input is index 0). -/
def lams : List Ty → Expr → Expr
  | [], body => body
  | a :: rest, body => .lam a (lams rest body)

@[simp] theorem lams_nil (body : Expr) : lams [] body = body := rfl

/-- **`lams_typed`**: a formula body checked in the context of its inputs is
    a realization of the signature's kernel type, and conversely.  For no
    inputs the context is `Γ` itself — the elaboration of `() -> B`
    introduces no binder. -/
theorem lams_typed (Θ : ConceptEnv) (Δ : DeclEnv) (G : Grant) :
    ∀ (is : List Ty) (Γ : Ctx) (body : Expr) (B : Ty),
      HasType Θ Δ G (is.reverse ++ Γ) body B ↔ HasType Θ Δ G Γ (lams is body) (encode ⟨is, B⟩)
  | [], Γ, body, B => by simp [lams, encode]
  | a :: rest, Γ, body, B => by
    have ih := lams_typed Θ Δ G rest (a :: Γ) body B
    rw [List.reverse_cons, List.append_assoc, List.singleton_append, ih]
    constructor
    · intro h; exact HasType.lam h
    · intro h; cases h with | lam h => exact h

/-- **`delay_not_under_binder`**: memory cannot live under a binder — the
    typing rules for `delay` and `sync` demand the empty context.  A literal
    kernel encoding of `() -> B` as a unit lambda would therefore forbid
    every zero-input declaration from holding state; the kernel encoding
    `B` keeps the realization in the empty context, where `delay` is legal.
    This is the reason the unit is eliminated before Core. -/
theorem delay_not_under_binder (Θ : ConceptEnv) (Δ : DeclEnv) (G : Grant)
    {Γ : Ctx} {dom : Ty} {i e : Expr} {τ : Ty} :
    ¬ HasType Θ Δ G Γ (.lam dom (.delay i e)) τ := by
  intro h; cases h with | lam h => cases h

theorem sync_not_under_binder (Θ : ConceptEnv) (Δ : DeclEnv) (G : Grant)
    {Γ : Ctx} {dom : Ty} {c : ClockId} {i e : Expr} {τ : Ty} :
    ¬ HasType Θ Δ G Γ (.lam dom (.sync c i e)) τ := by
  intro h; cases h with | lam h => cases h

/-- A zero-input realization may hold memory under the kernel encoding:
    `delay init e : B` is well typed at `B` whenever `B` is data — exactly
    the production rule "a relationship whose domain is `()` may hold
    memory". -/
theorem zero_input_memory (Θ : ConceptEnv) (Δ : DeclEnv) (G : Grant) {B : Ty} (hB : B.Data)
    {i e : Expr} (hi : HasType Θ Δ G [] i B) (he : HasType Θ Δ G [] e B) :
    RealizesSig Θ Δ G ⟨[], B⟩ (.delay i e) :=
  HasType.delay hB hi he

/-! ## Evaluation: `f`, `f()`, `f(())` -/

/-- The three surface spellings of a reference to a relationship without
    inputs.  `callUnit` is the application to the unique value `()` of the
    empty product. -/
inductive RefForm where
  | bare (d : DeclId)       -- `f`
  | call0 (d : DeclId)      -- `f()`
  | callUnit (d : DeclId)   -- `f(())`
  deriving DecidableEq, Repr

def RefForm.decl : RefForm → DeclId
  | .bare d | .call0 d | .callUnit d => d

/-- Elaboration: one kernel term, the reference.  The unit argument is
    erased here, above the kernel, and no term former for it exists. -/
def RefForm.desugar (r : RefForm) : Expr := .declRef r.decl

theorem RefForm.desugar_bare (d : DeclId) : (RefForm.bare d).desugar = .declRef d := rfl
theorem RefForm.desugar_call0 (d : DeclId) : (RefForm.call0 d).desugar = .declRef d := rfl
theorem RefForm.desugar_callUnit (d : DeclId) : (RefForm.callUnit d).desugar = .declRef d := rfl

/-- **`Ev.declRef_env_irrelevant`**: the value of a reference at a tick does
    not depend on the local environment `ρ` — a realized declaration is
    evaluated in the empty environment, an unresolved one is read from the
    input.  So there is nothing an argument to `f` could carry. -/
theorem Ev.declRef_env_irrelevant {Δ : DeclEnv} {I : Input} {t : Nat} {ρ ρ' : List Value} {d : DeclId}
    {v : Value} (h : Ev Δ I t ρ (.declRef d) v) : Ev Δ I t ρ' (.declRef d) v := by
  cases h with
  | refRealized hs hb => exact .refRealized hs hb
  | refInput hn => exact .refInput hn

theorem MEv.declRef_env_irrelevant {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat}
    {ρ ρ' : List Value} {d : DeclId} {v : Value}
    (h : MEv S Δ I c t ρ (.declRef d) v) : MEv S Δ I c t ρ' (.declRef d) v := by
  cases h with
  | refRealized hs hb => exact .refRealized hs hb
  | refInput hn => exact .refInput hn

/-- **`refForms_agree`**: `f`, `f()` and `f(())` denote the same observation
    of the declaration — in every domain, at every tick, under every
    environment. -/
theorem refForms_agree {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat}
    {ρ : List Value} {v : Value} {r₁ r₂ : RefForm} (h : r₁.decl = r₂.decl) :
    MEv S Δ I c t ρ r₁.desugar v ↔ MEv S Δ I c t ρ r₂.desugar v := by
  simp [RefForm.desugar, h]

/-- **`same_tick_same_value`**: two readings of one declaration in one tick
    agree, whatever their local environments.  There is no per-reference
    call: a zero-input declaration is evaluated as a declaration, once per
    activation, and every reference observes that value. -/
theorem same_tick_same_value {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat}
    {ρ₁ ρ₂ : List Value} {d : DeclId} {v₁ v₂ : Value}
    (h₁ : MEv S Δ I c t ρ₁ (.declRef d) v₁) (h₂ : MEv S Δ I c t ρ₂ (.declRef d) v₂) : v₁ = v₂ :=
  h₁.det (MEv.declRef_env_irrelevant (ρ' := ρ₁) h₂)

/-! ## Clocks -/

/-- **`Clocked.refForms`**: the three spellings have one clock judgment,
    the reference's.  The unit argument has no domain, no activation and no
    evaluation step: it is not a term. -/
theorem Clocked.refForms (Κ : ClockEnv) (c : Option ClockId) (r : RefForm) :
    Clocked Κ c r.desugar ↔ Clocked Κ c (.declRef r.decl) := Iff.rfl

theorem HasType.refForms (Θ : ConceptEnv) (Δ : DeclEnv) (G : Grant) (Γ : Ctx) (r : RefForm) (τ : Ty) :
    HasType Θ Δ G Γ r.desugar τ ↔ HasType Θ Δ G Γ (.declRef r.decl) τ := Iff.rfl

/-! ## The source role -/

/-- The *source role*: an unresolved declaration.  Its value at every tick
    is provided by the environment (`Input`), not computed.  This is a
    property of the realization state, not of the type. -/
def Source (Δ : DeclEnv) (d : DeclId) : Prop := Δ.realizationOf d = none

/-- The *unit-domain shape*: a declaration whose interface type is not an
    arrow, i.e. whose canonical type is `() -> B`. -/
def UnitDomain (Δ : DeclEnv) (d : DeclId) : Prop :=
  ∃ τ, Δ.tyView d = some τ ∧ ¬ Ty.IsArr τ

theorem UnitDomain.decode {Δ : DeclEnv} {d : DeclId} (h : UnitDomain Δ d) :
    ∃ τ, Δ.tyView d = some τ ∧ (decode τ).inputs = [] := by
  obtain ⟨τ, hτ, hn⟩ := h
  exact ⟨τ, hτ, by simp only [BDL.UnitDomain.decode, uncurry_of_not_arr hn]⟩

/-- **`source_value`**: a source's value is `I d t` — environment provision
    at the tick, independent of the local environment, of the domain the
    reader is in, and of the shape of the declaration's type.  The unique
    argument of `() -> A` carries no temporal or environmental information
    because the information is indexed by `(d, t)` alone. -/
theorem source_value {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat}
    {ρ : List Value} {d : DeclId} {v : Value} (hs : Source Δ d)
    (h : MEv S Δ I c t ρ (.declRef d) v) : v = I d t := by
  cases h with
  | refRealized hr => exact absurd (hs.symm.trans hr) (by simp)
  | refInput => rfl

theorem source_reads {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat}
    {ρ : List Value} {d : DeclId} (hs : Source Δ d) : MEv S Δ I c t ρ (.declRef d) (I d t) :=
  .refInput hs

/-- **`resolved_not_source`**: a unit-domain declaration with a realization
    is *not* a source — its value is its realization's, and the input stream
    is never consulted for it.  `() -> B` is a type shape; the source role is
    a realization state.  Every mathematical `() -> A` is not a sensor. -/
theorem resolved_not_source {S : Sched} {Δ : DeclEnv} {I I' : Input} {c : ClockId} {t : Nat}
    {ρ : List Value} {d : DeclId} {b : Expr} {v : Value}
    (hr : Δ.realizationOf d = some b) (h : MEv S Δ I c t ρ (.declRef d) v) :
    ¬ Source Δ d ∧ MEv S Δ I c t [] b v ∧
      (∀ w, MEv S Δ I' c t [] b w → MEv S Δ I' c t ρ (.declRef d) w) := by
  refine ⟨fun hs => ?_, ?_, fun w hw => MEv.refRealized hr hw⟩
  · unfold Source at hs; rw [hr] at hs; exact nomatch hs
  cases h with
  | refRealized hr' hb => rw [hr] at hr'; cases hr'; exact hb
  | refInput hn => rw [hr] at hn; exact nomatch hn

/-- The kernel's `Input` provides a value for every unresolved declaration,
    whatever its type; production narrows the *simulation input* role to
    unresolved unit-domain declarations, because what an environment
    provides is a value, not a function.  The narrowing is a surface policy
    over the same semantics: on a unit-domain source the two agree. -/
def SimulationInput (Δ : DeclEnv) (d : DeclId) : Prop := Source Δ d ∧ UnitDomain Δ d

theorem SimulationInput.value {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat}
    {ρ : List Value} {d : DeclId} {v : Value} (hs : SimulationInput Δ d)
    (h : MEv S Δ I c t ρ (.declRef d) v) : v = I d t :=
  source_value hs.1 h

/-! ## The two production consequences of the unit domain -/

/-- **`transport_needs_unit_domain`**: only a value can be transported.  A
    well-typed `sync` of a reference forces the referenced declaration's type
    to be data, hence not an arrow, hence unit-domain — production's
    `reference.transport_of_relationship` is a corollary of the existing
    typing rule for `sync`. -/
theorem transport_needs_unit_domain {Θ : ConceptEnv} {Δ : DeclEnv} {G : Grant}
    {c : ClockId} {i : Expr} {d : DeclId} {τ : Ty}
    (h : HasType Θ Δ G [] (.sync c i (.declRef d)) τ) : UnitDomain Δ d := by
  cases h with
  | sync hd _ he =>
    cases he with
    | declRef hv =>
      refine ⟨_, hv, ?_⟩
      cases τ <;> first | exact fun h => h | exact fun _ => hd

theorem delay_needs_unit_domain {Θ : ConceptEnv} {Δ : DeclEnv} {G : Grant}
    {i : Expr} {d : DeclId} {τ : Ty}
    (h : HasType Θ Δ G [] (.delay i (.declRef d)) τ) : UnitDomain Δ d := by
  cases h with
  | delay hd _ he =>
    cases he with
    | declRef hv =>
      refine ⟨_, hv, ?_⟩
      cases τ <;> first | exact fun h => h | exact fun _ => hd

/-- **`driver_is_unit_domain`**: a drive edge consumes a value of the sink's
    accepted type.  When the sink accepts a non-arrow type (every concept),
    the driver is a unit-domain declaration: "a relationship without inputs
    may drive an output" is the drive rule, not a separate permission. -/
theorem driver_is_unit_domain {Ω : OutputEnv} {Κ : ClockEnv} {Δ : DeclEnv} {β : DriveEnv}
    (hw : DriveWF Ω Κ Δ β) {d : DeclId} {o : OutputId} (hb : β d = some o)
    (hacc : ∀ spec, Ω o = some spec → ¬ Ty.IsArr spec.accepts) : UnitDomain Δ d := by
  obtain ⟨spec, hΩ, hty, _⟩ := hw d o hb
  exact ⟨spec.accepts, hty, hacc spec hΩ⟩

/-! ## `A -> ()` cannot name a consumer: the denotational remark

The kernel has no unit type, so `A -> ()` is not a kernel type; this is the
argument that it should not become one.  In any model where `1` is the
one-point type, `Hom(1, B) ≅ B` — a function out of the point is its value at
the point — and every function into `1` is the same function.  Two
"consumers" `sink₁ sink₂ : A -> ()` are therefore indistinguishable in a pure
total language: nothing in a value of that type says *which* physical output
receives `A`.  BDL names the receiver by `OutputId` and the drive edge
(`Output.lean`), and the value delivered is the driver's, a value of type `A`. -/

/-- A bijection, without importing any library. -/
structure Iso (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

/-- **`homUnit`**: `(1 → β) ≅ β`.  Evaluation at the unique point and the
    constant function are inverse. -/
def homUnit (β : Type) : Iso (Unit → β) β where
  toFun f := f ()
  invFun b := fun _ => b
  left_inv _ := rfl
  right_inv _ := rfl

/-- **`unit_codomain_collapse`**: all functions into the unit are equal
    (extensionally — the only axiom this uses is quotient soundness, through
    function extensionality). -/
theorem unit_codomain_collapse {α : Type} (f g : α → Unit) : f = g :=
  funext fun _ => rfl

/-- Consequently a type `A -> 1` has exactly one inhabitant up to
    extensionality: it cannot distinguish two physical consumers. -/
theorem consumers_indistinguishable {α : Type} (sink₁ sink₂ : α → Unit) : sink₁ = sink₂ :=
  unit_codomain_collapse sink₁ sink₂

/-- The kernel's evaluation relation has no effect component: a derivation
    relates a tick, an environment, a term and a value, and nothing else.
    The physical consequence of a value is the drive edge, which lives
    outside evaluation (`PhysicalOutput`).  Stated as the observation that
    two drive environments that agree on nothing evaluate every term
    identically. -/
theorem eval_independent_of_drives {S : Sched} {Δ : DeclEnv} {I : Input} {c : ClockId} {t : Nat}
    {ρ : List Value} {e : Expr} {v : Value} (_ : DriveEnv) (_ : DriveEnv)
    (h : MEv S Δ I c t ρ e v) : MEv S Δ I c t ρ e v := h

end BDL.UnitDomain
