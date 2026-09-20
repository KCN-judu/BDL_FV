# Abstract {-}

Interactive physical products are designed by people who state *relationships* before they can define them: a lamp's brightness follows its tilt; the room's temperature is read once a second while the tilt is read fifty times a second; the light is the product's only physical effect. We present $\lambda_{\mathrm{BDL}}$, the core calculus of the Behavior Design Language, in which such a design is a finite environment of *persistent declarations* — each a stable identity, a frozen expected type with a growable set of public commitments, and an optional realization — over a simply typed term language extended with nominal *concept* types bound write-once to data representations, a *construction grant* derived from the declaration's own signature, physical *dimensions* carried by operator types, ordinary data (options, lists, products) with one list recursor, and exactly one temporal primitive: read a *clock domain* at its last activation strictly before now. We give the calculus a tick-indexed big-step semantics and prove it deterministic and total on *causal* designs by a tick-indexed logical relation with a lexicographic induction on (tick, instantaneous rank, derivation); the single-domain semantics is the diagonal of the multi-domain one, memory is transport at the own domain, and no scheduler order is observable. We prove that refining a declaration — adding a commitment, supplying a body, strengthening a realized interface with re-verification — preserves every client's typing unconditionally and every client's discharged commitment provided the validation layer's evidence is monotone in the environment, and we show by a mechanized counterexample that the monotonicity condition is necessary. Semantic identity has no runtime residue (erasure is sound), cannot be manufactured except where a signature announces it (construction is granted, and provenance is preserved through memory and transport), and is orthogonal to dimension. Physical effect passes through explicit drive edges with a single driver per output, which makes the physical output a function of the tick. Behavior components are derived from renaming and realization alone, and flattening a composition yields an ordinary design checked by the unchanged judgments. Every definition and theorem is mechanized in Lean 4 with no `sorry` and no classical choice; every rejected alternative is a mechanized counterexample; every trace is computed by an interpreter proved sound for the relation.

**Keywords:** reactive semantics, clock domains, nominal types, refinement, logical relations, mechanized metatheory, Lean 4, synchronous languages, units of measure

# Introduction

A behavior designer working on an interactive physical product does something that a programmer's language makes awkward: they *declare a relationship they cannot yet define*. "Brightness follows tilt" is a complete design statement long before anyone knows the formula; it has a type — the concept `Tilt` to the concept `Brightness` — and other parts of the design depend on it at that type. Later the relationship acquires a formula, a promise ("monotone"), a timing domain, a physical output; none of these later steps should disturb what already depended on it. The formula must be unable to produce anything but a `Brightness`, even though a brightness and an opacity are both represented by a dimensionless number and a tilt and a motor angle are both angles. Values must be remembered across time with an explicit first value, and read across timing domains without making the scheduler visible. Physical effect must happen exactly once per output, explicitly.

This paper presents the core calculus that gives these requirements a semantics and proves that they compose: $\lambda_{\mathrm{BDL}}$, the kernel of the Behavior Design Language (BDL). The calculus is deliberately small. Its term language is a simply typed λ-calculus with registered first-order operators; what makes it a *design* calculus is not its terms but the environments they are typed and evaluated against, and the two disciplines those environments impose — a *refinement order* on declarations, and a *grant* on the construction of nominal values.

## What the calculus adds to the simply typed λ-calculus

- **Persistent declarations** (§4). A design is an environment $\Delta$ of declarations $\langle \mathit{id}, \langle \tau, C\rangle, \mathit{realization}\rangle$ with a stable identity, a frozen expected type, a growable list of public commitments, and an optional body. Terms refer to declarations by identity, and the typing judgment reads $\Delta$ through exactly one projection, the *type view*. A refinement order on declarations and environments captures the operations that a client may survive; everything else is an *edit* about which nothing is promised. We prove that refinement preserves every client's typing with no hypothesis, and every client's discharged commitment under a Kripke-style monotonicity condition on the validation layer's evidence — a condition we show necessary (Theorems 4–5, Proposition 6).
- **Nominal concepts with granted construction** (§5). A concept is a nominal type $\text{sem}\;s$; a concept environment $\Theta$ binds it, write-once, to a representation type that is data and mentions no concept. Observing a representation ($\text{rep}$) is always permitted; constructing a value ($\text{mk}\;s$) requires a grant, and a declaration's body is granted exactly the concepts in result position of its own signature. Under that discipline a hidden crossing between concepts is untypable, erasure to the representation is sound, and no tag is created by evaluation, memory, or transport (Theorems 8, 9 and 14).
- **Dimensions in operator types** (§5.3). A physical quantity has type $\text{q}\;d$ for an exponent vector $d$; the algebra lives entirely in the registered operators' types and no typing rule mentions it. The dimensionless baseline is the erasure of this typing, exactly as the numeric baseline is the erasure of nominal typing.
- **One temporal primitive** (§6–7). $\text{sync}\;c\;\mathit{init}\;e$ reads $e$ in clock domain $c$ at $c$'s last activation strictly before the current tick, or $\mathit{init}$ if there is none; $\text{delay}$ is $\text{sync}$ at the own domain. The semantics is tick-indexed big-step evaluation against an input stream and a schedule. It is deterministic unconditionally and total on *causal* designs — those whose instantaneous dependency graph is acyclic — by a logical relation indexed by the tick with a lexicographic induction on tick, rank and derivation (Theorems 10–13, 18–19). The delayed type must be data and $\text{delay}$ may appear only at top level; both restrictions are forced by the totality proof rather than chosen. Clock domains are nominal identities, not rates; the *strictly before* rule makes the semantics independent of any order between simultaneously active domains, and the alternative is mechanically shown to expose the scheduler (Theorem 20).
- **Data with one recursor** (§8). Options, lists and products are ordinary data; $\text{fold}$ is the one term former that applies a function value during evaluation. Its evaluation rule unrolls syntactically through the environment so that the evaluation relation remains an ordinary inductive relation. Polymorphism is rank-1 by definitional families instantiated by one-way matching against closed types; no type variable enters the kernel. The lossless cross-domain window buffer — the one construction a designer would expect to be primitive — is five declarations over $\text{delay}$, $\text{sync}$ and list operators, with a correctness theorem for every schedule (Theorem 21).
- **Explicit outputs** (§9). A declaration computes a value; hardware moves only through a drive edge to a nominally identified output with a single driver. With one driver the physical output is a partial function of the tick; with a hidden arbitration policy three different outputs arise from one design (Theorem 23).
- **Composition by renaming** (§10). Behavior components, fresh instantiation, bindings and flattening are derived from realization steps and an equivariance theorem for every judgment; the flattened system is an ordinary design accepted by the unchanged checkers (Theorems 24–26).

## Mechanization and claims

Every definition, theorem and counterexample in this paper is a Lean 4 declaration in the development `KCN-judu/BDL_FV` [@moura2021lean]. The development builds with no `sorry`; the axioms used are propositional extensionality and quotient soundness (the latter only through function extensionality), and classical choice is absent. Negative results are theorems whose content is a rejection; every trace is computed by an interpreter proved sound for the evaluation relation, inside the proof checker. The paper cites the Lean name of each result at the point it is stated, and Appendix A indexes them by section.

Two conventions bound the claims. *Minimal* always means minimal among the alternatives that were formalized and refuted, never a minimality theorem. Where a theorem is proved for a fragment — the modular-semantics result holds for single-domain wiring designs with direct bindings — the restriction is part of the statement.

## What this paper is not

It is not a paper about the surface language, the authoring environment or the production toolchain that implements the calculus; those are described in the BDL monograph, of which this paper is the formal core. It is not a paper about hardware validation or deployment, which live above the kernel as decidable relations that never enter typing or evaluation. And it is not a new type-theoretic mechanism: each ingredient is a known shape — the interface/implementation separation of module signatures [@leroy1994manifest; @harper1994modules], an abstract type with a private constructor [@mitchell1988abstract], a Kripke-style stability condition, the `pre` of Lustre [@halbwachs1991lustre] confined to nodes, a step-indexed logical relation [@appel2001indexed; @ahmed2006stepindexed]. What is specific is where the ingredients come from — the grant from the signature the designer already wrote, the domain from an authored identity rather than an inferred clock, the buffer from two reads of a log — and that their combination has been proved to compose.

# Overview: a lamp in $\lambda_{\mathrm{BDL}}$

We fix a small product to make the calculus concrete: a lamp whose brightness follows its tilt, dims smoothly, and warms its base according to the room temperature. The design begins with concepts and signatures and nothing else.

**Concepts.** `Tilt`, `Brightness`, `RoomTemp` and `MotorAngle` are semantic identities $s \in \text{SemanticId}$. Each is a nominal type $\text{sem}\;s$. The concept environment $\Theta$ binds `Tilt` and `MotorAngle` to $\text{q}\;\text{Angle}$ and `Brightness` to $\text{q}\;0$; the two angles remain distinct types.

**Declarations before definitions.** The relationship `dimByTilt : Tilt -> Brightness` is a declaration $\langle d_1, \langle \text{sem}\;\text{Tilt} \to \text{sem}\;\text{Brightness}, [\,]\rangle, \text{none}\rangle$: an identity, an interface, and no body. `tilt : Tilt` is a declaration with no body that will never receive one — an *input*, whose value the environment supplies at every tick. `light : Brightness` is realized as $\text{app}\;(\text{declRef}\;d_1)\;(\text{declRef}\;\mathit{tilt})$ and is well typed now, against $d_1$'s interface, whether or not $d_1$ ever acquires a formula.

**Refinement.** Giving `dimByTilt` the body $\lambda x{:}\text{sem}\;\text{Tilt}.\;\text{mk}\;\text{Brightness}\;(\text{clamp}\;(\text{rep}\;x \,/\, 90^\circ)\;0\;1)$ — where `90 deg` is surface notation for a dimensioned literal $\text{lit}_{\text{Angle}}$ and `clamp` for a library term over $\text{lt}$ and $\text{ite}$ — is a refinement step. The body is typed under the grant $\{\text{Brightness}\}$ — the concepts in result position of `Tilt -> Brightness` — so $\text{mk}\;\text{Brightness}$ is permitted and $\text{mk}\;\text{MotorAngle}$ would not be. `light`'s typing is untouched (Theorem 4). Adding the commitment `monotone` to `dimByTilt` later is a refinement; changing its expected type is an edit.

**Memory.** A smooth dimmer remembers its previous output: `smooth : Brightness` realized as a mix of `light` and $\text{delay}\;\mathit{init}\;(\text{declRef}\;\mathit{smooth})$. The self-reference is a structural cycle every path of which passes through a delayed operand; the design is *causal* and has a value at every tick (Theorem 13). The initial value is part of the syntax: without it the first tick is undefined or nondeterministic, and both failure modes are mechanized.

**Clock domains.** `tilt` and `light` live in a domain `fast`; `roomTemp` and `heat` in a domain `slow`. Domains are nominal: a clone of `fast` with the same schedule is a different domain, and a direct wire between them is rejected by the domain judgment. `heat` may read the tilt only through $\text{sync}\;\text{fast}\;\mathit{init}\;(\text{declRef}\;\mathit{light})$, whose value is `light` at the last `fast` activation strictly before the current `slow` tick. Typing is blind to domains and unchanged.

**Output.** The physical light is an output identity $o$ accepting $\text{sem}\;\text{Brightness}$ in domain `fast`; the drive edge $\beta\;\mathit{smooth} = \text{some}\;o$ is well formed because the types are equal and the domains agree, and it is the only driver of $o$. Nothing else in the design has a physical effect.

Sections 3–10 give each of these steps its rules and theorems.

# The calculus

## Syntax

Figure 1 gives the syntax. Types are those of a simply typed calculus with booleans, counts and arrows, extended by nominal concept types $\text{sem}\;s$ over an identity $s$, physical quantities $\text{q}\;d$ over a dimension $d$, and the data formers $\text{opt}$, $\text{list}$ and $\times$. A dimension is an exponent vector over a fixed finite set of base dimensions (length, time, angle, mass, temperature in the development); dimensions form an abelian group under pointwise addition, which is the only structure the calculus uses.

$$
\begin{array}{rl}
& s \in \text{SemanticId} \qquad d \in \text{Dim} \qquad c \in \text{ClockId} \qquad \delta \in \text{DeclId} \qquad o \in \text{OutputId}\\[3pt]
\tau,\sigma \;\text{::=}\; & \text{bool} \mid \text{nat} \mid \tau \to \sigma \mid \text{sem}\;s \mid \text{q}\;d \mid \text{opt}\;\tau \mid \text{list}\;\tau \mid \tau \times \sigma\\[3pt]
e \;\text{::=}\; & x \mid \text{true} \mid \text{false} \mid n \mid \lambda x{:}\tau.\,e \mid e\;e \mid \text{declRef}\;\delta \mid \text{rep}\;e \mid \text{mk}\;s\;e \mid p\\
\mid\; & \text{delay}\;e\;e \mid \text{sync}\;c\;e\;e \mid \text{fold}\;e\;e\;e\\[3pt]
p \;\text{::=}\; & \text{lit}_d\,n \mid \text{add}_d \mid \text{sub}_d \mid \text{mul}_{d_1 d_2} \mid \text{div}_{d_1 d_2} \mid \text{lt}_d \mid \text{eq}_\tau^{h} \mid \neg \mid \wedge \mid \vee \mid \text{ite}_\tau\\
\mid\; & \text{none}_\tau \mid \text{some}_\tau \mid \text{isSome}_\tau \mid \text{getD}_\tau \mid \text{nil}_\tau \mid \text{cons}_\tau \mid \text{length}_\tau \mid \text{take}_\tau \mid \text{drop}_\tau \mid \text{reverse}_\tau \mid \text{head}_\tau\\
\mid\; & \text{toList}_\tau \mid \text{pair}_{\tau\sigma} \mid \text{fst}_{\tau\sigma} \mid \text{snd}_{\tau\sigma}
\end{array}
$$

*Figure 1. Syntax of $\lambda_{\mathrm{BDL}}$. Variables are de Bruijn indices in the development; the paper writes names. $h$ in $\text{eq}_\tau^{h}$ is a proof that $\tau$ is a data type.*

Terms are those of the λ-calculus plus five design-specific forms. $\text{declRef}\;\delta$ refers to a declaration by identity; nothing about the declaration's interface or body is in the syntax. $\text{rep}\;e$ observes the representation of a concept value and $\text{mk}\;s\;e$ constructs one. $\text{delay}\;i\;e$ is the value of $e$ at the previous activation of the current domain, $i$ before any; $\text{sync}\;c\;i\;e$ is the value of $e$ in domain $c$ at $c$'s last activation strictly before now, $i$ if none. $\text{fold}\;f\;z\;l$ is the list recursor, $\text{fold}\;f\;z\;[x_1,\dots,x_n] = f\;x_1\;(\cdots(f\;x_n\;z))$. Registered operators $p$ are first-order constants with types; they never apply a closure.

Two predicates on types recur. A type is **data**, $\tau.\text{Data}$, when no arrow occurs in it; a type is **concept-free**, $\tau.\text{SemFree}$, when no $\text{sem}$ occurs in it. Both are decidable by structural recursion, and $(\tau \times \sigma).\text{Data} \iff \tau.\text{Data} \wedge \sigma.\text{Data}$, $(\text{list}\;\tau).\text{Data} \iff \tau.\text{Data}$ hold definitionally (`Ty.prod_data`, `Ty.list_data`).

## Environments

A term is typed and evaluated against several environments, each read through a stated projection and nothing else. This discipline — *which environment a judgment may see* — is what the metatheory rests on, and each theorem's hypotheses name the environments it depends on.

- A **declaration** is a triple
  $$\text{DesignDecl} = \langle\, \mathit{id} : \text{DeclId},\ \mathit{interface} : \langle \mathit{expectedType} : \text{Ty},\ \mathit{commitments} : \text{PropertyId}^{*}\rangle,\ \mathit{realization} : \text{Option}\;\text{Expr} \,\rangle .$$
  A **design** is a declaration environment $\Delta : \text{DeclId} \to \text{Option}\;\text{DesignDecl}$. Its *type view* $\Delta^{\mathrm{ty}}(\delta) = (\Delta\;\delta).\text{map}(\cdot.\mathit{interface}.\mathit{expectedType})$ is all that typing sees; its *realization view* $\Delta^{\mathrm{real}}(\delta) = (\Delta\;\delta).\text{bind}(\cdot.\mathit{realization})$ is all that evaluation sees. An **unresolved** declaration is one whose realization is $\text{none}$; nothing else distinguishes it.
- A **concept environment** $\Theta : \text{SemanticId} \to \text{Option}\;\text{Ty}$ binds each concept to a representation. It is well formed, $\Theta.\text{WF}$, when every bound representation is concept-free and data: $\Theta\;s = \text{some}\;R \Rightarrow R.\text{SemFree} \wedge R.\text{Data}$.
- A **grant** $G : \text{SemanticId} \to \text{Prop}$ says which concepts a term may construct. $\text{Grant.none}$ permits nothing; $\text{Grant.of}\;\tau$ permits the concepts in result position of $\tau$, $\text{grant}(\text{sem}\;s) = [s]$, $\text{grant}(\tau \to \sigma) = \text{grant}(\sigma)$, $\text{grant}(\_) = [\,]$.
- A **clock environment** $\mathrm{K} : \text{DeclId} \to \text{Option}\;\text{ClockId}$ assigns each declaration a domain; $\text{none}$ is a domain-agnostic pure mapping. A **schedule** $S : \text{ClockId} \to \mathbb{N} \to \text{Bool}$ says at which global ticks each domain activates. An **input** $I : \text{DeclId} \to \mathbb{N} \to \text{Value}$ supplies a value for every unresolved declaration at every tick.
- An **output environment** $\Omega : \text{OutputId} \to \text{Option}\;\langle \mathit{accepts} : \text{Ty}, \mathit{clock} : \text{ClockId}\rangle$ and the **drive edges** $\beta : \text{DeclId} \to \text{Option}\;\text{OutputId}$ are introduced in §9.

Typing sees $\Theta$, $\Delta^{\mathrm{ty}}$ and $G$. Evaluation sees $\Delta^{\mathrm{real}}$, $I$ and (in several domains) $S$. The domain judgment sees $\mathrm{K}$. Outputs see $\Omega$, $\mathrm{K}$, $\Delta^{\mathrm{ty}}$ and $\beta$. Commitments and evidence are seen by the satisfaction relation of §4 and by nothing else.

## Typing

The typing judgment $\Theta;\Delta;G;\Gamma \vdash e : \tau$ is given in Figure 2. Rules T-Var, T-Bool, T-Nat, T-Lam and T-App are those of the simply typed λ-calculus. T-Ref is the only rule that reads $\Delta$, and it reads the type view. T-Rep and T-Mk read $\Theta$ through the binding $\Theta\;s = \text{some}\;R$; T-Mk additionally requires the grant. T-Prim assigns each registered operator its type; the dimension algebra is entirely in that table (Figure 3), so an application of $\text{mul}_{d_1 d_2}$ is checked by T-App like any other. T-Delay and T-Sync require the type to be data and the context to be empty; T-Fold types the recursor.

$$
\frac{\Gamma(x) = \tau}{\Theta;\Delta;G;\Gamma \vdash x : \tau}\ \text{(T-Var)}
\qquad
\frac{}{\Theta;\Delta;G;\Gamma \vdash b : \text{bool}}\ \text{(T-Bool)}
\qquad
\frac{}{\Theta;\Delta;G;\Gamma \vdash n : \text{nat}}\ \text{(T-Nat)}
$$

$$
\frac{\Theta;\Delta;G;\Gamma, x{:}\tau \vdash e : \sigma}{\Theta;\Delta;G;\Gamma \vdash \lambda x{:}\tau.\,e : \tau \to \sigma}\ \text{(T-Lam)}
\qquad
\frac{\Theta;\Delta;G;\Gamma \vdash f : \tau \to \sigma \quad \Theta;\Delta;G;\Gamma \vdash a : \tau}{\Theta;\Delta;G;\Gamma \vdash f\;a : \sigma}\ \text{(T-App)}
$$

$$
\frac{\Delta^{\mathrm{ty}}(\delta) = \text{some}\;\tau}{\Theta;\Delta;G;\Gamma \vdash \text{declRef}\;\delta : \tau}\ \text{(T-Ref)}
\qquad
\frac{}{\Theta;\Delta;G;\Gamma \vdash p : \text{ty}(p)}\ \text{(T-Prim)}
$$

$$
\frac{\Theta\;s = \text{some}\;R \quad \Theta;\Delta;G;\Gamma \vdash e : \text{sem}\;s}{\Theta;\Delta;G;\Gamma \vdash \text{rep}\;e : R}\ \text{(T-Rep)}
\qquad
\frac{G\;s \quad \Theta\;s = \text{some}\;R \quad \Theta;\Delta;G;\Gamma \vdash e : R}{\Theta;\Delta;G;\Gamma \vdash \text{mk}\;s\;e : \text{sem}\;s}\ \text{(T-Mk)}
$$

$$
\frac{\tau.\text{Data} \quad \Theta;\Delta;G;[\,] \vdash i : \tau \quad \Theta;\Delta;G;[\,] \vdash e : \tau}{\Theta;\Delta;G;[\,] \vdash \text{delay}\;i\;e : \tau}\ \text{(T-Delay)}
$$

$$
\frac{\tau.\text{Data} \quad \Theta;\Delta;G;[\,] \vdash i : \tau \quad \Theta;\Delta;G;[\,] \vdash e : \tau}{\Theta;\Delta;G;[\,] \vdash \text{sync}\;c\;i\;e : \tau}\ \text{(T-Sync)}
$$

$$
\frac{\Theta;\Delta;G;\Gamma \vdash f : \tau \to \sigma \to \sigma \quad \Theta;\Delta;G;\Gamma \vdash z : \sigma \quad \Theta;\Delta;G;\Gamma \vdash l : \text{list}\;\tau}{\Theta;\Delta;G;\Gamma \vdash \text{fold}\;f\;z\;l : \sigma}\ \text{(T-Fold)}
$$

*Figure 2. Typing (`HasType`). T-Ref is the only rule reading $\Delta$; T-Rep and T-Mk the only rules reading $\Theta$; T-Mk the only rule reading $G$.*

| operator | type | operator | type |
|---|---|---|---|
| $\text{lit}_d\,n$ | $\text{q}\;d$ | $\text{eq}_\tau^{h}$ | $\tau \to \tau \to \text{bool}$ |
| $\text{add}_d,\ \text{sub}_d$ | $\text{q}\;d \to \text{q}\;d \to \text{q}\;d$ | $\text{ite}_\tau$ | $\text{bool} \to \tau \to \tau \to \tau$ |
| $\text{mul}_{d_1 d_2}$ | $\text{q}\;d_1 \to \text{q}\;d_2 \to \text{q}\;(d_1 + d_2)$ | $\text{some}_\tau$ | $\tau \to \text{opt}\;\tau$ |
| $\text{div}_{d_1 d_2}$ | $\text{q}\;d_1 \to \text{q}\;d_2 \to \text{q}\;(d_1 - d_2)$ | $\text{getD}_\tau$ | $\text{opt}\;\tau \to \tau \to \tau$ |
| $\text{lt}_d$ | $\text{q}\;d \to \text{q}\;d \to \text{bool}$ | $\text{toList}_\tau$ | $\text{opt}\;\tau \to \text{list}\;\tau$ |
| $\text{length}_\tau$ | $\text{list}\;\tau \to \text{q}\;0$ | $\text{cons}_\tau$ | $\tau \to \text{list}\;\tau \to \text{list}\;\tau$ |
| $\text{head}_\tau$ | $\text{list}\;\tau \to \text{opt}\;\tau$ | $\text{take}_\tau,\ \text{drop}_\tau$ | $\text{q}\;0 \to \text{list}\;\tau \to \text{list}\;\tau$ |
| $\text{fst}_{\tau\sigma}$ | $\tau \times \sigma \to \tau$ | $\text{pair}_{\tau\sigma}$ | $\tau \to \sigma \to \tau \times \sigma$ |

*Figure 3. Types of the registered operators (`Prim.ty`), abridged. Dimension algebra lives here and nowhere else. $\text{eq}$ is available at every data type and $\text{lt}$ at quantities only.*

Three features of Figure 2 carry the rest of the paper.

*The typing boundary.* Typing depends on the type view of declarations and the representation view of concepts and on nothing else — not on realizations, commitments, evidence, clocks or drive edges. The client-stability theorem of §4 is a one-line consequence, and its necessity is a one-line counterexample.

*The construction boundary.* Client code is typed under $\text{Grant.none}$; a declaration's realization is typed under $\text{Grant.of}$ its own expected type (§4.1). A value of $\text{sem}\;s$ is therefore constructed only inside a declaration whose signature announces $\text{sem}\;s$. This is the whole of the semantic-isolation mechanism, and §5 shows what each weaker alternative admits.

*The temporal boundary.* $\text{delay}$ and $\text{sync}$ are typed only in the empty context and only at data types. Both restrictions were forced by the totality proof of §6, not chosen: a delayed closure would have to be transported across ticks, and a delay under a binder would re-evaluate its operand at the previous tick in an environment created at the current one. Temporal state therefore belongs to declarations, and mappings are pointwise — the arrangement of `pre` in Lustre, where it lives in nodes rather than in functions [@halbwachs1991lustre].

## Inference, uniqueness and monotonicity

Inference is syntax-directed. A function $\text{infer}\;\Theta\;\Delta\;G\;\Gamma\;e : \text{Option}\;\text{Ty}$ follows the rules of Figure 2 and needs only decidability of $G$, of type equality and of $\tau.\text{Data}$.

**Theorem 1 (Inference; `infer_sound`, `infer_complete`, `HasType.unique`).** $\text{infer}\;\Theta\;\Delta\;G\;\Gamma\;e = \text{some}\;\tau$ iff $\Theta;\Delta;G;\Gamma \vdash e : \tau$; hence typing is decidable and every term has at most one type.

Uniqueness matters beyond decidability: it is why the surface language's polymorphism can be *matching* rather than unification (§8.4), and why a nominal mismatch is reported as "Brightness and Opacity are different concepts" and never as a unification residue.

**Theorem 2 (Monotonicity; `HasType.mono_env`, `HasType.mono_concept`, `HasType.mono_grant`).** Typing is monotone in each of its three environments: if $\Theta;\Delta;G;\Gamma \vdash e : \tau$, then the same holds in any $\Delta'$ with $\text{EnvRefines}\;\Delta\;\Delta'$ (§4.2), any $\Theta'$ that binds at least what $\Theta$ binds, and any $G' \supseteq G$.

Weakening holds for the delay-free fragment by appending to the context (`HasType.weaken_append`); a stateful term cannot be moved under a binder at all, so no stronger weakening is needed.

# Declarations, interfaces and refinement

The foundational object is the declaration, and the foundational question is which changes to a declaration its clients survive. This section fixes the answer: a *refinement order*, the three steps that generate it, and two preservation theorems with deliberately different hypotheses.

## Interfaces, evidence and satisfaction

An interface $S = \langle \tau, C\rangle$ is an expected type and a list of commitments — atomic labels such as `total`, `monotone`, `bounded` that a client may rely on. Interfaces are ordered by monotone refinement:
$$
S \sqsubseteq S' \;:=\; S.\tau = S'.\tau \;\wedge\; S.C \subseteq S'.C ,
$$
a decidable preorder, frozen on the type and growing on commitments (`InterfaceRefines`). Nothing else is an interface refinement.

What discharges a commitment is not the kernel's business; it is the validation layer's. The kernel abstracts it as an **evidence** relation $\mathit{ev} : \text{DeclEnv} \to \text{Expr} \to \text{PropertyId} \to \text{Prop}$. Evidence takes the environment because compositional discharge needs it — "$A$ is monotone because $B$ is committed to be monotone" consults $B$'s interface. A body $e$ **satisfies** $S$ in $\Theta,\Delta,\Gamma$ when it has the expected type under the grant of that type and every commitment is discharged:
$$
\text{Satisfies}\;\mathit{ev}\;\Theta\;\Delta\;\Gamma\;e\;S \;:=\; \Theta;\Delta;\text{Grant.of}(S.\tau);\Gamma \vdash e : S.\tau \;\wedge\; \forall p \in S.C.\;\mathit{ev}\;\Delta\;e\;p .
$$
A declaration is well formed when its body, if any, satisfies its interface; a design is **globally well formed**, $\text{GlobalWF}\;\mathit{ev}\;\Theta\;\Delta$, when every stored declaration sits under its own identity and is well formed in $\Delta$ at top level. An unresolved declaration is always well formed.

The refinement order is complete for abstract evidence: $S \sqsubseteq S'$ iff every realization of $S'$ in every environment under every evidence relation realizes $S$ (`InterfaceRefines_iff_semantic`). The proof of the converse instantiates evidence at "the property is in $S'$'s list" and the body at a reference to a single declaration.

## The refinement order and the lifecycle

A declaration takes a refinement step in one of three ways (`DeclRefines`), each preserving the identity by construction and each checked against the current environment $\Delta$:
$$
\frac{S \sqsubseteq S'}{\langle \delta, S, \text{none}\rangle \rightsquigarrow \langle \delta, S', \text{none}\rangle}
\qquad
\frac{\text{Satisfies}\;\mathit{ev}\;\Theta\;\Delta\;\Gamma\;e\;S}{\langle \delta, S, \text{none}\rangle \rightsquigarrow \langle \delta, S, \text{some}\;e\rangle}
\qquad
\frac{S \sqsubseteq S' \quad \text{Satisfies}\;\mathit{ev}\;\Theta\;\Delta\;\Gamma\;e\;S'}{\langle \delta, S, \text{some}\;e\rangle \rightsquigarrow \langle \delta, S', \text{some}\;e\rangle}
$$
An unresolved declaration may have its interface refined; an unresolved declaration may be realized by a satisfying body; a realized declaration may have its interface strengthened provided the body is *re-verified* against the new interface. Strengthening without re-verification breaks well-formedness, and the counterexample is mechanized (`naive_breaks_wellformedness`).

Separately from the steps there is a purely structural order with no satisfaction condition: $\text{DeclLeq}\;h\;h'$ requires the same identity, $h.S \sqsubseteq h'.S$, and a write-once realization ($h.\mathit{realization} = \text{some}\;e \Rightarrow h'.\mathit{realization} = \text{some}\;e$); $\text{EnvRefines}\;\Delta\;\Delta'$ lifts it pointwise and permits new declarations. Storing a refined declaration back under its identity is an environment refinement — $\Delta\;h.\mathit{id} = \text{some}\;h \wedge \text{DeclLeq}\;h\;h' \Rightarrow \text{EnvRefines}\;\Delta\;(\Delta[h'])$ (`EnvRefines_update`) — and this is the one place identity does any work: it makes the update land on the slot every reference resolves to, which is what a name does in any environment semantics.

**Theorem 3 (The lifecycle is the structural order; `DeclRefinesStar_iff`).** The reflexive–transitive closure of the three steps, all side conditions checked in $\Delta$, relates $h$ to $h'$ iff $\text{DeclLeq}\;h\;h'$ and $h'$ is well formed in $\Delta$.

## Client stability

Can a declaration be refined or realized without editing its clients, and without invalidating what was established about them? The answer has two halves.

**Theorem 4 (Client stability, typing; `local_refinement_preserves_global_typing`).** If $\Delta\;B.\mathit{id} = \text{some}\;B$ and $\text{DeclLeq}\;B\;B'$, then every judgment $\Theta;\Delta;G;\Gamma \vdash e : \tau$ holds in $\Delta[B']$.

The proof is one line: typing reads $\Delta$ through the type view, and the type view is invariant under $\text{DeclLeq}$. The theorem should be read as such — its content is that letting clients see interfaces and never bodies is *sufficient* for client stability. It is also necessary: change $B$'s expected type while keeping its identity and every client breaks; that is why the type is frozen in $\sqsubseteq$.

The commitment half needs more.

**Definition (Monotone evidence).** $\mathit{ev}$ is **monotone** when $\text{EnvRefines}\;\Delta_1\;\Delta_2 \wedge \mathit{ev}\;\Delta_1\;e\;p \Rightarrow \mathit{ev}\;\Delta_2\;e\;p$. Evidence that ignores the environment is monotone; evidence that consults only the *presence* of commitments and realizations is monotone; evidence that consults their *absence* is not.

**Theorem 5 (Client stability, commitments; `local_refinement_preserves_global_wf`, `local_lifecycle_preserves_global_wf`).** If $\mathit{ev}$ is monotone, $\text{GlobalWF}\;\mathit{ev}\;\Theta\;\Delta$, $\Delta\;B.\mathit{id} = \text{some}\;B$ and $B \rightsquigarrow B'$ with side conditions checked in $\Delta$, then $\text{GlobalWF}\;\mathit{ev}\;\Theta\;(\Delta[B'])$. The same holds for a whole lifecycle $B \rightsquigarrow^{*} B'$ checked against the original $\Delta$.

**Proposition 6 (Monotonicity is necessary; `badEv_not_mono`).** There is an evidence relation $\mathit{ev}_{\mathrm{bad}}$, a globally well formed two-declaration design, and a valid realization step of one declaration after which the design is not globally well formed; consequently $\mathit{ev}_{\mathrm{bad}}$ is not monotone.

The relation $\mathit{ev}_{\mathrm{bad}}$ discharges "$A$ is total" whenever the declaration $A$ reads is still unresolved — evidence from absence. Realizing that declaration is a perfectly valid step, and it destroys the discharge. The monotonicity hypothesis was not part of the original design; it appeared when Theorem 5 was attacked, and it is a Kripke-style stability condition on the validation layer: any discharge mechanism meant to survive refinement must be positive in the environment.

Binding a representation to a previously unbound concept is likewise a refinement: typing, satisfaction and global well-formedness are monotone in $\Theta$ (`GlobalWF.of_conceptRefines`). Rebinding a concept to a different representation is an edit that breaks existing realizations (`representation_change_is_edit_not_refinement`).

## Refinement versus edit

Theorems 4–5 cover refinement only. Table 1 classifies the operations a tool offers on a declaration $B$ read by a client $A$; each row is witnessed by a mechanized example on a two-declaration design.

| operation on $B$ | kind | effect on $A$ |
|---|---|---|
| add a public commitment | refinement | typing and commitments preserved |
| realize | refinement | preserved; $A$ now unfolds to a closed program |
| strengthen a realized interface | refinement, with re-verification | preserved |
| change the expected type, keep identity | edit | typing broken |
| drop a commitment | edit | typing silent; $A$'s commitment broken |
| replace $B$ by a new identity | edit | dangling reference |
| detach or replace the realization | edit | evidence that consulted the body is void |
| assign or change a clock domain (§7) | edit | domain judgment on clients broken |
| retarget an output binding (§9) | edit | completeness or single-driver may break |

*Table 1. Refinement versus edit.*

Two rows are instructive. Dropping a commitment changes no type, so the type checker is silent, yet $A$'s own commitment was discharged through $B$'s and is now unsupported: commitments are part of the interface in the same load-bearing sense as the expected type. Detaching a realization is an edit for the same reason. The kernel does not forbid edits; it declines to promise anything about them.

## Unfolding

Before time enters, the semantics of a design is *unfolding*: replace each reference to a realized declaration by its body, recursively, stopping at unresolved declarations ($\text{Unfolds}\;\Delta\;e\;e'$). Let $\text{DependsOn}\;\Delta\;a\;b$ hold when the body of $a$ refers to $b$.

**Theorem 7 (Unfolding; `Unfolds.det`, `Unfolds.exists_of_acyclic`, `Unfolds.not_of_cyclic`, `Unfolds.refFree_of_fullyRealized`).** Unfolding is deterministic; on the delay-free fragment it exists iff the reference graph is acyclic; a reference on a cycle through realized declarations has no unfolding at all; and a fully realized well-typed design unfolds to a reference-free program of the same type.

Acyclicity is witnessed by a rank that strictly decreases along edges, $\text{Acyclic}\;\Delta := \exists\,\mathit{rank}.\;\forall a\,b.\;\text{DependsOn}\;\Delta\;a\;b \to \mathit{rank}\;b < \mathit{rank}\;a$, and excludes cycles (`Acyclic.not_cyclic`). The pure fragment has no fixpoints, so a cyclic definition denotes nothing; §6 shows which cycles become meaningful once $\text{delay}$ exists, and that unfolding agrees with tick evaluation on the first-order fragment (Theorem 15).

# Nominal concepts, representation and dimensions

Section 4 typed declarations without saying what a type means. This section adds the two things a product concept carries that a number does not — an identity that survives representation, and a physical dimension — and states the theorems that make the identity trustworthy.

## Nominal identity and the grant

Suppose concepts were represented only by their representation types, so that `Tilt` and `MotorAngle` are both $\text{q}\;\text{Angle}$. Then the wire `motorTarget := tiltSensor` is well typed and the design is globally well formed, because nothing in the model records the distinction. Nominal types $\text{sem}\;s$ over an internal identity record it: two distinct identities are distinct types regardless of representation, so the invalid wire is rejected by T-App with no additional judgment. An explicit relationship `tiltToMotor : Tilt -> MotorAngle` is an ordinary declaration of arrow type — signature-first, possibly unresolved — and it appears in the term wherever a crossing occurs. The kernel has no cast, coercion or conversion.

Nominal identity alone leaves concept values opaque: under T-Ref and T-App only, a value of $\text{sem}\;s$ can originate only in a declaration of semantic type (`no_semantic_value_without_declaration`). To let a formula realize a mapping, representation must be observable and constructible, and the obvious way to add it destroys what identity just bought. With global $\text{rep}_s : \text{sem}\;s \to R$ and $\text{mk}_s : R \to \text{sem}\;s$ available everywhere, $\lambda x.\;\text{mk}_{\mathrm{Motor}}(\text{rep}_{\mathrm{Tilt}}\;x)$ is a well-typed `Tilt -> MotorAngle` in the empty environment with no declaration and no mapping (`unrestricted_representation_binding_bypasses_semantic_identity`), and the crossing can hide inside a body whose signature mentions no motor (`hidden_crossing_inside_unrelated_body`). Observation alone is safe but cannot realize a mapping.

The grant separates the two. $\text{rep}$ is typed everywhere (T-Rep); $\text{mk}\;s$ is typed only where $G\;s$ (T-Mk); client code is typed under $\text{Grant.none}$ and a body under $\text{Grant.of}$ of its own signature (the definition of $\text{Satisfies}$). Let $e.\text{constructs}\;s$ hold when $\text{mk}\;s$ occurs in $e$.

**Theorem 8 (Construction is granted; `HasType.constructs_granted`).** If $\Theta;\Delta;G;\Gamma \vdash e : \tau$ and $e.\text{constructs}\;s$, then $G\;s$. Under $\text{Grant.of}\;\tau$: a value of $\text{sem}\;s$ is built only inside a realization whose signature announces $\text{sem}\;s$.

The hidden crossing above is rejected under the grant of an unrelated declaration and becomes legal, and visible, once `tiltToMotor` is declared (`hidden_crossing_rejected_under_grant`, `representation_binding_does_not_enable_hidden_semantic_mapping`).

Two constraints on representations in $\Theta.\text{WF}$ were not anticipated. Representations must be concept-free: if `Tilt` may be represented *by* `MotorAngle`, then $\text{rep}$ itself is a hidden mapping under every policy including observation-only. And they must be data, a requirement that arrived from the reactive semantics: a concept value may be delayed, and a function-typed representation would carry a closure across ticks.

The grant is a known shape — the private constructor of an abstract type exported only to its defining module [@mitchell1988abstract], or a capability attached to a definition site. What is specific is that the capability comes from the signature the designer already wrote, so no annotation is added, and one consequence follows: after all bodies are inlined into one program, that program is checked under the universal grant, because each construction was authorized at its own declaration. Semantic isolation is a property of the design graph and survives inlining as provenance (Theorem 14), not as a type property of the executable.

## Erasure

Let $\rho : \text{SemanticId} \to \text{Ty}$ map each concept to a data type, agreeing with $\Theta$ on bound concepts. Erasure $\tau^{\rho}$ replaces $\text{sem}\;s$ by $\rho\;s$ throughout a type; on terms, $\text{rep}\;e$ and $\text{mk}\;s\;e$ erase to $e^{\rho}$, and the type indices of operators are erased.

**Theorem 9 (Erasure is sound; `HasType.erase`).** If $\Theta.\text{WF}$, $\rho$ agrees with $\Theta$, and $\Theta;\Delta;G;\Gamma \vdash e : \tau$, then $\Theta;\Delta^{\rho};G';\Gamma^{\rho} \vdash e^{\rho} : \tau^{\rho}$ for every grant $G'$.

Erasure is not injective — `Tilt` and `MotorAngle` erase to the same type (`erase_not_injective`) — and the untyped baseline is exactly what erasure leaves: the design the nominal calculus rejects is accepted after erasure (`baseline_is_erased_modelA`). Generated code is therefore ordinary code; the semantic layer has no runtime residue.

Three alternatives were formalized and refuted. A model in which the display name *is* the identity makes renaming destructive (`rename_under_name_identity_breaks_client`), whereas here a rename preserves identity (`semantic_rename_preserves_identity`). Treating a concept as an ordinary declaration admits category errors: the concept becomes usable as a value and can be realized by a number. Keeping identity out of the type as interface metadata checked by a direct-wire rule is evaded by η-expansion, since $(\lambda x.\,x)\;\mathit{tilt}$ has the same flow with no direct wire (`bweak_evaded_by_eta`); a compositional role judgment strong enough to close that gap has the rule shapes of typing over $\text{sem}$ and duplicates it.

## Dimensions

A physical quantity has type $\text{q}\;d$. There is no dimension-specific typing rule: $\text{add}_d : \text{q}\;d \to \text{q}\;d \to \text{q}\;d$, $\text{mul}_{d_1 d_2} : \text{q}\;d_1 \to \text{q}\;d_2 \to \text{q}\;(d_1 + d_2)$ and $\text{div}_{d_1 d_2}$ with $d_1 - d_2$ are registered operators, and an application is checked by T-App. `length + time` is ill typed (`dimension_mismatch_rejected`); erasing every dimension to the zero vector is a sound translation that accepts it (`counterexampleB_baseline_accepts_length_plus_time`), so the untyped numeric baseline is the erasure of dimensional typing in the same sense that it is the erasure of nominal typing.

Dimension and identity are orthogonal. `Tilt` and `MotorAngle` both bound to $\text{q}\;\text{Angle}$ remain distinct types (`same_dimension_does_not_imply_same_semantic_identity`); a mapping realized by the dimensioned formula $\lambda x.\;\text{mk}\;\text{Brightness}\;(\text{rep}\;x \cdot \mathit{gain})$ with $\mathit{gain} : \text{q}\;(0 - \text{Angle})$ is typed, a dimension error inside it is caught by the same typing, and the formula cannot manufacture a `MotorAngle` despite the shared dimension (`explicit_semantic_mapping_uses_dimensioned_formula`). The association between a concept and its dimension lives in $\Theta$, not in the identity and not in the type constructor.

Units are not in the calculus at all. A literal `90 deg` elaborates to $\text{lit}_{\text{Angle}}$ of a scaled magnitude; a coordinate $\text{inUnit}(q, u)$ is $q$ divided by a scale constant and has dimension zero; $\text{withUnit}(x, u)$ is the converse; a conversion is their composition. Each is elaboration, none is a kernel construct, and a unit choice never reaches a type: `1 m` and `100 cm` are equal values of one type. The unit laws are proved above the kernel over an abstract scalar domain and instantiated exactly by a symbolic group in which π is a generator, so that a degree is exactly π/180 radian; we do not develop them here. Dimensional typing is thus Kennedy's discipline [@kennedy1997units; @kennedy2010units] without unit polymorphism in the kernel: dimension variables appear only in the surface's definitional families (§8.4), where matching against closed dimensions instantiates them.

# Reactive semantics in one domain

Every declaration denotes a stream over a tick domain. This section gives the single-domain semantics — one primitive, $\text{delay}$ — and proves it deterministic and total on causal designs. Section 7 generalizes it to many domains and shows that this section is the diagonal of that one.

## Values and evaluation

Values are booleans, naturals (which also carry every $\text{q}\;d$; the executable kernel's magnitudes are naturals), tagged concept values $\text{sem}\;s\;v$, $\text{none}$, $\text{some}\;v$, lists, pairs, closures $\text{clo}\;\rho\;e$ over a value environment, and partially applied operators $\text{prim}\;p\;\vec{v}$. An operator is computed when saturated: $\text{applyPrim}\;p\;\vec{v}$ is $\text{compute}\;p\;\vec{v}$ if $|\vec{v}|$ equals $p$'s arity and $\text{prim}\;p\;\vec{v}$ otherwise.

The judgment $\rho \vdash_t e \Downarrow v$ — the value of $e$ at tick $t$ under local environment $\rho$, with the design $\Delta$ and the input $I$ ambient — is defined in Figure 4 (`Ev`).

$$
\frac{\rho(x) = v}{\rho \vdash_t x \Downarrow v}
\qquad
\frac{}{\rho \vdash_t \lambda x{:}\tau.\,e \Downarrow \text{clo}\;\rho\;e}
\qquad
\frac{}{\rho \vdash_t p \Downarrow \text{applyPrim}\;p\;[\,]}
$$

$$
\frac{\rho \vdash_t f \Downarrow \text{clo}\;\rho'\;b \quad \rho \vdash_t a \Downarrow w \quad w\,\text{::}\,\rho' \vdash_t b \Downarrow v}{\rho \vdash_t f\;a \Downarrow v}
\qquad
\frac{\rho \vdash_t f \Downarrow \text{prim}\;p\;\vec{u} \quad \rho \vdash_t a \Downarrow w}{\rho \vdash_t f\;a \Downarrow \text{applyPrim}\;p\;(\vec{u}{+\!\!+}[w])}
$$

$$
\frac{\Delta^{\mathrm{real}}(\delta) = \text{some}\;b \quad [\,] \vdash_t b \Downarrow v}{\rho \vdash_t \text{declRef}\;\delta \Downarrow v}\ \text{(E-Real)}
\qquad
\frac{\Delta^{\mathrm{real}}(\delta) = \text{none}}{\rho \vdash_t \text{declRef}\;\delta \Downarrow I\;\delta\;t}\ \text{(E-Input)}
$$

$$
\frac{\rho \vdash_t e \Downarrow \text{sem}\;s\;w}{\rho \vdash_t \text{rep}\;e \Downarrow w}
\qquad
\frac{\rho \vdash_t e \Downarrow w}{\rho \vdash_t \text{mk}\;s\;e \Downarrow \text{sem}\;s\;w}
$$

$$
\frac{\rho \vdash_0 i \Downarrow v}{\rho \vdash_0 \text{delay}\;i\;e \Downarrow v}\ \text{(E-Delay0)}
\qquad
\frac{\rho \vdash_t e \Downarrow v}{\rho \vdash_{t+1} \text{delay}\;i\;e \Downarrow v}\ \text{(E-DelayS)}
$$

$$
\frac{\rho \vdash_t f \Downarrow v_f \quad \rho \vdash_t z \Downarrow v_z \quad \rho \vdash_t l \Downarrow \text{list}\,[\,]}{\rho \vdash_t \text{fold}\;f\;z\;l \Downarrow v_z}\ \text{(E-FoldNil)}
$$

$$
\frac{\begin{array}{c}\rho \vdash_t f \Downarrow v_f \quad \rho \vdash_t z \Downarrow v_z \quad \rho \vdash_t l \Downarrow \text{list}\,(x\,\text{::}\,\mathit{xs})\\ {}[\text{list}\,\mathit{xs},\, v_z,\, v_f] \vdash_t \text{fold}\;\#2\;\#1\;\#0 \Downarrow r \qquad [r,\, x,\, v_f] \vdash_t \#2\;\#1\;\#0 \Downarrow v\end{array}}{\rho \vdash_t \text{fold}\;f\;z\;l \Downarrow v}\ \text{(E-FoldCons)}
$$

*Figure 4. Single-domain evaluation (`Ev`), with $\Delta$ and $I$ ambient. In one domain $\text{sync}\;c$ evaluates exactly as $\text{delay}$ (rules `syncZero`, `syncSucc`), which §7 justifies. Literals evaluate to themselves. $\#i$ is de Bruijn index $i$.*

Three points of Figure 4 deserve comment. An unresolved declaration is an *input*: E-Input reads $I\;\delta\;t$. A realized declaration is evaluated from its body at the current tick in the *empty* environment (E-Real): a reference's value never depends on the local environment of the reader, which is what makes a declaration a stream rather than a function of its call site (`Ev.declRef_env_irrelevant`). And $\text{delay}$ shifts the tick: read at $t+1$, it evaluates its operand at $t$; at $0$ it evaluates the initial value.

The recursor's rule unrolls syntactically. Rather than a recursive definition of a fold on values, the rule evaluates the syntactic term $\text{fold}\;\#2\;\#1\;\#0$ in an environment holding the tail, the seed and the function, and then the term $\#2\;\#1\;\#0$ in an environment holding the result, the head and the function. This keeps $\text{Ev}$ an ordinary inductive relation with no mutual recursion, so every proof by induction on $\text{Ev}$ that predated the recursor extends by one case, and totality is a separate lemma by induction on the list (§8.1).

**Theorem 10 (Determinism; `Ev.det`).** If $\rho \vdash_t e \Downarrow v_1$ and $\rho \vdash_t e \Downarrow v_2$ then $v_1 = v_2$.

Evaluation is a partial function with no hidden evaluation order — there are no effects to order — and this holds unconditionally.

An executable interpreter $\text{evalF}$ with a fuel parameter is proved sound for the relation (`evalF_sound`, `Ev.of_evalF`). Every trace in the development and in this paper was computed by it inside the proof checker.

## Cycles and causality

Let $e.\text{instRefs}$ be the declarations $e$ refers to *instantaneously*: those not under the delayed operand of a $\text{delay}$ or $\text{sync}$ (the initial value is read at tick $0$ and counts as instantaneous). $\text{InstDependsOn}\;\Delta\;a\;b$ holds when $b \in \text{instRefs}$ of $a$'s body.

**Definition (Causal).** $\text{Causal}\;\Delta := \exists\,\mathit{rank}\,R.\;(\forall \delta.\;\mathit{rank}\;\delta < R) \wedge \forall a\,b.\;\text{InstDependsOn}\;\Delta\;a\;b \to \mathit{rank}\;b < \mathit{rank}\;a$.

On the delay-free fragment $\text{InstDependsOn}$ is $\text{DependsOn}$, so causality is exactly bounded acyclicity (`Causal_iff_acyclic_of_delayFree`): the earlier condition is the timeless special case rather than a replaced requirement. A structural cycle every path of which passes through a delayed operand — `A := delay 0 B; B := A`, or a self-delayed accumulator — is causal. A cycle that is partly delayed is not.

**Theorem 11 (Strict cycles have no value; `Ev.not_of_strictCyclic`).** If $a$ lies on a cycle of references passing through neither a delayed operand nor a lambda, then for every tick and environment there is no $v$ with $\rho \vdash_t \text{declRef}\;a \Downarrow v$.

Not "some default", not "one of several": no derivation exists. A gap should be recorded. A cycle guarded by a lambda, `A := λx. A x`, is rejected by $\text{Causal}$ yet `declRef A` does evaluate — to a closure; only applying it diverges. $\text{Causal}$ is conservative for lambda-guarded cycles and Theorem 11 covers strict cycles only.

## The logical relation and totality

Totality is proved by a logical relation indexed by the tick. The relation is stated generically in an *application relation* $A : \text{Value} \to \text{Value} \to \text{Value} \to \text{Prop}$ — how a function value applied to an argument yields a result — so that the single-domain and multi-domain semantics share one relation. At a fixed tick, $A$ is $\text{Apply}\;\Delta\;I\;t$: $v_f$ applied to $w$ yields $v$ when $v_f$ is a closure whose body evaluates to $v$ at $t$ under $w$, or a partial operator whose saturation is $v$.

$$
\begin{array}{rl}
\mathcal{R}^{A}_{\Theta}[\text{bool}]\;v \iff & \exists b.\;v = \text{bool}\;b\\
\mathcal{R}^{A}_{\Theta}[\text{nat}]\;v \;=\; \mathcal{R}^{A}_{\Theta}[\text{q}\;d]\;v \iff & \exists n.\;v = \text{nat}\;n\\
\mathcal{R}^{A}_{\Theta}[\text{opt}\;\tau]\;v \iff & v = \text{none} \;\vee\; \exists w.\;v = \text{some}\;w \wedge \mathcal{R}^{A}_{\Theta}[\tau]\;w\\
\mathcal{R}^{A}_{\Theta}[\text{list}\;\tau]\;v \iff & \exists \vec{w}.\;v = \text{list}\;\vec{w} \wedge \forall w \in \vec{w}.\;\mathcal{R}^{A}_{\Theta}[\tau]\;w\\
\mathcal{R}^{A}_{\Theta}[\tau \times \sigma]\;v \iff & \exists x\,y.\;v = \text{pair}\;x\;y \wedge \mathcal{R}^{A}_{\Theta}[\tau]\;x \wedge \mathcal{R}^{A}_{\Theta}[\sigma]\;y\\
\mathcal{R}^{A}_{\Theta}[\tau \to \sigma]\;v \iff & \forall w.\;\mathcal{R}^{A}_{\Theta}[\tau]\;w \to \exists v'.\;A\;v\;w\;v' \wedge \mathcal{R}^{A}_{\Theta}[\sigma]\;v'\\
\mathcal{R}^{A}_{\Theta}[\text{sem}\;s]\;v \iff & \exists w.\;v = \text{sem}\;s\;w \wedge \forall R.\;\Theta\;s = \text{some}\;R \to \mathcal{R}^{A}[R]\;w
\end{array}
$$

The concept clause says that a concept value is a tagged representation value. Its inner use of the relation at the representation $R$ is the concept-free relation $\text{RedSF}$; because $\Theta.\text{WF}$ makes $R$ concept-free, the definition is well founded on the type without appeal to $\Theta$ (`Red_semFree`). At data types the relation is independent of $A$ (`Red_data`), which is what allows a delayed value to be transported between ticks. Registered operators are related at their types for any $A$ that saturates them (`Red_prim`).

Well-typed inputs are inputs related to the type view: $\Delta^{\mathrm{ty}}(\delta) = \text{some}\;\tau \wedge \Delta^{\mathrm{real}}(\delta) = \text{none} \Rightarrow \mathcal{R}^{\text{Apply}\;\Delta\;I\;t}_{\Theta}[\tau]\;(I\;\delta\;t)$ for every $t$.

**Theorem 12 (Fundamental theorem; `fundamental`).** Let $\Theta.\text{WF}$, let $\mathit{rank}, R$ witness $\text{Causal}\;\Delta$, let $\text{GlobalWF}\;\mathit{ev}\;\Theta\;\Delta$ and let $I$ be well typed. Then for every tick $t$, bound $r$, grant $G$, and $\Theta;\Delta;G;\Gamma \vdash e : \tau$, and every $\rho$ related to $\Gamma$ such that every instantaneous reference of $e$ has rank below $r$, there is $v$ with $\rho \vdash_t e \Downarrow v$ and $\mathcal{R}^{\text{Apply}\;\Delta\;I\;t}_{\Theta}[\tau]\;v$.

*Proof sketch.* Lexicographic induction on $(t, r, \text{derivation})$. A delayed operand at tick $t+1$ is evaluated at tick $t$ under *any* rank (the first component decreases); an instantaneous reference to a realized declaration $\delta$ is evaluated at the same tick under the smaller bound $\mathit{rank}\;\delta$ (the second decreases), and its body is well typed under the grant of its own signature by $\text{GlobalWF}$; every other case is the induction on the derivation. The $\text{fold}$ case uses `fold_total` (§8.1). $\square$

**Theorem 13 (Totality; `reactive_total`, `Ev.red`).** In a causal, globally well formed design with well-typed inputs, every declared identity has a value at every tick, and that value — unique by Theorem 10 — is related to its expected type.

The relation is a step-indexed logical relation in the sense of Appel and McAllester [@appel2001indexed] and Ahmed [@ahmed2006stepindexed], with the tick as the index and the rank as a second, inner index; what differs is that the index counts *time* rather than *steps*, so that the induction on it is the induction that makes a delayed self-reference well defined.

## Two restrictions forced by totality

T-Delay and T-Sync restrict their type to data and their context to empty. Neither restriction was a design decision; each is what the induction of Theorem 12 needs. A delayed closure would be a value at tick $t$ related by $\mathcal{R}^{\text{Apply}\;\Delta\;I\;t}$ that must be transported to tick $t+1$, and the arrow clause is tick-indexed and cannot be transported; `Red_data` is exactly the statement that data clauses can. A delay under a binder would evaluate its operand at the previous tick in an environment created at the current one. The restrictions have two corollaries stated as theorems: nothing of function type can be delayed or transported (`arrow_not_delayable`, by inversion), and memory and transport are typed only in the empty context (`delay_not_under_binder`, `sync_not_under_binder`). Temporal state therefore belongs to declarations, and a reusable stateful component is instantiated into fresh declarations (§10) rather than abstracted over.

Initialization is semantic, not validation. Every $\text{delay}$ carries an explicit initial value. Two toy relations without one show why: the first tick is either undefined (`first_tick_undefined_without_init`) or nondeterministic (`first_tick_nondeterministic_without_init`).

## Provenance through time

State carries semantic tags; it never creates them. Let $v.\text{Taints}\;s$ hold when the tag $s$ occurs anywhere inside $v$ — including inside closures' environments and bodies.

**Theorem 14 (Tag provenance; `Ev.tag_provenance`, `temporal_state_preserves_semantic_identity`).** If no realization in $\Delta$ constructs $s$, no input value is tainted by $s$, $e$ does not construct $s$ and $\rho$ is clean, then every value $\rho \vdash_t e \Downarrow v$ is clean. In particular a delayed value carries exactly the tag of the value delayed.

Combined with Theorem 8 this is the runtime half of semantic isolation: a concept appears in a value only if some signature announces it or some input carries it, at every tick. The typing rule $\text{delay} : \tau \to \tau \to \tau$ at data $\tau$ gives the static half — a delayed tilt is a tilt, and a backward difference over a time step has dimension $\text{Length} - \text{Time}$ with no derivative primitive.

## Wiring designs and unfolding

The first-order fragment of interest to a compiler consists of *wiring* terms — references, literals, operators, applications, $\text{rep}$, $\text{mk}$, $\text{delay}$ and $\text{sync}$, with no lambda — and designs all of whose bodies are wiring terms. On this fragment closures never arise (`Ev.noClo`) and evaluation is independent of the local environment (`Ev.env_irrelevant`).

**Theorem 15 (Unfolding preserves stepping; `unfolds_preserves_eval`).** On a wiring design with closure-free inputs, if $\text{Unfolds}\;\Delta\;e\;e'$ then $\rho \vdash_t e \Downarrow v$ iff $\rho \vdash_t e' \Downarrow v$.

This licenses inlining: the value of the unfolded program at a tick is the value of the referencing program. A more general statement is available for *pure* terms — closed terms with no reference, state or transport — whose value is the same in every design, at every tick, under every input (`Ev.pure`); §8.4 uses it for the definitional library.

## Derived temporal operators

Every temporal operator a surface language offers reduces to $\text{delay}$ and registered operators. Table 2 lists the elaborations; each is a declaration referring to itself — a self-delayed cycle, the class that structural acyclicity forbade and causality licenses — and each was typed, checked causal, and run on a concrete trace. There is no independent kernel definition of `count` for the reduction to be proved equal to; the claim is that the elaboration has the intended trace.

| surface | declaration body |
|---|---|
| `previous x` | $\text{delay}\;\mathit{init}\;x$ |
| `previous x` without an initial value | $\text{delay}\;\text{none}\;(\text{some}\;x)$; the absence is pushed to consumers |
| `hold init e` | $\text{getD}\;e\;(\text{delay}\;\mathit{init}\;\mathit{self})$ |
| `count e` | $\text{ite}\;(\text{isSome}\;e)\;(1 + \text{delay}\;0\;\mathit{self})\;(\text{delay}\;0\;\mathit{self})$ |
| `since e` | $\text{ite}\;(\text{isSome}\;e)\;0\;(1 + \text{delay}\;0\;\mathit{self})$ |
| `once e` | $\text{delay}\;\text{false}\;\mathit{self} \vee \text{isSome}\;e$ |
| `every n` | a modulo-$n$ counter over $\text{delay}$ |
| `rise b` | $b \wedge \neg\,\text{delay}\;\text{false}\;b$, as an optional Boolean |

*Table 2. Derived temporal operators (`Experiments/ReactiveAlternatives.lean`).*

There is no signal type in $\text{Ty}$: under this semantics a signal type would be inhabited by exactly the terms of the underlying type and would reject nothing. There is no event type: within one domain an input delivers at most one value per tick by construction, so an occurrence is a stream of optional type, and the streams of type $\text{opt}\;\tau$ are exactly the streams of multiplicity at most one. What separates an occurrence from an optional value can only be seen when a source ticks faster than its observer, which is a cross-domain question (§7.5). State has no identity of its own: a cell is a $\text{delay}$ in a declaration body, consumers refer to the declaration, and there is consequently no notion of two writers to one cell.

# Clock domains

"Contact and orientation move with the interaction; temperature moves with the environment." A designer can say this before any rate is known, and it is a statement about which quantities update together, not about how often. The calculus records it as a nominal **clock domain** and treats rate as data outside the kernel.

## Schedules and the domain judgment

The time model is one global base tick and a schedule $S : \text{ClockId} \to \mathbb{N} \to \text{Bool}$ saying at which global ticks each domain activates. A period $n$ induces the schedule $t \bmod n = 0$ (`Sched.periodic`); the schedule lives outside the design. Domain-local time is not a separate counter but the sequence of a domain's activations. The last activation of $c$ strictly before $t$ is
$$
\text{prevAct}\;S\;c\;0 = \text{none},\qquad \text{prevAct}\;S\;c\;(t{+}1) = \text{if}\;S\;c\;t\;\text{then}\;\text{some}\;t\;\text{else}\;\text{prevAct}\;S\;c\;t ,
$$
with $\text{prevAct}\;S\;c\;t = \text{some}\;t' \Rightarrow t' < t \wedge S\;c\;t'$.

Each declaration is assigned a domain by the clock environment $\mathrm{K}$, or none if it is a pure mapping usable anywhere. The clock is interface data in every sense that matters — clients' validity depends on it, it is frozen under refinement, and changing it is an edit (Table 1) — and it is stored as a projection beside the interface, as a concept's representation is stored in $\Theta$ rather than in the type.

The **domain judgment** $\text{Clocked}\;\mathrm{K}\;c\;e$, for $c : \text{Option}\;\text{ClockId}$, says that $e$ may be evaluated in domain $c$:
$$
\begin{array}{rl}
\text{Clocked}\;\mathrm{K}\;c\;(\text{declRef}\;\delta) \iff & \mathrm{K}\;\delta = \text{none} \;\vee\; \mathrm{K}\;\delta = c\\
\text{Clocked}\;\mathrm{K}\;(\text{some}\;c)\;(\text{delay}\;i\;e) \iff & \text{Clocked}\;\mathrm{K}\;(\text{some}\;c)\;i \wedge \text{Clocked}\;\mathrm{K}\;(\text{some}\;c)\;e\\
\text{Clocked}\;\mathrm{K}\;(\text{some}\;c)\;(\text{sync}\;c'\;i\;e) \iff & \text{Clocked}\;\mathrm{K}\;(\text{some}\;c)\;i \wedge \text{Clocked}\;\mathrm{K}\;(\text{some}\;c')\;e\\
\text{Clocked}\;\mathrm{K}\;\text{none}\;(\text{delay}\;i\;e) \iff & \text{False} \qquad\qquad \text{Clocked}\;\mathrm{K}\;\text{none}\;(\text{sync}\;c'\;i\;e) \iff \text{False}
\end{array}
$$
and homomorphically elsewhere. A reference stays in its domain or is agnostic; a delay needs a domain; $\text{sync}\;c'$ switches the domain of its operand. A design is well clocked when every body is clocked in its own declaration's domain. Typing is unchanged and blind to domains: the direct wire between two domains at the same value type is well typed and rejected only by $\text{Clocked}$. Placing the domain in the type instead was tried and set aside: every pure mapping would then need clock polymorphism (`clocked_type_forces_polymorphism`), and nothing the type rejects is missed by the judgment.

## Multi-domain evaluation

The judgment $\rho \vdash^{c}_{t} e \Downarrow v$ — in domain $c$ at global tick $t$, with $S$, $\Delta$, $I$ ambient — is $\text{Ev}$ with the two temporal rules replaced by four (`MEv`):
$$
\frac{\text{prevAct}\;S\;c\;t = \text{none} \quad \rho \vdash^{c}_{t} i \Downarrow v}{\rho \vdash^{c}_{t} \text{delay}\;i\;e \Downarrow v}
\qquad
\frac{\text{prevAct}\;S\;c\;t = \text{some}\;t' \quad \rho \vdash^{c}_{t'} e \Downarrow v}{\rho \vdash^{c}_{t} \text{delay}\;i\;e \Downarrow v}
$$
$$
\frac{\text{prevAct}\;S\;c'\;t = \text{none} \quad \rho \vdash^{c}_{t} i \Downarrow v}{\rho \vdash^{c}_{t} \text{sync}\;c'\;i\;e \Downarrow v}
\qquad
\frac{\text{prevAct}\;S\;c'\;t = \text{some}\;t' \quad \rho \vdash^{c'}_{t'} e \Downarrow v}{\rho \vdash^{c}_{t} \text{sync}\;c'\;i\;e \Downarrow v}
$$
$\text{delay}$ reads the previous activation of the current domain; $\text{sync}\;c'$ reads the previous activation of $c'$ and evaluates its operand *there*, in $c'$. All other rules carry $c$ unchanged.

**Theorem 16 (Memory is transport at the own domain; `delay_is_sync_own`, `clocked_delay_iff_sync_own`).** $\rho \vdash^{c}_{t} \text{delay}\;i\;e \Downarrow v$ iff $\rho \vdash^{c}_{t} \text{sync}\;c\;i\;e \Downarrow v$, and $\text{delay}\;i\;e$ is clocked in $c$ iff $\text{sync}\;c\;i\;e$ is.

The kernel therefore has one temporal primitive — read a domain at its previous activation — and $\text{delay}$ is notation for its diagonal. A $\text{delay}$ in a slow domain reads three global ticks back where a $\text{delay}$ in a fast one reads one, with the same syntax.

**Theorem 17 (Single-domain embedding; `single_domain_embedding`).** Under the always-active schedule, $\rho \vdash^{c}_{t} e \Downarrow v$ iff $\rho \vdash_t e \Downarrow v$, for every $c$.

The results of §6 are thus the one-domain special case of this section rather than a replaced machine.

**Theorem 18 (Determinism; `MEv.det`).** Multi-domain evaluation is a partial function, for every schedule.

**Theorem 19 (Totality in every domain; `mfundamental`, `multi_domain_total`).** In a causal, globally well formed design with inputs well typed in every domain, every declared identity has a value in every domain at every tick, related to its expected type.

The proof reuses the logical relation of §6.3 with the application relation $\text{MApply}\;S\;\Delta\;I\;c\;t$, and the same lexicographic induction: a transport at $t$ evaluates its operand at $t' < t$ under any rank. Causality is the *same* $\text{Causal}\;\Delta$: a transport's operand is never instantaneous, so no cross-domain cycle can be. An interpreter $\text{mevalF}$ is proved sound (`mevalF_sound`). Tag provenance holds across domains (`MEv.tag_provenance`): transport changes timing, not identity, and a crossing from `Tilt@fast` to `Tilt@slow` authorizes neither `Tilt -> MotorAngle` nor $\text{q}\;\text{Length} \to \text{q}\;\text{Time}$, by the typing rule.

## Strictly before, and what the alternative exposes

A transport sees only source activations strictly before the destination tick. That is a choice with an observable alternative, and the alternative was built.

**Theorem 20 (Same-tick visibility exposes the scheduler; `scheduling_order_observable`).** Let $\text{MEv}_{\le}$ be the semantics in which a transport may also see a simultaneously active source, resolved by a priority between domains. There is a two-domain design, a schedule and an input such that two priorities give two different values to the same declaration at the same tick.

At tick 1 both domains are active for the first time; with the source first the transport delivers the source's current value, with the destination first it delivers the initial value. The strictly-before rule has no such parameter, and Theorem 18 has no order between simultaneously active domains in its statement. Every crossing costs one destination-visible step; "synchronous sub-domains evaluated in one instant" are, in this model, the same domain.

Rate and identity are distinct. A clone of a domain with the identical schedule is a different domain, and a direct wire between them is rejected (`equal_rate_not_same_domain`); a domain at the same rate but shifted in phase reads different values through a transport. Rate changes are validation-only: they change the induced schedule and the observed values, but no client's well-formedness. This is where the calculus departs from synchronous languages that recover clocks by inference [@colaco2003clocks; @biernacki2008clock]: the domain is authored, because the information needed to infer it — the realization binding — arrives at the point where a designer is least able to make the decision.

## Occurrences across domains: the window buffer

Within one domain an occurrence is a stream of optional type. Across domains this fails: $\text{sync}$ is a zero-order hold, so a slow consumer of a fast event source sees the last value only. Two fast events at ticks 1 and 2 and one event at tick 2 are indistinguishable at the slow activation at tick 3, and a single event at tick 1 followed by a quiet fast tick is dropped outright (`opt_loses_multiplicity_under_sync`). The counterexample is against $\text{sync}$ as an *event transport*, not against optional types; it says that multiplicity and order are observable across domains and that keeping them requires buffering.

What the destination should see is the source's activations since the destination's own previous activation — the *window*, $\text{windowTicks}\;S\;\mathit{src}\;\mathit{dst}\;t$, the source ticks in $[\text{prevAct}\;S\;\mathit{dst}\;t,\ t)$. The window equals the source's accumulated log read at the current tick minus its length at the previous destination activation (`buffer_from_log_and_cursor`): two single-instant reads, a $\text{sync}$ of a source-side accumulator and a $\text{delay}$ of a cursor. With list data this is five ordinary declarations:
```
log     @src :  cons src (delay nil log)             -- source-side accumulator
logD    @dst :  sync src nil log                     -- the log, transported
seen    @dst :  length logD                          -- log length now
cursor  @dst :  delay 0 seen                         -- log length at the previous activation
window  @dst :  reverse (take (seen - cursor) logD)  -- the new entries, oldest first
```

**Theorem 21 (The window is computed; `buffer_window_correspondence`).** For every schedule, input, destination domain and tick, if the five declarations are realized as above and $\mathit{src}$ is an input, then $[\,] \vdash^{\mathit{dst}}_{t} \text{window} \Downarrow \text{list}\,(\text{map}\,(I\,\mathit{src})\,(\text{windowTicks}\;S\;\mathit{src}\;\mathit{dst}\;t))$.

The elaboration is well typed and well clocked (`buffer_elaboration_well_typed`, `buffer_elaboration_well_clocked`); the list is injective on windows, ordered by tick, and multiplicity-preserving for every predicate (`buffer_lossless`, `window_to_list_preserves_order`, `window_to_list_preserves_multiplicity`). The general negative result is that any summary depending only on the newest $k$ entries, for any fixed $k$, identifies a $k$-entry window with a $(k{+}1)$-entry window (`bounded_summary_not_lossless`); a lossless summary is injective and therefore unbounded (`lossless_iff_injective`). Capacity is thus a deployment obligation on the schedule — for periodic schedules one destination period of source activations suffices (`periodic_capacity_sufficient`) — and the only overflow policy that preserves the semantics is to reject the deployment; dropping is a semantic change (`bounded_buffer_agrees`, `negE`).

The point for the calculus is what was *not* added: no event type, no buffer primitive, no scheduler order, no same-tick visibility, no implicit overflow rule. An event stream is a data-typed declaration in a domain; an occurrence is its value at an activation; a lossless view of it across domains is the five declarations; `latest`, `count`, `coalesce` are ordinary computations over `window`.

# Data, the recursor and polymorphism

The kernel of §3–7 computes with booleans, counts, quantities, concepts and optional values and abstracts with lambdas over them. A product needs more: a mode tested against a finite set of modes, every reading below a threshold, a pair of readings, a calibration mapped over a collection. This section records the smallest typed data basis that supports them, what could not be derived and why, and how polymorphism is provided without a type variable in the kernel.

## The list recursor

$\text{fold}\;f\;z\;l$ is a *term former*, not a registered operator. The kernel has no recursion, deliberately; a total language needs an eliminator for its inductive data, and $\text{fold}$ is the one construct that applies a function value in the course of evaluation. Registered operators never apply closures. The alternative of one primitive per collection operation was rejected because a primitive cannot apply a closure and each would need its own evaluation rule; the alternative of bounded unrolling was rejected because lists — the cross-domain window — are unbounded.

**Theorem 22 (The recursor is total; `fold_total`, `mfold_total`).** If $v_f$ is related at $\tau \to \sigma \to \sigma$, $v_z$ at $\sigma$ and every element of $\vec{w}$ at $\tau$, then $[\text{list}\,\vec{w}, v_z, v_f] \vdash_t \text{fold}\;\#2\;\#1\;\#0 \Downarrow r$ for some $r$ related at $\sigma$.

The proof is an induction on the list, separate from the fundamental theorem, which invokes it in its $\text{fold}$ case. Every collection operation — `map`, `filter`, `any`, `all`, `contains`, `append`, `sum`, `zip`, and through $\text{toList}$ the option eliminators — is a definition over $\text{fold}$, and each is proved to compute the mathematical function it names through one general lemma: the recursor computes $\text{List.foldr}\;g$ whenever the step closure implements $g$ on the reachable accumulators (`fold_spec`; then `any_spec`, `all_spec`, `map_spec`, `filter_spec`, `min_spec`, `clamp_spec`, …). Finite quantification is a fold — $\forall x \in \mathit{xs}.\,P\,x$ iff `all xs P` evaluates to true (`forall_in_list`, `exists_in_list`) — and a finite-set literal means membership with duplicates irrelevant (`oneOf_mem`, `oneOf_dup_irrelevant`), so there is no `Set` type and no uniqueness convention.

## Products, and why not Church pairs

$\tau \times \sigma$ with $\text{pair}$, $\text{fst}$, $\text{snd}$ entered the kernel after the Church encoding was tried and refuted twice. A Church pair is an arrow, and arrows are not data: nothing of function type can be delayed or transported (`arrow_not_delayable`), so paired *state* — a delayed reading with its timestamp — needs a data product. And a Church pair used as a first-class value needs rank-2 types: in a toy System F with a rank measure, the type of $\text{fst}$ on Church pairs has rank 2 (`church_fst_rank`), and in the prenex fragment a pair instantiated at one result type serves only one projection (`church_pair_prenex_one_projection`). Products are value composition only; they are never a component interface or an output bundle (§10 shows what a tuple-returning declaration does to the dependency graph).

## Equality with its evidence in the syntax

$\text{eq}_\tau^{h}$ is structural equality at every data type — booleans, numbers, $\text{none}$/$\text{some}$, pairs and lists componentwise, concept values by tag and representation — with the proof $h : \tau.\text{Data}$ carried *in the syntax*. This is the kernel's only capability evidence: an equality on a function type is unwritable rather than ill typed, which keeps T-Prim unconditional. On first-order values structural equality is equality (`Value.beq_iff`, by a mutual induction over the nested value type).

Order is deliberately not generalized. A first formulation gave `<` a structural meaning at every data type — booleans, options, pairs and lists lexicographically — and it was formally consistent. An audit rejected it on the grounds that no such order has a design meaning: `mode1 < mode2` would order modes by a constructor tag, `None < Some x` is an artifact. The structural order was deleted and $\text{lt}_d$ restored to quantities only. So $\text{Data} \Rightarrow \text{Eq}$ holds (`Cap.eq_iff_data`) but $\text{Eq} \not\Rightarrow \text{Ord}$; order on a *concept* is a surface capability — a concept the designer declared ordered and represented by a quantity compares as $\text{lt}_d$ on $\text{rep}$, a term the kernel already admits (`lt_only_on_quantities`, `lt_rejected`, `min_mode_rejected`). Enumerations follow the same rule: equality is natural, declaration order is never silently behavioral order.

## Rank-1 polymorphism by families

Five models of polymorphism were compared: a monomorphic kernel; per-type duplication; rank-1 parametric polymorphism; System F; higher rank. The one adopted is rank-1 *as definitional families*: every library entry is a function $\text{Ty} \to \text{Expr}$ (or $\text{Dim} \to \text{Expr}$) in the metalanguage, and a scheme is a pattern over type and dimension variables with capability constraints. The kernel sees only the instances (`instances_are_monomorphic`: three uses of `min` are three kernel terms), and T-Prim, T-App and Theorem 1 are unchanged.

Why this needs no kernel support: a use site always has *closed* argument types. Every declaration's expected type is frozen and closed, and inference is bottom-up, so finding the instance of a scheme is one-way *matching* of the scheme's pattern against closed types — decidable, returning the unique substitution on the pattern's variables (`matchTy_sound`, `matchTy_complete`). There is no unification of two open types, no let-generalization inside expressions [@damas1982principal], and no principal-type search; those problems arise when a definition's type is inferred from its body, and every definition here carries its signature. The situation is that of local type inference [@pierce2000local] with no bidirectionality needed. Capability constraints are checked after matching (`Scheme.instantiate_sound`), and the two failure points have designer-level explanations: *no instance* and *capability failed*. System F was rejected by measuring what it would add — the prenex fragment *is* instantiation of families — and every candidate higher-rank use has a rank-1 replacement (`applyBoth_rank`, `applyBoth_replacement`). Dimension polymorphism (`sum : list (q d) → q d`) uses the same mechanism with dimension pattern variables; no kind system, because the dimension algebra already lives in the operator table.

Nominality survives all of it. *Any* family typed at $\alpha \to \alpha \to \alpha$, instantiated at concept $s$, rejects an argument of concept $s' \neq s$, the representations never consulted (`generic_preserves_identity`); the same for $\text{q}\;d$ versus $\text{q}\;d'$ (`generic_preserves_dimension`). This is Reynolds's abstraction [@reynolds1983types] and Wadler's free theorems [@wadler1989free] at the level of syntax: a family cannot inspect what it is instantiated at, because it is instantiated by substitution into a closed term.

## The library as combinators, and inlining

Every library entry is a **combinator**: variables, literals, lambdas, applications, registered operators, the recursor and $\text{rep}$ — no reference, no state, no transport, no $\text{mk}$. For combinators four facts are proved once and combine into an inlining statement (`lib_expansion`): typing is independent of the design and the grant and reads $\Theta$ only through write-once bindings (`HasType.comb_irrelevant`); the value is the same in every design at every tick under every input (`lib_eval_context_free`, from `Ev.pure`); the term is clocked in every domain (`lib_clocked`); nothing is constructed (`Comb.noConstruct`). This is what lets an implementation inline an equation at each use without creating a declaration — a library entry as a declaration would be monomorphic and would enter the dependency graph.

The expressiveness ceiling, stated once: total first-order-data computation over booleans, quantities, concepts, options, lists and pairs, with higher-order functions and one list recursor; generic definitions instantiated at closed types; no general recursion, no type abstraction in terms, no sums (an enumeration with a payload is encoded as a tag paired with an optional payload, and a kernel sum would cost one more eliminator term former exactly like $\text{fold}$), no unbounded quantification. This is a design conclusion backed by executed cases and the proved library; it is not a minimality theorem.

# Physical outputs

A declaration computes a value; it does not move hardware. Physical effect happens only through an explicit **drive edge** from a declaration to a nominally identified **output** — a logical actuator channel, a resource in a different sort from both concepts and declarations: "the desired steering angle" is a value, "the steering motor" is a resource.

- $\Omega : \text{OutputId} \to \text{Option}\;\langle \mathit{accepts}, \mathit{clock}\rangle$ — each output's accepted type and domain;
- $\beta : \text{DeclId} \to \text{Option}\;\text{OutputId}$ — the drive edges, a write-once per-declaration projection of the same shape as $\mathrm{K}$;
- $\text{DriveWF}\;\Omega\;\mathrm{K}\;\Delta\;\beta := \forall \delta\,o.\;\beta\;\delta = \text{some}\;o \to \exists \mathit{spec}.\;\Omega\;o = \text{some}\;\mathit{spec} \wedge \Delta^{\mathrm{ty}}(\delta) = \text{some}\;\mathit{spec}.\mathit{accepts} \wedge \mathrm{K}\;\delta = \text{some}\;\mathit{spec}.\mathit{clock}$;
- $\text{SingleDriver}\;\beta := \forall \delta_1\,\delta_2\,o.\;\beta\;\delta_1 = \text{some}\;o \to \beta\;\delta_2 = \text{some}\;o \to \delta_1 = \delta_2$;
- $\text{CompleteOutputs}\;\beta\;\mathit{req}$ — every required output is driven.

Nothing was added to types, typing, the domain judgment, evaluation or the grant. The edge neither coerces nor converts nor synchronizes: the driver's type *equals* the accepted type and its domain *is* the output's. A declaration typed `Tilt` cannot drive a `MotorAngle` output; an output that accepts a representation type needs an explicit $\text{rep}$-typed declaration in front of it; a slow driver reading a fast value must $\text{sync}$ it upstream. A driver of a concept-accepting output is necessarily a value, not a function (`driver_is_unit_domain`).

**Definition.** $\text{PhysicalOutput}\;S\;\Delta\;I\;\Omega\;\beta\;o\;t\;v := \exists \delta\,\mathit{spec}.\;\beta\;\delta = \text{some}\;o \wedge \Omega\;o = \text{some}\;\mathit{spec} \wedge [\,] \vdash^{\mathit{spec}.\mathit{clock}}_{t} \text{declRef}\;\delta \Downarrow v$.

**Theorem 23 (One driver, one output; `single_driver_output_deterministic`, `multiple_direct_drivers_rejected`).** Under $\text{SingleDriver}\;\beta$, $\text{PhysicalOutput}$ is a partial function of $o$ and $t$. Two declarations driving one output — each well typed, well clocked, causal and individually well formed — violate $\text{SingleDriver}$ and nothing else, and there is a tick at which the output receives two values.

The principle is *many contributors, one explicit final driver*. Contributors are dependencies: `base + corr -> final -> motor` passes every check; priority is a conditional in the single driver; blend, maximum and clamp are ordinary declarations of the target type. Why arbitration must be explicit is shown rather than argued: first-wins, last-wins and maximum over the same value graph give three different physical outputs (`hidden_arbitration_observable`). Binding an unbound declaration to an undriven output is a refinement and preserves $\text{SingleDriver}$ (`first_output_binding_is_monotone`); binding to a driven output is invalid; retargeting, renaming or detaching an edge invalidates an unchanged design.

Two alternatives were formalized in toy form. Direct effect rows — the set of outputs a declaration drives — are exactly the drive edges, and single-driver is exactly their pairwise disjointness; propagated rows flag a valid design in which a display reads the driver; action values move the conflict into the collector that consumes them, which must then be a policy, which is the single driver by another name. None of this bears on richer effect systems [@plotkin2013handlers]; it says these formulations add no rejection the single-driver rule lacks.

Finally, the dual form. Once zero-input relationships have the canonical interface type `() -> A` (normalized above the kernel to `A`, with the unit eliminated before any term is typed — the kernel has no unit type, and `delay` inside a zero-input declaration is why: a unit binder would forbid memory there, `delay_not_under_binder`), the form `A -> ()` suggests itself as a consumer. It cannot name one: in a pure total language every function into the one-point type is the same function (`unit_codomain_collapse`, by function extensionality), so two "consumers" are indistinguishable (`consumers_indistinguishable`), and the evaluation relation has no effect component (`eval_independent_of_drives`). Naming a receiver needs an output semantics, and the calculus already has exactly one.

# Composition by renaming

A second lamp should reuse the first's behavior without copying it. This needs a component with a promised interface, instantiated with fresh identity and bound to other behaviors. The section's result is that all of it is derivable from what §4 provides — realization plus renaming — and that the flattened system is checked by the unchanged judgments.

## Equivariance

A renaming $r$ bundles four maps — on declaration, semantic, clock and output identities. Renaming acts on types (through $\text{sem}$), on terms, on interfaces, on declarations and pointwise on environments; $\Delta.\text{RenamedBy}\;r\;\Delta'$ says $\Delta'$ stores the renamed declaration of $\Delta$ at the renamed identity.

**Theorem 24 (Equivariance; `HasType.rename`, `Satisfies.rename`, `Clocked.rename`).** If $\Theta;\Delta;G;\Gamma \vdash e : \tau$ and $\Theta', \Delta', G'$ are the images of $\Theta, \Delta, G$ under $r$ (agreement on the image, with no injectivity required), then $\Theta';\Delta';G';\Gamma^{r} \vdash e^{r} : \tau^{r}$; likewise for satisfaction, and for the domain judgment under a clock environment that agrees on the declared identities.

Evidence must be equivariant as well (`Evidence.Equivariant`), an abstract condition beside monotonicity. Nothing else is new in the composition theory; the rest is definitions over Theorem 24 and §4.

## Components, instances and flattening

A **port** is a template declaration by local identity with the public part of its interface and its parameter clock. A **behavior interface** has required ports (unresolved declarations a composer binds), provided ports, elaboration-time parameters (unresolved data-typed declarations bound to closed constants at instantiation) and clock parameters. A **component** is an interface, a template design over local identities below a width $W$, and a partition of its concepts and outputs into private (freshened per instance) and shared. $\text{Realizes}\;\mathit{ev}\;C$ is a predicate over the existing judgments: the template is a well-formed design (`Design.WF`: $\text{GlobalWF}$, $\Theta.\text{WF}$, well clocked, causal, $\text{DriveWF}$, $\text{SingleDriver}$), every required port is an unresolved declaration of the stated interface, every provided port is declared with it, parameters are unresolved, data-typed and clock-free.

Instance $k$ of a component maps local identity $n$ to $\text{fresh}\;W\;k\;n = W\cdot(k{+}1) + n$, with $\text{decode}$ its inverse; distinct instances never share an identity (`inst_decl_disjoint`). The encoding is a device — any injective allocator would do. A **binding** realizes a destination port of one instance from a source — a port of another instance or a closed constant — with an optional transport: none for a direct reference in the same or an agnostic domain, $\text{some}\;\mathit{init}$ for $\text{sync}$ from the source's domain. A **system** is a width, a list of instances, a list of bindings, the shared concept environment and the external outputs. **Flattening** is the union of the renamed instances followed by the bindings applied as §4 realization steps: the destination port is realized as $\text{declRef}\;\mathit{src}$ or $\text{sync}\;c\;\mathit{init}\;(\text{declRef}\;\mathit{src})$. The result is a design, consumed by every existing judgment unchanged.

**Theorem 25 (Flattening is well formed; `binding_satisfies`, `flatten_WF`, `flatten_causal`, `flatten_wellClocked`, `flatten_singleDriver`, `open_port_stays_open`).** Under $\text{ComposeWF}$ — every instance realizes its interface; every binding is well formed (types agree; a direct binding's source is in the destination's domain or agnostic; a transported binding's source has a domain); external outputs are driven by at most one instance — and with evidence that is monotone, equivariant and port-sound (a discharged commitment survives when a port copy is realized by a reference to a declaration of the same interface), the flattening is globally well formed, well clocked, single-driver, causal when the inter-instance graph is acyclic, and its open ports remain open.

**Theorem 26 (Modular semantics, restricted; `eval_flat_to_inst`, `eval_inst_to_flat`, `modular_iff_flat`).** For wiring designs with closure-free inputs and direct bindings, in one domain, the value of a declaration in an instance evaluated alone with a consistent modular input equals its value in the flattened system.

The restriction is exact and recorded: transported bindings under $\text{MEv}$ need a domain-indexed input for the transported port, and higher-order bodies are not covered — the same obstacle in both directions. Substitutability follows the usual contravariance: $B$ may replace $A$ when every port $A$ provides, $B$ provides at the same type and clock, and every port $B$ requires, $A$ required; replacing an instance by a refining component preserves $\text{ComposeWF}$ (`substitute_composeWF`).

The counterexamples that fixed the design (`Experiments/BehaviorAlternatives.lean`): a name-based identity collides on double instantiation; a shared clock captured inside a template cannot be re-bound; a binding across domains without transport is rejected by $\text{Clocked}$; two instances driving one external output violate $\text{SingleDriver}$.

## Groups are the identity, and extraction is a system

A *group* — a designer's selection of several declarations — is authoring metadata: a group identity and a member list beside the design. Every group operation acts on the list and leaves the design untouched, so every kernel judgment of the design is the *same proposition* before and after, each proved by reflexivity (`group_is_identity_on_design`). A group's boundary is a projection over a finite enumeration: the non-members some member depends on ($\text{crossIn}$), the members some non-member depends on ($\text{crossOut}$); the aggregate socket a collapsed group shows is these lists, none of which is a declaration, and $a \in \text{crossIn}$ says *some* member depends on $a$ and nothing about the others (`socket_no_fanout`). Two encodings of a socket as a declaration were refuted: as a declaration every member reads, a member acquires an instantaneous dependency it never had; as a tuple-returning declaration, the consumer of one member comes to depend on the inputs of all of them. The kernel has no tuples for boundaries, and this is a reason not to add them for that purpose.

Packaging a group as a component — the one semantic step in the hierarchy declaration → group → component → system — builds two *restrictions* of the design, the component with an unresolved copy of each crossing-in declaration as a required port and the residual with an unresolved copy of each crossing-out member, and forms a two-instance system with one direct binding per crossing. No body is translated or copied across the boundary. Both templates realize their inferred interfaces (`restrict_realizes`, needing evidence that depends only on the interfaces of the referenced declarations, `Evidence.InterfaceLocal`); the system is a well-formed composition and its flattening a well-formed design (`system_composeWF`, `flat_WF`); causality needed its own argument, since a group with both inputs and outputs is never inter-instance-acyclic, yet the flattened instantaneous graph is the original with every crossing edge subdivided through a port copy, and doubling the original rank witnesses it (`flat_causal`); private members are unobservable from the residual (`private_unobservable`); and for wiring designs an original declaration and its home copy evaluate to the same value at every tick (`orig_iff_flat`).

# Mechanization

The development is 68 Lean 4 modules (Lean 4.33.1, no dependencies beyond core): 11 in `Core` (the calculus of §3–7 and §9), 12 in `Behavior` (§10), 19 in `Surface` (the definitional library, polymorphism, units, buffering and the boundary constructions above the kernel), 2 in `Validation` (hardware and capacity, outside this paper), and 24 experiment modules holding alternatives, counterexamples and executed examples; about 26 500 lines and 1 545 theorem declarations. It builds with no `sorry`. The axioms are propositional extensionality and quotient soundness, the latter only through function extensionality and the choice-free rational quotient used by the unit laws; classical choice is absent, and the whole development was re-audited for it at every phase.

Three proof-engineering choices carried the metatheory.

*One inductive relation.* $\text{Ev}$ and $\text{MEv}$ are ordinary inductive relations with no mutual recursion and no fixpoint, because the recursor's rule unrolls through the environment (§6.1). Every induction on evaluation — determinism, provenance, closure-freeness, environment irrelevance, unfolding — extends by one case when a construct is added; the transport primitive and the recursor entered this way, and every earlier theorem was re-established without a change of statement.

*One logical relation, generic in application.* $\mathcal{R}$ is parameterized by an application relation so that the single- and multi-domain semantics share it; at data types it is independent of that parameter (`Red_data`), which is the fact that lets a value cross a tick. The lexicographic induction on (tick, rank, derivation) is written once, in `fundamental`, and once more in `mfundamental` with $\text{prevAct}$ in place of the predecessor.

*Counterexamples as theorems, traces by a proved interpreter.* Every rejected alternative is a theorem whose content is a rejection, stated on a concrete design and discharged by `decide` or by running $\text{evalF}$/$\text{mevalF}$ (proved sound for the relations) inside the checker. There is no test suite beside the proofs; the executed examples are part of the same `lake build`. Several results are recorded as trivial by definition — the typing half of client stability, the well-formedness of a refinement target — and are reported as such rather than presented as content.

Extraction to an implementation is not part of the development. The production toolchain implements the calculus in Rust and is tested differentially against the traces the interpreter computes; that correspondence is a tested claim, not a theorem, and is recorded as such in the monograph.

# Related work

*Synchronous languages.* $\lambda_{\mathrm{BDL}}$'s time model is that of Lustre [@halbwachs1991lustre] and Esterel [@berry1992esterel]: a global logical tick, streams as the meaning of declarations, memory as `pre` with an explicit initial value, causality as acyclicity of instantaneous dependencies. Two departures are deliberate. Clocks are nominal and authored, not inferred [@colaco2003clocks; @biernacki2008clock; @caspi1996kahn], because the information that would let a clock be inferred arrives at realization binding, after the design has been reasoned about; and a cross-clock read is a single primitive with a strictly-before rule and an explicit initial value, so that no simultaneously active domains ever see each other and no `when`/`merge` calculus of sub-sampling is needed — sub-domains evaluated in one instant are the same domain here. The window buffer of §7.5 plays the role that sampling operators play in Lucid Synchrone. Vélus [@bourke2017velus] verifies a Lustre compiler; the present development verifies a calculus and its metatheory, and leaves the compiler to differential testing. Zélus [@bourke2013zelus] and state-machine extensions [@colaco2005state] address continuous time and modes, neither of which the calculus has.

*Functional reactive programming.* FRP [@elliott1997fran; @nilsson2002frp; @cooper2006frtime] makes signals first-class values. The calculus has no signal type: every declaration is a stream by interpretation, and a signal type would reject nothing (§6.7). Typed FRP with modal or temporal types [@krishnaswami2013frp; @jeffrey2012ltl; @cave2014fair] uses the type to control what may be remembered; here that control is the data restriction on $\text{delay}$ and the empty-context restriction, both forced by the totality proof, and the guarantee is totality rather than the absence of space leaks.

*Logical relations.* The totality proof is a step-indexed logical relation [@appel2001indexed; @ahmed2006stepindexed] in which the index is the tick and a rank on declarations is a second index; the arrow clause is tick-indexed and the data clauses are not, which is what makes memory sound. Kripke-style monotonicity conditions on a world are standard in such proofs; the evidence-monotonicity condition of §4.3 is the same shape imposed on a *validation layer* rather than on a store.

*Modules, abstract types and nominal types.* Persistent declarations are the interface/implementation separation of module signatures [@leroy1994manifest; @harper1994modules] with a growable commitment set whose growth is a first-class operation on a declared-but-undefined name. The grant is the private constructor of an abstract type [@mitchell1988abstract; @reynolds1983types] with the capability derived from the signature. Nominal type identity is the ordinary mechanism of a nominal type system [@pierce2002tapl]; the contribution is the pair of erasure and provenance theorems and the refuted alternatives, not the mechanism.

*Units of measure.* Kennedy's dimension types [@kennedy1997units; @kennedy2010units] put dimension polymorphism in the type system. The calculus keeps dimensions monomorphic in operator types and provides dimension polymorphism only in surface families instantiated by matching (§8.4), with units entirely outside the kernel.

*Typed holes and live programming.* Hazelnut [@omar2017hazelnut; @omar2019live] gives a semantics to programs with holes and edits. An unresolved declaration is not a hole position in a term but a declaration whose realization is absent, referred to by identity and typed by its interface; the refinement order plays the role of the edit action calculus, restricted to the operations under which clients are stable.

*Effects.* The single-driver discipline is not an effect system [@plotkin2013handlers]; §9 records that effect rows and action values, in the toy forms tried, add no rejection the drive edge lacks. Statecharts [@harel1987statecharts] and model-based design tools supply modes and hierarchy that the calculus encodes as ordinary declarations.

*Expressiveness.* The negative results of §7.5 and §8 are statements about what a construct can and cannot express relative to the kernel — in Felleisen's sense [@felleisen1990expressive] of whether a construct is definable by a local translation — with the difference that each is a mechanized theorem about a specific candidate rather than a general expressiveness result.

# Limitations and open problems

The paper's claims are bounded by the following, each recorded in the development.

- *Causality is conservative for lambda-guarded cycles.* `A := λx. A x` is rejected by $\text{Causal}$ although `declRef A` evaluates to a closure; Theorem 11 covers strict cycles only. A finer criterion that admits productive higher-order cycles has not been formulated.
- *Modular semantics is proved for a fragment.* Theorem 26 holds for single-domain wiring designs with direct or constant bindings. Transported bindings under $\text{MEv}$ need a domain-indexed modular input; higher-order bodies need a relation between closures across the two evaluations. Both are open.
- *Evidence is abstract.* The kernel imposes monotonicity, equivariance and port-soundness on the validation layer's evidence and proves nothing about a concrete discharge mechanism; a compositional evidence model that discharges these once is future work.
- *No sums.* Enumerations with payloads are encoded; a kernel sum would be one eliminator term former, and its absence is a decision to stop where the executed cases stopped.
- *Magnitudes are naturals.* The executable kernel's quantities are natural numbers, so its unit registry is exact only for integer scales; the unit laws are proved over an abstract scalar domain instantiated symbolically, and floating-point implementations are held to toleranced versions above the kernel.
- *No minimality theorem.* "Minimal" means minimal among the formalized candidates; several alternatives (flow-sensitive semantic analyses, structural typing with a separate role judgment) were argued against rather than refuted.
- *Nothing about designers.* The calculus was shaped by requirements from a design workflow; whether it serves designers is an empirical question no theorem addresses.

# Conclusion

$\lambda_{\mathrm{BDL}}$ is a small calculus whose content is in its environments and the disciplines they impose rather than in its terms: a declaration environment read by typing through the type view and by evaluation through the realization view, with a refinement order under which clients are stable; a concept environment read through write-once bindings, with a grant derived from the signature under which construction is authorized; a clock environment read by a judgment that typing never sees; and an output environment read by a drive discipline with a single driver. One temporal primitive gives memory and transport, and a tick-indexed logical relation gives totality on causal designs in one domain and in many. The negative results — a scheduler made observable by same-tick visibility, an evidence relation destroyed by a valid realization, a hidden concept crossing admitted by unrestricted construction, three physical outputs from one design under hidden arbitration, a lossy summary for every bounded buffer — are mechanized alongside the positive ones and are, we think, as much a part of the calculus's specification as the rules.

# Appendix A — Theorem index {-}

Every name is a Lean declaration in `KCN-judu/BDL_FV`; the file is given per group, and names are unqualified where the namespace is `BDL`.

```{=typst}
#block(width: 100%)[
#set text(size: 8pt)
#table(
  columns: (0.55fr, 2.6fr, 1.75fr), align: left, inset: (x: 3pt, y: 2.6pt),
  stroke: (x: none, y: 0.3pt),
  table.header([*paper*], [*Lean name*], [*file*]),
  [Thm 1], [`infer_sound`, `infer_complete`, `HasType.unique`], [`Core/Typing`],
  [Thm 2], [`HasType.mono_env`, `HasType.mono_concept`, `HasType.mono_grant`], [`Core/Typing`],
  [§4.1], [`InterfaceRefines_iff_semantic`, `naive_breaks_wellformedness`], [`Core/Satisfaction`, `Experiments/DeclCounterexamples`],
  [Thm 3], [`DeclRefinesStar_iff`, `EnvRefines_update`], [`Core/Satisfaction`, `Core/Decl`],
  [Thm 4], [`local_refinement_preserves_global_typing`], [`Core/Env`],
  [Thm 5], [`local_refinement_preserves_global_wf`, `local_lifecycle_preserves_global_wf`], [`Core/Env`],
  [Prop 6], [`badEv_not_mono`, `probe6_breaks`], [`Experiments/DeclCounterexamples`],
  [Thm 7], [`Unfolds.det`, `Unfolds.exists_of_acyclic`, `Unfolds.not_of_cyclic`, `Unfolds.refFree_of_fullyRealized`], [`Core/Dependency`],
  [Thm 8], [`HasType.constructs_granted`, `hidden_crossing_rejected_under_grant`], [`Core/Typing`, `Experiments/RepresentationBindingAlternatives`],
  [Thm 9], [`HasType.erase`, `erase_not_injective`, `baseline_is_erased_modelA`], [`Experiments/SemanticTypeAlternatives`],
  [§5.3], [`dimension_mismatch_rejected`, `counterexampleB_baseline_accepts_length_plus_time`, `same_dimension_does_not_imply_same_semantic_identity`], [`Experiments/DimensionAlternatives`],
  [Thm 10], [`Ev.det`, `evalF_sound`], [`Core/Reactive`],
  [Thm 11], [`Ev.not_of_strictCyclic`, `Causal_iff_acyclic_of_delayFree`], [`Core/Reactive`, `Core/Dependency`],
  [Thm 12], [`fundamental`, `Red_data`, `Red_prim`], [`Core/Reactive`],
  [Thm 13], [`reactive_total`, `Ev.red`], [`Core/Reactive`],
  [§6.4], [`arrow_not_delayable`, `delay_not_under_binder`, `sync_not_under_binder`, `first_tick_undefined_without_init`], [`Experiments/PolyAlternatives`, `Surface/UnitDomain`, `Experiments/ReactiveAlternatives`],
  [Thm 14], [`Ev.tag_provenance`, `temporal_state_preserves_semantic_identity`], [`Core/Reactive`],
  [Thm 15], [`unfolds_preserves_eval`, `Ev.pure`, `Ev.env_irrelevant`], [`Core/Reactive`],
  [Thm 16], [`delay_is_sync_own`, `clocked_delay_iff_sync_own`], [`Core/Clock`],
  [Thm 17], [`single_domain_embedding`], [`Core/Clock`],
  [Thm 18], [`MEv.det`, `mevalF_sound`], [`Core/Clock`],
  [Thm 19], [`mfundamental`, `multi_domain_total`, `MEv.tag_provenance`], [`Core/Clock`],
  [Thm 20], [`scheduling_order_observable`, `equal_rate_not_same_domain`, `clocked_type_forces_polymorphism`], [`Experiments/ClockAlternatives`],
  [Thm 21], [`buffer_window_correspondence`, `buffer_from_log_and_cursor`, `bounded_summary_not_lossless`, `lossless_iff_injective`], [`Surface/Buffer`, `Core/Clock`, `Experiments/BufferAlternatives`],
  [Thm 22], [`fold_total`, `mfold_total`, `fold_spec`], [`Core/Reactive`, `Core/Clock`, `Surface/Stdlib`],
  [§8.2–8.3], [`church_fst_rank`, `church_pair_prenex_one_projection`, `Value.beq_iff`, `Cap.eq_iff_data`, `lt_only_on_quantities`], [`Experiments/PolyAlternatives`, `Surface/Generic`, `Surface/Poly`, `Experiments/EquationExamples`],
  [§8.4–8.5], [`matchTy_sound`, `matchTy_complete`, `Scheme.instantiate_sound`, `generic_preserves_identity`, `lib_expansion`], [`Surface/Poly`, `Surface/Generic`, `Surface/Stdlib`],
  [Thm 23], [`single_driver_output_deterministic`, `multiple_direct_drivers_rejected`, `hidden_arbitration_observable`, `first_output_binding_is_monotone`], [`Core/Output`, `Experiments/OutputAlternatives`],
  [§9], [`driver_is_unit_domain`, `unit_codomain_collapse`, `consumers_indistinguishable`, `eval_independent_of_drives`], [`Surface/UnitDomain`],
  [Thm 24], [`HasType.rename`, `Satisfies.rename`, `Clocked.rename`], [`Behavior/Rename`],
  [Thm 25], [`inst_decl_disjoint`, `binding_satisfies`, `flatten_WF`, `flatten_causal`, `flatten_wellClocked`, `flatten_singleDriver`, `open_port_stays_open`], [`Behavior/Instantiate`, `Behavior/Preservation`],
  [Thm 26], [`eval_flat_to_inst`, `eval_inst_to_flat`, `modular_iff_flat`, `substitute_composeWF`], [`Behavior/Semantics`, `Behavior/Substitution`],
  [§10.3], [`group_is_identity_on_design`, `socket_no_fanout`, `restrict_realizes`, `system_composeWF`, `flat_WF`, `flat_causal`, `private_unobservable`, `orig_iff_flat`], [`Behavior/Group`, `Behavior/Boundary`, `Behavior/Extract`, `Behavior/ExtractPreservation`],
)
]
```
