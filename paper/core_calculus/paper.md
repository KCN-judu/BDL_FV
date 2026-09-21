# Abstract {-}

When the behavior of an interactive physical product is designed, the designer often knows *that* one product quantity determines another before knowing *how*: a lamp's brightness follows its tilt, and other parts of the design can be built on that relationship long before its formula is chosen. This paper presents $\lambda_{\mathrm{BDL}}$, the core calculus of the Behavior Design Language, in which a typed semantic relationship is the primary design object. A relationship is a persistent declaration — a stable identity, a signature between nominal *concepts*, a growable set of public commitments — that may exist and be depended upon while its realization is absent; a realization, when it arrives, *refines* the declaration rather than replacing it. The calculus gives this intermediate design state a precise semantics and proves that design progression respects it: refining a declaration preserves every client's typing unconditionally and every client's discharged commitment under a monotonicity condition on evidence that a mechanized counterexample shows necessary. Nominal concepts keep a relationship between *meanings* distinct from a relationship between the representations those meanings share, and a realization may construct only the concepts its own signature announces, so that realization cannot silently cross a semantic boundary the designer did not draw. Because relationships in a physical product hold over time, the calculus interprets declarations as streams in authored clock domains with one temporal primitive, and is deterministic and total on causal designs without exposing any scheduler order; because a computed value is not yet an effect, a relationship reaches the world only through an explicit drive edge with a single driver. Reusable behavior is a structured set of relationships instantiated by renaming, and composition adds no semantic machinery. All definitions, theorems and counterexamples are mechanized in Lean 4 with no `sorry` and no classical choice.

**Keywords:** design calculi, refinement, nominal types, reactive semantics, clock domains, logical relations, mechanized metatheory, Lean 4

# Introduction

Consider a designer working out the behavior of a tilt-dimmed lamp. Early in the work they know five things that are not yet code. Brightness depends on tilt — a relationship whose formula is undecided and may stay undecided for weeks. Other parts of the design already rest on that relationship: the light is driven by it, a warming base reads it, a second lamp will reuse it. When the formula does arrive, it must not retroactively change what the earlier declaration meant to those parts. A tilt and a motor angle are both angles, and a brightness and an opacity are both numbers between zero and one, yet the relationship *tilt to brightness* is not the relationship *motor angle to brightness*, and no formula should be able to turn one into the other by accident. And the relationship will eventually hold over time, in a timing domain, and move a physical light — facts that must attach to it without collapsing the design into its implementation.

The first of these is the one that a programming-language presentation handles least naturally. In a functional language, writing

$$
f : A \to B
$$

is normally the first line of a definition; the signature anticipates, and is soon accompanied by, a computation $f\,x = \dots$. The signature has meaning on its own — it is checked, it documents, it constrains — but the object being authored is the function. In the design workflow above, the first line alone is already the artifact. `dimByTilt : Tilt -> Brightness` states that a relationship exists, what it connects, and which semantic boundary it draws; it says nothing about how the relationship is computed, and the designer has not yet decided. This is not an unfinished program. It is a complete design commitment at one level of detail, deliberately left open at the next.

This paper is about giving that state a semantics. We present $\lambda_{\mathrm{BDL}}$, the core calculus of the Behavior Design Language (BDL), a language for designing the behavior of interactive physical products. Its organizing thesis is **relation before realization**: the primary authored object is a typed semantic relationship, represented in the calculus as a *persistent declaration* with a stable identity, a signature, and public commitments; a computation is one possible *realization* of that relationship, supplied later as a refinement. The calculus exists to make the intermediate state — declared, typed, depended upon, unrealized — typable, referenceable, composable, refinable, stable for its clients, and eventually realizable, without pretending that the computation already exists.

We are careful about what this claim is. Existing mechanisms provide every piece of the story: module signatures separate interface from implementation; abstract types hide representations; refinement and contract systems attach progressively stronger constraints; synchronous languages interpret definitions as clocked streams. $\lambda_{\mathrm{BDL}}$ does not show that any of these cannot express a declared-but-unrealized relationship. What it contributes is a direct, compositional semantics for a workflow in which *concept identity, interface commitment, delayed realization, temporal structure and physical effect coexist as facts about one object*, together with mechanized proofs that they interact as the workflow needs. A relationship is representationally a declaration in an environment, referred to by identity from terms; it is a first-class *design* object, not a first-class value that terms pass around, and the paper says so wherever the distinction matters.

## One object, six constraints

A likely first reaction to the calculus is that it bundles unrelated mechanisms — a refinement order, nominal types, dimensions, clocks, output bindings, renaming. The answer that organizes this paper is that each is a constraint on the same object:

- **Refinement** governs how a relationship acquires commitments and a realization (§4). The refinement order is the mathematical form of design progression, and the stability theorems say that progress does not destroy the meaning of earlier decisions.
- **Nominal concepts and the construction grant** govern *what meanings* a relationship connects and *what* a realization is authorized to produce (§5). Representation is not meaning; a signature's result concept is the only concept its realization may construct.
- **Dimensions** govern the arithmetic of representations once a concept is observed, and are orthogonal to concept identity (§5.3).
- **Clock domains** govern *when* a relationship's value belongs to the design (§6). A relationship participates in an authored temporal structure, and the semantics must respect it without exposing a scheduler.
- **Outputs** govern when a relationship's value becomes physical effect (§8). A computed value is not an effect; the drive edge is where the design meets the world, once per output.
- **Composition** governs how relationship structures are reused (§9). A behavior is a structured set of relationships; instantiation renames, binding connects, and flattening shows that nothing new is needed.

The same choice recurs on three of these axes: identity is nominal — of a concept, of a clock domain, of an output — and crossing an identity is always a visible artifact (a declared relationship, a transport with an initial value, a drive edge), never a coercion the implementation performs on the designer's behalf.

## Contributions

The contributions, in the order the paper develops them, each answer a design question with a formal mechanism and a theorem.

1. **Relationship-first declarations and refinement** (§2, §4). A design is an environment of declarations each of which may lack a realization; typing reads declarations through their signatures only. The refinement order (add a commitment, supply a realization, strengthen a realized interface with re-verification) formalizes progressive commitment. Theorem 3 shows that a client typed against a relationship before its realization is typed after it, with no hypothesis; Theorem 4 shows that a client's discharged commitments survive refinement when the validation layer's evidence is monotone in the environment; Theorem 5 is a mechanized counterexample showing the condition necessary.
2. **Semantic integrity of realizations** (§5). A relationship connects concepts, not representations. Nominal concept types with write-once representation bindings keep `Tilt -> Brightness` distinct from `MotorAngle -> Brightness`; the construction grant, derived from the declaration's own signature, is the authority a realization has to produce a concept (Theorem 7); erasure to representations is sound, and no evaluation, memory or transport creates a concept tag (Theorem 12).
3. **Temporal interpretation of relationships** (§6). Declarations are interpreted as streams in nominal clock domains with one temporal primitive — read a domain at its last activation strictly before now. Evaluation is deterministic (Theorems 9, 14) and total on causal designs by a tick-indexed logical relation (Theorems 11, 14); the strictly-before rule keeps the scheduler unobservable, and its alternative is mechanically shown to expose it (Theorem 15).
4. **Derived rather than primitive design structure** (§7). Lists, products and one recursor suffice for the collection equations a designer writes, and the lossless cross-domain window — the construction most likely to be proposed as a primitive — is five declarations over memory, transport and lists, correct for every schedule (Theorem 16).
5. **Explicit physical effect** (§8). A relationship becomes effect only through a drive edge to a nominally identified output with a single driver; the physical output is then a function of the tick (Theorem 17), and hidden arbitration is shown to make three outputs from one design.
6. **Compositional reuse** (§9). Components, instances and bindings are derived from renaming and realization; the flattened composition is an ordinary design accepted by the unchanged judgments (Theorem 19), and modular and flat evaluation agree on a stated fragment (Theorem 20).
7. **Mechanization.** Every definition, theorem and counterexample is a Lean 4 declaration in `KCN-judu/BDL_FV` [@moura2021lean]; the development has no `sorry`, uses only propositional extensionality and quotient soundness (through function extensionality), and no classical choice. Each result is cited by its Lean name where it is stated; Appendix A indexes them.

Two conventions bound every claim. *Minimal* means minimal among the alternatives that were formalized and refuted, never a minimality theorem. Where a theorem holds for a fragment, the fragment is part of the statement. The paper is not about the surface language, the authoring environment, the toolchain, hardware validation or deployment, all of which live above the kernel and are described in the BDL monograph of which this paper is the formal core; and it makes no claim about designers — that a workflow is well served by this semantics is an empirical question no theorem here addresses.

# The design problem

## A relationship as a design object

We fix vocabulary for the rest of the paper. A **relationship** is the design-level commitment: *brightness follows tilt*. A **declaration** is the formal object that represents it — a stable identity $\delta$, an **interface** (the relationship's public promise: an expected type between concepts and a list of commitments), and an optional **realization** (a computation implementing the promise). **Refinement** is the progressive strengthening of a declaration — more commitments, then a realization, then stronger commitments re-verified — under which clients that relied on the earlier state remain valid. A **design** is an environment of declarations. In the Lean development a declaration without a realization is `unresolved`; the paper says *unrealized*, because the word matters: nothing is missing from such a declaration. Its identity, its concepts, its commitments and, later, its timing domain and output are all present. What is postponed is the computation, and postponing it is the designer's decision.

Three kinds of declaration will appear. A relationship with inputs, `dimByTilt : Tilt -> Brightness`, has an arrow signature. A relationship with no inputs, `light : Brightness`, is a value the design computes. And a declaration that will *never* receive a realization, `tilt : Tilt`, is an *input*: a relationship the environment realizes, whose value the product reads. The kernel distinguishes none of these by kind; all are declarations, and the last two differ only in whether a realization is present. That an input is "a relationship realized by the world" is not a metaphor here — it is exactly how the semantics of §6 reads it.

In type-theoretic terms the whole design state is a *global environment* of named constants, and that is the vocabulary the rest of the paper uses. A **concept** is a *nominal base type*: a type constant $C$, distinct from every other by name, whose values are formed by an injection $\text{sem}\;C$ from a representation type $R$ that the environment $\Theta$ binds to it — an abstract type with a private constructor (§5). A **declaration** is a *typed constant* $\delta : \tau$ in the global environment $\Delta$, with an optional *definiens*: exactly a proof assistant's `Parameter` before its `Definition`, except that here the parameter state is the normal one and giving the definiens is the design step. A declaration of base type, $\delta : \text{sem}\;C$, is one *inhabitant* of the concept — one value at each tick — and its definiens, when present, is the one term that produces that value; a declaration without a definiens is an *axiom* the environment discharges (the product's *Source*). A declaration of function type is a template applied wherever another definiens names it. Several constants of one base type are ordinary (`sensorA : Temperature`, `sensorB : Temperature`, `roomTemp : Temperature := if available then sensorA else sensorB`); a term refers to a constant by name and never to a type, so nothing is ever resolved "by concept". The product speaks the same ladder as *concept* (the type), *Sem block* (a constant of concept type, holding one value) and *mapping block* (its definiens); the calculus needs only *type*, *constant* and *definiens*, and it keeps the product's word *relationship* for a constant read as a design object.

## Unrealized but usable

The claim that an unrealized declaration is a complete design state is only worth making if the state is *usable*. In $\lambda_{\mathrm{BDL}}$ it is. Let the design $\Delta_0$ contain

$$
\begin{array}{l}
\mathit{dimByTilt} = \langle \delta_1,\ \langle \text{sem}\;\text{Tilt} \to \text{sem}\;\text{Brightness},\ [\,]\rangle,\ \text{none}\rangle,\\
\mathit{tilt} = \langle \delta_2,\ \langle \text{sem}\;\text{Tilt},\ [\,]\rangle,\ \text{none}\rangle,
\end{array}
$$

and let the designer now declare and *realize* the light:
$$
\mathit{light} = \langle \delta_3,\ \langle \text{sem}\;\text{Brightness},\ [\,]\rangle,\ \text{some}\;((\text{declRef}\;\delta_1)\;(\text{declRef}\;\delta_2))\rangle .
$$
The realization of `light` is well typed in $\Delta_0$, by T-Ref twice — using only $\Delta_0^{\mathrm{ty}}(\delta_1) = \text{some}\;(\text{sem}\;\text{Tilt} \to \text{sem}\;\text{Brightness})$ and $\Delta_0^{\mathrm{ty}}(\delta_2) = \text{some}\;(\text{sem}\;\text{Tilt})$ — and T-App once:
$$
\begin{array}{ll}
\text{(T-Ref)} & \Theta;\Delta_0;G;[\,] \vdash \text{declRef}\;\delta_1 : \text{sem}\;\text{Tilt} \to \text{sem}\;\text{Brightness}\\[2pt]
\text{(T-Ref)} & \Theta;\Delta_0;G;[\,] \vdash \text{declRef}\;\delta_2 : \text{sem}\;\text{Tilt}\\[2pt]
\text{(T-App)} & \Theta;\Delta_0;G;[\,] \vdash (\text{declRef}\;\delta_1)\;(\text{declRef}\;\delta_2) : \text{sem}\;\text{Brightness}
\end{array}
$$

The derivation consults $\Delta_0$ only through the *type view* $\Delta^{\mathrm{ty}}$ — the expected type of each declared identity — and never asks whether $\delta_1$ has a realization. `light` is a well-formed, typed, referenceable part of the design while `dimByTilt` has no formula. This is the calculus's thesis made formal, and the theorem that completes it is stated in §4: when `dimByTilt` is later realized, or given a commitment, every judgment about `light` in $\Delta_0$ holds in the refined design (Theorem 3). The client did not depend on a body, so no body can invalidate it.

## Design progression as refinement

The running example progresses through eight commitments, in the order a designer might make them; each is a step in the calculus and each is taken up in a later section.

| step | the designer commits to | the calculus records | §  |
|---|---|---|---|
| 1 | a relationship `dimByTilt : Tilt -> Brightness` exists | an unrealized declaration with that signature | 2.2, 4 |
| 2 | `light` is what `dimByTilt` yields for the current tilt | a realized declaration referring to `dimByTilt` by identity | 2.2 |
| 3 | `Tilt` is represented by an angle, `Brightness` by a scalar | write-once bindings in the concept environment $\Theta$ | 5 |
| 4 | a formula for `dimByTilt` | a realization, typed under the grant of its own signature | 4, 5 |
| 5 | `dimByTilt` promises `monotone` | a commitment, with evidence re-verified | 4 |
| 6 | `light` updates with the interaction, in domain `fast` | a clock assignment and the domain judgment | 6 |
| 7 | the lamp's LED shows `light` | a drive edge to an output with a single driver | 8 |
| 8 | a second lamp reuses the whole behavior | a component instantiated by renaming and bound | 9 |

*Table 1. The running example as progressive commitment.*

Conceptually, a design before all its realizations are chosen describes a constrained family of completed behaviors, and each step narrows the family: a commitment excludes realizations that lack the property, a realization fixes one computation, a clock assignment fixes when values are observed, a drive edge fixes what the product does. We use this reading as motivation only. The calculus does not denote a set of possible products; what it has is a *refinement relation* on declarations and environments (§4.2), and the theorems are about that relation — one direction of progressive commitment, from less determined to more. Steps that do not narrow — changing a signature, dropping a commitment, replacing a realization — are *edits*, and the calculus promises nothing about them (§4.4).

# The calculus

The term language of $\lambda_{\mathrm{BDL}}$ is a simply typed λ-calculus with registered first-order operators. What makes it a calculus of relationships rather than of functions is not its terms but the environments they are typed and evaluated against, and the projections through which each judgment may read them. This section fixes the syntax, the environments and the typing judgment; the design content of each environment is developed in the sections that follow.

## Syntax

Figure 1 gives the syntax. Types are those of a simply typed calculus with booleans, counts and arrows, extended by nominal concept types $\text{sem}\;C$ over an identity $C$, physical quantities $\text{q}\;d$ over a dimension $d$, and the data formers $\text{opt}$, $\text{list}$ and $\times$. A dimension is an exponent vector over a fixed finite set of base dimensions (length, time, angle, mass, temperature in the development); dimensions form an abelian group under pointwise addition, which is the only structure the calculus uses.

$$
\begin{array}{rl}
& C \in \text{ConceptId} \qquad d \in \text{Dim} \qquad \kappa \in \text{ClockId} \qquad \delta \in \text{DeclId} \qquad o \in \text{OutputId}\\[3pt]
\tau,\sigma \;\text{::=}\; & \text{bool} \mid \text{nat} \mid \tau \to \sigma \mid \text{sem}\;C \mid \text{q}\;d \mid \text{opt}\;\tau \mid \text{list}\;\tau \mid \tau \times \sigma\\[3pt]
e \;\text{::=}\; & x \mid \text{true} \mid \text{false} \mid n \mid \lambda x{:}\tau.\,e \mid e\;e \mid \text{declRef}\;\delta \mid \text{rep}\;e \mid \text{mk}\;C\;e \mid p\\
\mid\; & \text{delay}\;e\;e \mid \text{sync}\;\kappa\;e\;e \mid \text{fold}\;e\;e\;e\\[3pt]
p \;\text{::=}\; & \text{lit}_d\,n \mid \text{add}_d \mid \text{sub}_d \mid \text{mul}_{d_1 d_2} \mid \text{div}_{d_1 d_2} \mid \text{lt}_d \mid \text{eq}_\tau^{\mathit{pf}} \mid \neg \mid \wedge \mid \vee \mid \text{ite}_\tau\\
\mid\; & \text{none}_\tau \mid \text{some}_\tau \mid \text{isSome}_\tau \mid \text{getD}_\tau \mid \text{nil}_\tau \mid \text{cons}_\tau \mid \text{length}_\tau \mid \text{take}_\tau \mid \text{drop}_\tau \mid \text{reverse}_\tau \mid \text{head}_\tau\\
\mid\; & \text{toList}_\tau \mid \text{pair}_{\tau\sigma} \mid \text{fst}_{\tau\sigma} \mid \text{snd}_{\tau\sigma}
\end{array}
$$

*Figure 1. Syntax of $\lambda_{\mathrm{BDL}}$. Variables are de Bruijn indices in the development; the paper writes names. $\mathit{pf}$ in $\text{eq}_\tau^{\mathit{pf}}$ is a proof that $\tau$ is a data type.*

*Notation.* Each letter is bound once, where its object first appears, and is never rebound: $C$ a concept (a nominal type, the level of $\text{ConceptId}$), $\delta$ a declaration identity and $h$ a declaration record (§3.2), $v, w$ values — a value of concept $C$ is $\text{sem}\;C\;v$ (§6) — $\kappa$ a clock domain (lowercase $c$ is avoided, so that no letter reads as an instance of the concept $C$), $o$ an output, $d$ a dimension, $\tau, \sigma$ types, $R$ a representation (a concept-free data type), $e, b$ terms, $x$ variables, $t$ a tick, $p$ a property. Environments: $\Theta$ concepts, $\Delta$ the design, $G$ the grant, $\Gamma$ the context, $\mathrm{K}$ clocks, $S$ the schedule, $I$ the input, $\rho$ the evaluation environment, $\Omega$ outputs and $\beta$ drive edges (§3.2, §8); $\mathcal{P} = \langle \tau, \mathcal{K} \rangle$ an interface with its commitment list (§4), $\mathit{ev}$ evidence, $\eta$ an erasure (§5.2), $\mathcal{C}$ a component and $k$ an instance index (§9). The ladder of §2 reads, in these letters: $R$ is the type of a type, $C$ is a type, $h$ (named $\delta$) is one instance holding one $v$ per $t$.

Terms are those of the λ-calculus plus five design-specific forms. $\text{declRef}\;\delta$ refers to a relationship by the identity of its declaration; nothing about the declaration's interface or realization is in the syntax, which is what lets a term refer to a relationship that has no realization yet. $\text{rep}\;e$ observes the representation of a concept value and $\text{mk}\;C\;e$ constructs one. $\text{delay}\;i\;e$ is the value of $e$ at the previous activation of the current domain, $i$ before any; $\text{sync}\;\kappa\;i\;e$ is the value of $e$ in domain $\kappa$ at $\kappa$'s last activation strictly before now, $i$ if none. $\text{fold}\;f\;z\;l$ is the list recursor, $\text{fold}\;f\;z\;[x_1,\dots,x_n] = f\;x_1\;(\cdots(f\;x_n\;z))$. Registered operators $p$ are first-order constants with types; they never apply a closure.

Two predicates on types recur. A type is **data**, $\tau.\text{Data}$, when no arrow occurs in it; a type is **concept-free**, $\tau.\text{SemFree}$, when no $\text{sem}$ occurs in it. Both are decidable by structural recursion, and $(\tau \times \sigma).\text{Data} \iff \tau.\text{Data} \wedge \sigma.\text{Data}$, $(\text{list}\;\tau).\text{Data} \iff \tau.\text{Data}$ hold definitionally (`Ty.prod_data`, `Ty.list_data`).

## Environments

A term is typed and evaluated against several environments, each read through a stated projection and nothing else. This discipline — *which environment a judgment may see* — is what the stability results of §4 rest on: a client sees a relationship's signature and never its realization, so the realization can change without the client noticing.

- A **declaration** is a triple
  $$\text{DesignDecl} = \langle\, \mathit{id} : \text{DeclId},\ \mathit{interface} : \langle \mathit{expectedType} : \text{Ty},\ \mathit{commitments} : \text{PropertyId}^{*}\rangle,\ \mathit{realization} : \text{Option}\;\text{Expr} \,\rangle .$$
  A **design** is a declaration environment $\Delta : \text{DeclId} \to \text{Option}\;\text{DesignDecl}$. Its *type view* $\Delta^{\mathrm{ty}}(\delta) = (\Delta\;\delta).\text{map}(\cdot.\mathit{interface}.\mathit{expectedType})$ is all that typing sees; its *realization view* $\Delta^{\mathrm{real}}(\delta) = (\Delta\;\delta).\text{bind}(\cdot.\mathit{realization})$ is all that evaluation sees. An **unrealized** declaration is one whose realization is $\text{none}$; nothing else distinguishes it. - A **concept environment** $\Theta : \text{ConceptId} \to \text{Option}\;\text{Ty}$ binds each concept to a representation. It is well formed, $\Theta.\text{WF}$, when every bound representation is concept-free and data: $\Theta\;C = \text{some}\;R \Rightarrow R.\text{SemFree} \wedge R.\text{Data}$.
- A **grant** $G : \text{ConceptId} \to \text{Prop}$ says which concepts a term may construct. $\text{Grant.none}$ permits nothing; $\text{Grant.of}\;\tau$ permits the concepts in result position of $\tau$, $\text{grant}(\text{sem}\;C) = [C]$, $\text{grant}(\tau \to \sigma) = \text{grant}(\sigma)$, $\text{grant}(\_) = [\,]$.
- A **clock environment** $\mathrm{K} : \text{DeclId} \to \text{Option}\;\text{ClockId}$ assigns each declaration a domain; $\text{none}$ marks a domain-agnostic relationship usable in any domain. A **schedule** $S : \text{ClockId} \to \mathbb{N} \to \text{Bool}$ says at which global ticks each domain activates. An **input** $I : \text{DeclId} \to \mathbb{N} \to \text{Value}$ supplies a value for every unrealized declaration at every tick — the environment's realization of the design's inputs.
- An **output environment** $\Omega : \text{OutputId} \to \text{Option}\;\langle \mathit{accepts} : \text{Ty}, \mathit{clock} : \text{ClockId}\rangle$ and the **drive edges** $\beta : \text{DeclId} \to \text{Option}\;\text{OutputId}$ are introduced in §8.

Typing sees $\Theta$, $\Delta^{\mathrm{ty}}$ and $G$. Evaluation sees $\Delta^{\mathrm{real}}$, $I$ and (in several domains) $S$. The domain judgment sees $\mathrm{K}$. Outputs see $\Omega$, $\mathrm{K}$, $\Delta^{\mathrm{ty}}$ and $\beta$. Commitments and evidence are seen by the satisfaction relation of §4 and by nothing else.

## Typing

The typing judgment $\Theta;\Delta;G;\Gamma \vdash e : \tau$ is given in Figure 2. Rules T-Var, T-Bool, T-Nat, T-Lam and T-App are those of the simply typed λ-calculus. T-Ref is the only rule that reads $\Delta$, and it reads the type view. T-Rep and T-Mk read $\Theta$ through the binding $\Theta\;C = \text{some}\;R$; T-Mk additionally requires the grant. T-Prim assigns each registered operator its type; the dimension algebra is entirely in that table (Figure 3), so an application of $\text{mul}_{d_1 d_2}$ is checked by T-App like any other. T-Delay and T-Sync require the type to be data and the context to be empty; T-Fold types the recursor.

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
\frac{\Theta\;C = \text{some}\;R \quad \Theta;\Delta;G;\Gamma \vdash e : \text{sem}\;C}{\Theta;\Delta;G;\Gamma \vdash \text{rep}\;e : R}\ \text{(T-Rep)}
\qquad
\frac{G\;C \quad \Theta\;C = \text{some}\;R \quad \Theta;\Delta;G;\Gamma \vdash e : R}{\Theta;\Delta;G;\Gamma \vdash \text{mk}\;C\;e : \text{sem}\;C}\ \text{(T-Mk)}
$$

$$
\frac{\tau.\text{Data} \quad \Theta;\Delta;G;[\,] \vdash i : \tau \quad \Theta;\Delta;G;[\,] \vdash e : \tau}{\Theta;\Delta;G;[\,] \vdash \text{delay}\;i\;e : \tau}\ \text{(T-Delay)}
$$

$$
\frac{\tau.\text{Data} \quad \Theta;\Delta;G;[\,] \vdash i : \tau \quad \Theta;\Delta;G;[\,] \vdash e : \tau}{\Theta;\Delta;G;[\,] \vdash \text{sync}\;\kappa\;i\;e : \tau}\ \text{(T-Sync)}
$$

$$
\frac{\Theta;\Delta;G;\Gamma \vdash f : \tau \to \sigma \to \sigma \quad \Theta;\Delta;G;\Gamma \vdash z : \sigma \quad \Theta;\Delta;G;\Gamma \vdash l : \text{list}\;\tau}{\Theta;\Delta;G;\Gamma \vdash \text{fold}\;f\;z\;l : \sigma}\ \text{(T-Fold)}
$$

*Figure 2. Typing (`HasType`). T-Ref is the only rule reading $\Delta$; T-Rep and T-Mk the only rules reading $\Theta$; T-Mk the only rule reading $G$.*

| operator | type | operator | type |
|---|---|---|---|
| $\text{lit}_d\,n$ | $\text{q}\;d$ | $\text{eq}_\tau^{\mathit{pf}}$ | $\tau \to \tau \to \text{bool}$ |
| $\text{add}_d,\ \text{sub}_d$ | $\text{q}\;d \to \text{q}\;d \to \text{q}\;d$ | $\text{ite}_\tau$ | $\text{bool} \to \tau \to \tau \to \tau$ |
| $\text{mul}_{d_1 d_2}$ | $\text{q}\;d_1 \to \text{q}\;d_2 \to \text{q}\;(d_1 + d_2)$ | $\text{some}_\tau$ | $\tau \to \text{opt}\;\tau$ |
| $\text{div}_{d_1 d_2}$ | $\text{q}\;d_1 \to \text{q}\;d_2 \to \text{q}\;(d_1 - d_2)$ | $\text{getD}_\tau$ | $\text{opt}\;\tau \to \tau \to \tau$ |
| $\text{lt}_d$ | $\text{q}\;d \to \text{q}\;d \to \text{bool}$ | $\text{toList}_\tau$ | $\text{opt}\;\tau \to \text{list}\;\tau$ |
| $\text{length}_\tau$ | $\text{list}\;\tau \to \text{q}\;0$ | $\text{cons}_\tau$ | $\tau \to \text{list}\;\tau \to \text{list}\;\tau$ |
| $\text{head}_\tau$ | $\text{list}\;\tau \to \text{opt}\;\tau$ | $\text{take}_\tau,\ \text{drop}_\tau$ | $\text{q}\;0 \to \text{list}\;\tau \to \text{list}\;\tau$ |
| $\text{fst}_{\tau\sigma}$ | $\tau \times \sigma \to \tau$ | $\text{pair}_{\tau\sigma}$ | $\tau \to \sigma \to \tau \times \sigma$ |

*Figure 3. Types of the registered operators (`Prim.ty`), abridged. Dimension algebra lives here and nowhere else. $\text{eq}$ is available at every data type and $\text{lt}$ at quantities only.*

Three features of Figure 2 carry the rest of the paper.

*The typing boundary.* Typing depends on the type view of declarations and the representation view of concepts and on nothing else — not on realizations, commitments, evidence, clocks or drive edges. This is the formal content of *relation before realization*: a reference is typed by the relationship's promise, and the stability of clients under later realization (Theorem 3) is a direct consequence.

*The construction boundary.* Client code is typed under $\text{Grant.none}$; a declaration's realization is typed under $\text{Grant.of}$ its own expected type (§4.1). A value of $\text{sem}\;C$ is therefore constructed only inside a declaration whose signature announces $\text{sem}\;C$: the signature is the realization's authority, and §5 shows what each weaker alternative admits.

*The temporal boundary.* $\text{delay}$ and $\text{sync}$ are typed only in the empty context and only at data types. Both restrictions were forced by the totality proof of §6, not chosen: a delayed closure would have to be transported across ticks, and a delay under a binder would re-evaluate its operand at the previous tick in an environment created at the current one. Temporal state therefore belongs to declarations — memory is a property of a relationship, not of a function — and relationships with inputs are pointwise — the arrangement of `pre` in Lustre, where it lives in nodes rather than in functions [@halbwachs1991lustre].

## Inference, uniqueness and monotonicity

Inference is syntax-directed. A function $\text{infer}\;\Theta\;\Delta\;G\;\Gamma\;e : \text{Option}\;\text{Ty}$ follows the rules of Figure 2 and needs only decidability of $G$, of type equality and of $\tau.\text{Data}$.

**Proposition 1 (Inference; `infer_sound`, `infer_complete`, `HasType.unique`).** $\text{infer}\;\Theta\;\Delta\;G\;\Gamma\;e = \text{some}\;\tau$ iff $\Theta;\Delta;G;\Gamma \vdash e : \tau$; hence typing is decidable and every term has at most one type.

Uniqueness matters beyond decidability: it is why the surface language's polymorphism can be *matching* rather than unification (§7.2), and why a nominal mismatch is reported as "Brightness and Opacity are different concepts" and never as a unification residue. Typing is moreover monotone in each of its three environments — under environment refinement (§4.2), under binding more concepts, and under a larger grant (`HasType.mono_env`, `HasType.mono_concept`, `HasType.mono_grant`); each monotonicity is one direction of progressive commitment.

Weakening holds for the delay-free fragment by appending to the context (`HasType.weaken_append`); a stateful term cannot be moved under a binder at all, so no stronger weakening is needed.

# Progressive realization

A declaration evolves: it is declared with a signature, it acquires commitments, it acquires a realization, its commitments are strengthened. Throughout, other declarations refer to it. This section gives design progression its mathematical form — a *refinement order* generated by three steps — and proves that progression preserves what was established before it: clients typed against a relationship stay typed (Theorem 3), and clients whose commitments were discharged through it stay discharged, provided the validation layer's evidence is monotone (Theorem 4), a proviso that Theorem 5 shows cannot be dropped.

## Interfaces, evidence and satisfaction

An interface $\mathcal{P} = \langle \tau, \mathcal{K}\rangle$ is the relationship's public promise: an expected type and a list of commitments — atomic labels such as `total`, `monotone`, `bounded` that a client may rely on. Interfaces are ordered by monotone refinement:
$$
\mathcal{P} \sqsubseteq \mathcal{P}' \;:=\; \mathcal{P}.\tau = \mathcal{P}'.\tau \;\wedge\; \mathcal{P}.\mathcal{K} \subseteq \mathcal{P}'.\mathcal{K} ,
$$
a decidable preorder, frozen on the type and growing on commitments (`InterfaceRefines`). Nothing else is an interface refinement.

What discharges a commitment is not the kernel's business; it is the validation layer's. The kernel abstracts it as an **evidence** relation $\mathit{ev} : \text{DeclEnv} \to \text{Expr} \to \text{PropertyId} \to \text{Prop}$. Evidence takes the environment because compositional discharge needs it — "$A$ is monotone because $B$ is committed to be monotone" consults $B$'s interface. A realization $e$ **satisfies** $\mathcal{P}$ in $\Theta,\Delta,\Gamma$ when it has the expected type under the grant of that type and every commitment is discharged:
$$
\text{Satisfies}\;\mathit{ev}\;\Theta\;\Delta\;\Gamma\;e\;\mathcal{P} \;:=\; \Theta;\Delta;\text{Grant.of}(\mathcal{P}.\tau);\Gamma \vdash e : \mathcal{P}.\tau \;\wedge\; \forall p \in \mathcal{P}.\mathcal{K}.\;\mathit{ev}\;\Delta\;e\;p .
$$
A declaration is well formed when its body, if any, satisfies its interface; a design is **globally well formed**, $\text{GlobalWF}\;\mathit{ev}\;\Theta\;\Delta$, when every stored declaration sits under its own identity and is well formed in $\Delta$ at top level. An unrealized declaration is always well formed.

The refinement order is complete for abstract evidence: $\mathcal{P} \sqsubseteq \mathcal{P}'$ iff every realization of $\mathcal{P}'$ in every environment under every evidence relation realizes $\mathcal{P}$ (`InterfaceRefines_iff_semantic`). The proof of the converse instantiates evidence at "the property is in $\mathcal{P}'$'s list" and the body at a reference to a single declaration.

## The refinement order and the lifecycle

Design progression is generated by three steps (`DeclRefines`), each preserving the identity by construction and each checked against the current environment $\Delta$:
$$
\frac{S \sqsubseteq \mathcal{P}'}{\langle \delta, \mathcal{P}, \text{none}\rangle \rightsquigarrow \langle \delta, \mathcal{P}', \text{none}\rangle}
\qquad
\frac{\text{Satisfies}\;\mathit{ev}\;\Theta\;\Delta\;\Gamma\;e\;\mathcal{P}}{\langle \delta, \mathcal{P}, \text{none}\rangle \rightsquigarrow \langle \delta, \mathcal{P}, \text{some}\;e\rangle}
\qquad
\frac{S \sqsubseteq \mathcal{P}' \quad \text{Satisfies}\;\mathit{ev}\;\Theta\;\Delta\;\Gamma\;e\;\mathcal{P}'}{\langle \delta, \mathcal{P}, \text{some}\;e\rangle \rightsquigarrow \langle \delta, \mathcal{P}', \text{some}\;e\rangle}
$$
An unrealized declaration may have its interface refined; an unrealized declaration may be realized by a satisfying computation; a realized declaration may have its interface strengthened provided the realization is *re-verified* against the new interface. Strengthening without re-verification breaks well-formedness, and the counterexample is mechanized (`naive_breaks_wellformedness`).

Separately from the steps there is a purely structural order with no satisfaction condition: $\text{DeclLeq}\;h\;h'$ requires the same identity, $h.\mathcal{P} \sqsubseteq h'.\mathcal{P}$, and a write-once realization ($h.\mathit{realization} = \text{some}\;e \Rightarrow h'.\mathit{realization} = \text{some}\;e$); $\text{EnvRefines}\;\Delta\;\Delta'$ lifts it pointwise and permits new declarations. Storing a refined declaration back under its identity is an environment refinement — $\Delta\;h.\mathit{id} = \text{some}\;h \wedge \text{DeclLeq}\;h\;h' \Rightarrow \text{EnvRefines}\;\Delta\;(\Delta[h'])$ (`EnvRefines_update`) — and this is the one place identity does any work: it makes the update land on the slot every reference resolves to, which is what a name does in any environment semantics.

**Proposition 2 (The lifecycle is the structural order; `DeclRefinesStar_iff`).** The reflexive–transitive closure of the three steps, all side conditions checked in $\Delta$, relates $h$ to $h'$ iff $\text{DeclLeq}\;h\;h'$ and $h'$ is well formed in $\Delta$.

## Client stability

Another part of the product may already depend on a relationship before that relationship is realized (§2.2). Can the relationship then be realized, or strengthened, without editing those clients and without invalidating what was established about them? The answer has two halves with deliberately different hypotheses, and together they are the paper's central result: progress in the design does not destroy the meaning of earlier design decisions.

**Theorem 3 (Clients survive realization — typing; `local_refinement_preserves_global_typing`).** If $\Delta\;B = \text{some}\;h$ and $\text{DeclLeq}\;h\;h'$, then every judgment $\Theta;\Delta;G;\Gamma \vdash e : \tau$ holds in $\Delta[h']$.

The proof is one line: typing reads $\Delta$ through the type view, and the type view is invariant under $\text{DeclLeq}$. That the proof is short is the point, not a weakness. The theorem says that the decision to let clients see a relationship's promise and never its realization is *sufficient* for every client to survive every realization and every added commitment, with no side condition. It is also necessary: change $B$'s expected type while keeping its identity and every client breaks, which is why the type is frozen in $\sqsubseteq$ and why changing it is an edit (§4.4).

The commitment half needs more.

**Definition (Monotone evidence).** $\mathit{ev}$ is **monotone** when $\text{EnvRefines}\;\Delta_1\;\Delta_2 \wedge \mathit{ev}\;\Delta_1\;e\;p \Rightarrow \mathit{ev}\;\Delta_2\;e\;p$. Evidence that ignores the environment is monotone; evidence that consults only the *presence* of commitments and realizations is monotone; evidence that consults their *absence* is not.

**Theorem 4 (Clients survive realization — commitments; `local_refinement_preserves_global_wf`, `local_lifecycle_preserves_global_wf`).** If $\mathit{ev}$ is monotone, $\text{GlobalWF}\;\mathit{ev}\;\Theta\;\Delta$, $\Delta\;B = \text{some}\;h$ and $h \rightsquigarrow h'$ with side conditions checked in $\Delta$, then $\text{GlobalWF}\;\mathit{ev}\;\Theta\;(\Delta[h'])$. The same holds for a whole lifecycle $h \rightsquigarrow^{*} h'$ checked against the original $\Delta$.

**Theorem 5 (Monotonicity is necessary; `badEv_not_mono`).** There is an evidence relation $\mathit{ev}_{\mathrm{bad}}$, a globally well formed two-declaration design, and a valid realization step of one declaration after which the design is not globally well formed; consequently $\mathit{ev}_{\mathrm{bad}}$ is not monotone.

The relation $\mathit{ev}_{\mathrm{bad}}$ discharges "$A$ is total" whenever the declaration $A$ reads is still unrealized — evidence from absence. Realizing that declaration is a perfectly valid step, and it destroys the discharge. The monotonicity hypothesis was not part of the original design; it appeared when Theorem 4 was attacked, and it is a Kripke-style stability condition imposed by the kernel on the validation layer: any discharge mechanism meant to survive design progression must be positive in the environment. Its design reading is direct — a commitment may be justified by what other relationships promise, never by what they have not yet decided.

Binding a representation to a previously unbound concept is likewise a refinement: typing, satisfaction and global well-formedness are monotone in $\Theta$ (`GlobalWF.of_conceptRefines`). Rebinding a concept to a different representation is an edit that breaks existing realizations (`representation_change_is_edit_not_refinement`).

## Refinement versus edit

Theorems 3–4 cover refinement only; they are what the calculus promises about design progression, and the line between progression and *edit* is part of the design. Table 2 classifies the operations a tool offers on a declaration $B$ read by a client $A$; each row is witnessed by a mechanized example on a two-declaration design.

| operation on $B$ | kind | effect on $A$ |
|---|---|---|
| add a public commitment | refinement | typing and commitments preserved |
| realize | refinement | preserved; $A$ now unfolds to a closed program |
| strengthen a realized interface | refinement, with re-verification | preserved |
| change the expected type, keep identity | edit | typing broken |
| drop a commitment | edit | typing silent; $A$'s commitment broken |
| replace $B$ by a new identity | edit | dangling reference |
| detach or replace the realization | edit | evidence that consulted the body is void |
| assign or change a clock domain (§6) | edit | domain judgment on clients broken |
| retarget an output binding (§8) | edit | completeness or single-driver may break |

*Table 2. Refinement versus edit.*

Two rows are instructive. Dropping a commitment changes no type, so the type checker is silent, yet $A$'s own commitment was discharged through $B$'s and is now unsupported: commitments are part of the interface in the same load-bearing sense as the expected type. Detaching a realization is an edit for the same reason: clients' typing is unaffected, but evidence that consulted the body is void. The kernel does not forbid edits; it declines to promise anything about them, and a tool must reopen the validation of transitive dependents.

## Unfolding

Before time enters, the semantics of a design is *unfolding*: replace each reference to a realized declaration by its realization, recursively, stopping at unrealized declarations ($\text{Unfolds}\;\Delta\;e\;e'$). Let $\text{DependsOn}\;\Delta\;a\;b$ hold when the body of $a$ refers to $b$.

**Proposition 6 (Unfolding; `Unfolds.det`, `Unfolds.exists_of_acyclic`, `Unfolds.not_of_cyclic`, `Unfolds.refFree_of_fullyRealized`).** Unfolding is deterministic; on the delay-free fragment it exists iff the reference graph is acyclic; a reference on a cycle through realized declarations has no unfolding at all; and a fully realized well-typed design unfolds to a reference-free program of the same type.

Acyclicity is witnessed by a rank that strictly decreases along edges, $\text{Acyclic}\;\Delta := \exists\,\mathit{rank}.\;\forall a\,b.\;\text{DependsOn}\;\Delta\;a\;b \to \mathit{rank}\;b < \mathit{rank}\;a$, and excludes cycles (`Acyclic.not_cyclic`). The pure fragment has no fixpoints, so a cyclic definition denotes nothing; §6 shows which cycles become meaningful once $\text{delay}$ exists, and that unfolding agrees with tick evaluation on the first-order fragment (`unfolds_preserves_eval`).

# Semantic integrity

A relationship connects *meanings*. `dimByTilt : Tilt -> Brightness` relates a product concept to a product concept, and it is not the relationship `MotorAngle -> Brightness` even though a tilt and a motor angle are both angles. Section 4 typed declarations without saying what a type means; this section adds the two things a product concept carries that a number does not — an identity that survives representation, and a physical dimension — and shows that a realization, when it arrives, is constrained to preserve the semantic boundary the signature drew before it existed. The distinction the section rests on is stated once: a **concept** is what the designer means, its **representation** is the data it is carried by, and the two are bound separately, later, and write-once.

## Nominal identity, and the grant as realization authority

*Why not identify concepts by representation?* Suppose concepts were represented only by their representation types, so that `Tilt` and `MotorAngle` are both $\text{q}\;\text{Angle}$. Then the wire `motorTarget := tiltSensor` is well typed and the design is globally well formed, because nothing in the model records the distinction the designer drew. Nominal types $\text{sem}\;C$ over an internal identity record it: two distinct identities are distinct types regardless of representation, so the invalid wire is rejected by T-App with no additional judgment. An explicit relationship `tiltToMotor : Tilt -> MotorAngle` is an ordinary declaration of arrow type — signature-first, possibly unrealized — and it appears in the term wherever a crossing occurs. The kernel has no cast, coercion or conversion.

*Why not let any realization construct any concept of matching representation?* Nominal identity alone leaves concept values opaque: under T-Ref and T-App only, a value of $\text{sem}\;C$ can originate only in a declaration of concept type (`no_semantic_value_without_declaration`). That is the right state *before* a realization exists. To let a formula realize a relationship, representation must be observable and constructible, and the obvious way to add it destroys what identity just bought. With global $\text{rep}_C : \text{sem}\;C \to R$ and $\text{mk}_C : R \to \text{sem}\;C$ available everywhere, $\lambda x.\;\text{mk}_{\mathrm{Motor}}(\text{rep}_{\mathrm{Tilt}}\;x)$ is a well-typed `Tilt -> MotorAngle` in the empty environment with no declared relationship (`unrestricted_representation_binding_bypasses_semantic_identity`), and the crossing can hide inside a body whose signature mentions no motor (`hidden_crossing_inside_unrelated_body`). Observation alone is safe but cannot realize a mapping.

The grant separates the two, and its design reading is *realization authority*: the signature the designer wrote before any computation existed is what authorizes the computation's result. $\text{rep}$ is typed everywhere (T-Rep); $\text{mk}\;C$ is typed only where $G\;C$ (T-Mk); client code is typed under $\text{Grant.none}$ and a realization under $\text{Grant.of}$ of its own signature (the definition of $\text{Satisfies}$). A realization of `Tilt -> Brightness` may construct a `Brightness` and nothing else — not a `MotorAngle`, not an `Opacity`, whatever their representations. Let $e.\text{constructs}\;C$ hold when $\text{mk}\;C$ occurs in $e$.

**Theorem 7 (Realization authority; `HasType.constructs_granted`).** If $\Theta;\Delta;G;\Gamma \vdash e : \tau$ and $e.\text{constructs}\;C$, then $G\;C$. Under $\text{Grant.of}\;\tau$: a value of $\text{sem}\;C$ is built only inside a realization whose signature announces $\text{sem}\;C$.

The hidden crossing above is rejected under the grant of an unrelated declaration and becomes legal, and visible, once `tiltToMotor` is declared (`hidden_crossing_rejected_under_grant`, `representation_binding_does_not_enable_hidden_semantic_mapping`).

Two constraints on representations in $\Theta.\text{WF}$ were not anticipated. Representations must be concept-free: if `Tilt` may be represented *by* `MotorAngle`, then $\text{rep}$ itself is a hidden mapping under every policy including observation-only. And they must be data, a requirement that arrived from the reactive semantics: a concept value may be delayed, and a function-typed representation would carry a closure across ticks.

The grant is a known shape — the private constructor of an abstract type exported only to its defining module [@mitchell1988abstract], or a capability attached to a definition site. What is specific is that the capability comes from the signature the designer already wrote, so no annotation is added, and one consequence follows: after all bodies are inlined into one program, that program is checked under the universal grant, because each construction was authorized at its own declaration. Semantic isolation is a property of the design graph and survives inlining as provenance (Theorem 12), not as a type property of the executable.

## Representation is not meaning: erasure

Let $\eta : \text{ConceptId} \to \text{Ty}$ map each concept to a data type, agreeing with $\Theta$ on bound concepts. Erasure $\tau^{\eta}$ replaces $\text{sem}\;C$ by $\eta\;C$ throughout a type; on terms, $\text{rep}\;e$ and $\text{mk}\;C\;e$ erase to $e^{\eta}$, and the type indices of operators are erased.

**Proposition 8 (Erasure is sound; `HasType.erase`).** If $\Theta.\text{WF}$, $\eta$ agrees with $\Theta$, and $\Theta;\Delta;G;\Gamma \vdash e : \tau$, then $\Theta;\Delta^{\eta};G';\Gamma^{\eta} \vdash e^{\eta} : \tau^{\eta}$ for every grant $G'$.

Erasure is not injective — `Tilt` and `MotorAngle` erase to the same type (`erase_not_injective`) — and the untyped baseline is exactly what erasure leaves: the design the nominal calculus rejects is accepted after erasure (`baseline_is_erased_modelA`). Generated code is therefore ordinary code; the semantic layer has no runtime residue. This is the precise sense in which representation is not meaning: the meaning lives in the design's declarations and is checked there, and the representation is all that runs.

Three alternatives were formalized and refuted. A model in which the display name *is* the identity makes renaming destructive (`rename_under_name_identity_breaks_client`), whereas here a rename preserves identity (`semantic_rename_preserves_identity`). Treating a concept as an ordinary declaration admits category errors: the concept becomes usable as a value and can be realized by a number. Keeping identity out of the type as interface metadata checked by a direct-wire rule is evaded by η-expansion, since $(\lambda x.\,x)\;\mathit{tilt}$ has the same flow with no direct wire (`bweak_evaded_by_eta`); a compositional role judgment strong enough to close that gap has the rule shapes of typing over $\text{sem}$ and duplicates it.

## Dimensions: coherent arithmetic on representations

Dimensions play a narrower role than concept identity. Once a concept is observed through $\text{rep}$, the arithmetic on its representation must remain physically coherent, and that is all dimensions do. A physical quantity has type $\text{q}\;d$. There is no dimension-specific typing rule: $\text{add}_d : \text{q}\;d \to \text{q}\;d \to \text{q}\;d$, $\text{mul}_{d_1 d_2} : \text{q}\;d_1 \to \text{q}\;d_2 \to \text{q}\;(d_1 + d_2)$ and $\text{div}_{d_1 d_2}$ with $d_1 - d_2$ are registered operators, and an application is checked by T-App. `length + time` is ill typed (`dimension_mismatch_rejected`); erasing every dimension to the zero vector is a sound translation that accepts it (`counterexampleB_baseline_accepts_length_plus_time`), so the untyped numeric baseline is the erasure of dimensional typing in the same sense that it is the erasure of nominal typing.

Dimension and identity are orthogonal, and the orthogonality is what the relationship-first reading needs: `Tilt` and `MotorAngle` both bound to $\text{q}\;\text{Angle}$ remain distinct types (`same_dimension_does_not_imply_same_semantic_identity`); a relationship realized by the dimensioned formula $\lambda x.\;\text{mk}\;\text{Brightness}\;(\text{rep}\;x \cdot \mathit{gain})$ with $\mathit{gain} : \text{q}\;(0 - \text{Angle})$ is typed, a dimension error inside it is caught by the same typing, and the formula cannot manufacture a `MotorAngle` despite the shared dimension (`explicit_semantic_mapping_uses_dimensioned_formula`). The association between a concept and its dimension lives in $\Theta$, not in the identity and not in the type constructor: the designer says *tilt to brightness* first and *tilt is an angle* separately.

Units are not in the calculus at all. A literal `90 deg` elaborates to $\text{lit}_{\text{Angle}}$ of a scaled magnitude; a coordinate $\text{inUnit}(q, u)$ is $q$ divided by a scale constant and has dimension zero; $\text{withUnit}(x, u)$ is the converse; a conversion is their composition. Each is elaboration, none is a kernel construct, and a unit choice never reaches a type: `1 m` and `100 cm` are equal values of one type. The unit laws are proved above the kernel over an abstract scalar domain and instantiated exactly by a symbolic group in which π is a generator, so that a degree is exactly π/180 radian; we do not develop them here. Dimensional typing is thus Kennedy's discipline [@kennedy1997units; @kennedy2010units] without unit polymorphism in the kernel: dimension variables appear only in the surface's definitional families (§7.2), where matching against closed dimensions instantiates them.

# Relationships in time

A relationship in an interactive physical product does not hold only in a type space; it holds *over time*, and it holds in an authored temporal structure — the tilt moves with the interaction, the room temperature with the environment. This section interprets declarations in time. Its order follows the thesis: first what it means for a declared relationship to have a value at a tick (a stream, with unrealized declarations read from the environment), then how memory enters a relationship, then which timing domain a relationship's value belongs to, and finally why the one rule that governs reading across domains is the one that keeps the designer's temporal structure intact.

## Declarations as streams

Values are booleans, naturals (which also carry every $\text{q}\;d$; the executable kernel's magnitudes are naturals), tagged concept values $\text{sem}\;C\;v$, $\text{none}$, $\text{some}\;v$, lists, pairs, closures $\text{clo}\;\rho\;e$ over a value environment, and partially applied operators $\text{prim}\;p\;\vec{v}$. An operator is computed when saturated: $\text{applyPrim}\;p\;\vec{v}$ is $\text{compute}\;p\;\vec{v}$ if $|\vec{v}|$ equals $p$'s arity and $\text{prim}\;p\;\vec{v}$ otherwise.

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
\frac{\rho \vdash_t e \Downarrow \text{sem}\;C\;w}{\rho \vdash_t \text{rep}\;e \Downarrow w}
\qquad
\frac{\rho \vdash_t e \Downarrow w}{\rho \vdash_t \text{mk}\;C\;e \Downarrow \text{sem}\;C\;w}
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

*Figure 4. Single-domain evaluation (`Ev`), with $\Delta$ and $I$ ambient. In one domain $\text{sync}\;\kappa$ evaluates exactly as $\text{delay}$ (rules `syncZero`, `syncSucc`), which §6.7 justifies. Literals evaluate to themselves. $\#i$ is de Bruijn index $i$.*

Three points of Figure 4 deserve comment. An unrealized declaration is an *input*: E-Input reads $I\;\delta\;t$, the environment's realization of the relationship. A realized declaration is evaluated from its realization at the current tick in the *empty* environment (E-Real): a reference's value never depends on the local environment of the reader, which is what makes a relationship a stream the design observes rather than a function of its call site (`Ev.declRef_env_irrelevant`). And $\text{delay}$ shifts the tick: read at $t+1$, it evaluates its operand at $t$; at $0$ it evaluates the initial value.

The recursor's rule unrolls syntactically. Rather than a recursive definition of a fold on values, the rule evaluates the syntactic term $\text{fold}\;\#2\;\#1\;\#0$ in an environment holding the tail, the seed and the function, and then the term $\#2\;\#1\;\#0$ in an environment holding the result, the head and the function. This keeps $\text{Ev}$ an ordinary inductive relation with no mutual recursion, so every proof by induction on $\text{Ev}$ that predated the recursor extends by one case, and totality is a separate lemma by induction on the list (§7.1).

**Theorem 9 (Determinism; `Ev.det`).** If $\rho \vdash_t e \Downarrow v_1$ and $\rho \vdash_t e \Downarrow v_2$ then $v_1 = v_2$.

Evaluation is a partial function with no hidden evaluation order — there are no effects to order — and this holds unconditionally.

An executable interpreter $\text{evalF}$ with a fuel parameter is proved sound for the relation (`evalF_sound`, `Ev.of_evalF`). Every trace in the development and in this paper was computed by it inside the proof checker.

## Cycles and causality

Let $e.\text{instRefs}$ be the declarations $e$ refers to *instantaneously*: those not under the delayed operand of a $\text{delay}$ or $\text{sync}$ (the initial value is read at tick $0$ and counts as instantaneous). $\text{InstDependsOn}\;\Delta\;a\;b$ holds when $b \in \text{instRefs}$ of $a$'s body.

**Definition (Causal).** $\text{Causal}\;\Delta := \exists\,\mathit{rank}\,R.\;(\forall \delta.\;\mathit{rank}\;\delta < R) \wedge \forall a\,b.\;\text{InstDependsOn}\;\Delta\;a\;b \to \mathit{rank}\;b < \mathit{rank}\;a$.

On the delay-free fragment $\text{InstDependsOn}$ is $\text{DependsOn}$, so causality is exactly bounded acyclicity (`Causal_iff_acyclic_of_delayFree`): the earlier condition is the timeless special case rather than a replaced requirement. A structural cycle every path of which passes through a delayed operand — `A := delay 0 B; B := A`, or a self-delayed accumulator — is causal. A cycle that is partly delayed is not.

**Proposition 10 (Strict cycles have no value; `Ev.not_of_strictCyclic`).** If $a$ lies on a cycle of references passing through neither a delayed operand nor a lambda, then for every tick and environment there is no $v$ with $\rho \vdash_t \text{declRef}\;a \Downarrow v$.

Not "some default", not "one of several": no derivation exists. A gap should be recorded. A cycle guarded by a lambda, `A := λx. A x`, is rejected by $\text{Causal}$ yet `declRef A` does evaluate — to a closure; only applying it diverges. $\text{Causal}$ is conservative for lambda-guarded cycles and Proposition 10 covers strict cycles only.

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
\mathcal{R}^{A}_{\Theta}[\text{sem}\;C]\;v \iff & \exists w.\;v = \text{sem}\;C\;w \wedge \forall R.\;\Theta\;C = \text{some}\;R \to \mathcal{R}^{A}[R]\;w
\end{array}
$$

The concept clause says that a concept value is a tagged representation value. Its inner use of the relation at the representation $R$ is the concept-free relation $\text{RedSF}$; because $\Theta.\text{WF}$ makes $R$ concept-free, the definition is well founded on the type without appeal to $\Theta$ (`Red_semFree`). At data types the relation is independent of $A$ (`Red_data`), which is what allows a delayed value to be transported between ticks. Registered operators are related at their types for any $A$ that saturates them (`Red_prim`).

Well-typed inputs are inputs related to the type view: $\Delta^{\mathrm{ty}}(\delta) = \text{some}\;\tau \wedge \Delta^{\mathrm{real}}(\delta) = \text{none} \Rightarrow \mathcal{R}^{\text{Apply}\;\Delta\;I\;t}_{\Theta}[\tau]\;(I\;\delta\;t)$ for every $t$.

**Theorem 11 (Totality under causality; `fundamental`, `reactive_total`, `Ev.red`).** Let $\Theta.\text{WF}$, let $\mathit{rank}, R$ witness $\text{Causal}\;\Delta$, let $\text{GlobalWF}\;\mathit{ev}\;\Theta\;\Delta$ and let $I$ be well typed. Then for every tick $t$, bound $r$, grant $G$, and $\Theta;\Delta;G;\Gamma \vdash e : \tau$, and every $\rho$ related to $\Gamma$ such that every instantaneous reference of $e$ has rank below $r$, there is $v$ with $\rho \vdash_t e \Downarrow v$ and $\mathcal{R}^{\text{Apply}\;\Delta\;I\;t}_{\Theta}[\tau]\;v$.

Consequently, in a causal, globally well formed design with well-typed inputs, every declared relationship has a value at every tick, and that value — unique by Theorem 9 — is related to its expected type.

*Proof sketch.* Lexicographic induction on $(t, r, \text{derivation})$. A delayed operand at tick $t+1$ is evaluated at tick $t$ under *any* rank (the first component decreases); an instantaneous reference to a realized declaration $\delta$ is evaluated at the same tick under the smaller bound $\mathit{rank}\;\delta$ (the second decreases), and its realization is well typed under the grant of its own signature by $\text{GlobalWF}$; every other case is the induction on the derivation. The $\text{fold}$ case uses `fold_total` (§7.1). $\square$

The relation is a step-indexed logical relation in the sense of Appel and McAllester [@appel2001indexed] and Ahmed [@ahmed2006stepindexed], with the tick as the index and the rank as a second, inner index; what differs is that the index counts *time* rather than *steps*, so that the induction on it is the induction that makes a delayed self-reference well defined.

## Two restrictions forced by totality

T-Delay and T-Sync restrict their type to data and their context to empty. Neither restriction was a design decision; each is what the induction of Theorem 11 needs. A delayed closure would be a value at tick $t$ related by $\mathcal{R}^{\text{Apply}\;\Delta\;I\;t}$ that must be transported to tick $t+1$, and the arrow clause is tick-indexed and cannot be transported; `Red_data` is exactly the statement that data clauses can. A delay under a binder would evaluate its operand at the previous tick in an environment created at the current one. The restrictions have two corollaries stated as theorems: nothing of function type can be delayed or transported (`arrow_not_delayable`, by inversion), and memory and transport are typed only in the empty context (`delay_not_under_binder`, `sync_not_under_binder`). Temporal state therefore belongs to declarations — a relationship may remember, a function may not — and a reusable stateful behavior is instantiated into fresh declarations (§9) rather than abstracted over.

Initialization is semantic, not validation. Every $\text{delay}$ carries an explicit initial value. Two toy relations without one show why: the first tick is either undefined (`first_tick_undefined_without_init`) or nondeterministic (`first_tick_nondeterministic_without_init`).

## Provenance through time

State carries semantic tags; it never creates them. Let $v.\text{Taints}\;C$ hold when the tag $C$ occurs anywhere inside $v$ — including inside closures' environments and bodies.

**Theorem 12 (Semantic integrity over time; `Ev.tag_provenance`, `temporal_state_preserves_semantic_identity`).** If no realization in $\Delta$ constructs $C$, no input value is tainted by $C$, $e$ does not construct $C$ and $\rho$ is clean, then every value $\rho \vdash_t e \Downarrow v$ is clean. In particular a delayed value carries exactly the tag of the value delayed.

Combined with Theorem 7 this is the runtime half of semantic integrity: a concept appears in a value only if some signature announces it or some input carries it, at every tick. The typing rule $\text{delay} : \tau \to \tau \to \tau$ at data $\tau$ gives the static half — a delayed tilt is a tilt, and a backward difference over a time step has dimension $\text{Length} - \text{Time}$ with no derivative primitive.

On the first-order fragment a compiler cares about — *wiring* designs, whose realizations contain no lambda — closures never arise, evaluation is independent of the local environment, and unfolding a reference to its realization preserves the value at every tick (`Ev.noClo`, `Ev.env_irrelevant`, `unfolds_preserves_eval`); *pure* terms, with no reference, memory or transport, have the same value in every design at every tick (`Ev.pure`), which §7.2 uses for the definitional library.

## Clock domains as design context

A clock domain is part of a relationship's design context: it says *when the relationship's value belongs to the design*, and the designer authors it as an identity — "moves with the interaction", "moves with the environment" — before any rate is known. The time model is one global base tick and a schedule $S : \text{ClockId} \to \mathbb{N} \to \text{Bool}$ saying at which global ticks each domain activates. A period $n$ induces the schedule $t \bmod n = 0$ (`Sched.periodic`); the schedule lives outside the design. Domain-local time is not a separate counter but the sequence of a domain's activations. The last activation of $\kappa$ strictly before $t$ is
$$
\text{prevAct}\;S\;\kappa\;0 = \text{none},\qquad \text{prevAct}\;S\;\kappa\;(t{+}1) = \text{if}\;S\;\kappa\;t\;\text{then}\;\text{some}\;t\;\text{else}\;\text{prevAct}\;S\;\kappa\;t ,
$$
with $\text{prevAct}\;S\;\kappa\;t = \text{some}\;t' \Rightarrow t' < t \wedge S\;\kappa\;t'$.

Each declaration is assigned a domain by the clock environment $\mathrm{K}$, or none if it is a domain-agnostic relationship usable anywhere. The clock is interface data in every sense that matters — clients' validity depends on it, it is frozen under refinement, and changing it is an edit (Table 2) — and it is stored as a projection beside the interface, as a concept's representation is stored in $\Theta$ rather than in the type.

The **domain judgment** $\text{Clocked}\;\mathrm{K}\;\kappa\;e$, for $\kappa : \text{Option}\;\text{ClockId}$, says that $e$ may be evaluated in domain $\kappa$:
$$
\begin{array}{rl}
\text{Clocked}\;\mathrm{K}\;\kappa\;(\text{declRef}\;\delta) \iff & \mathrm{K}\;\delta = \text{none} \;\vee\; \mathrm{K}\;\delta = \kappa\\
\text{Clocked}\;\mathrm{K}\;(\text{some}\;\kappa)\;(\text{delay}\;i\;e) \iff & \text{Clocked}\;\mathrm{K}\;(\text{some}\;\kappa)\;i \wedge \text{Clocked}\;\mathrm{K}\;(\text{some}\;\kappa)\;e\\
\text{Clocked}\;\mathrm{K}\;(\text{some}\;\kappa)\;(\text{sync}\;\kappa'\;i\;e) \iff & \text{Clocked}\;\mathrm{K}\;(\text{some}\;\kappa)\;i \wedge \text{Clocked}\;\mathrm{K}\;(\text{some}\;\kappa')\;e\\
\text{Clocked}\;\mathrm{K}\;\text{none}\;(\text{delay}\;i\;e) \iff & \text{False} \qquad\qquad \text{Clocked}\;\mathrm{K}\;\text{none}\;(\text{sync}\;\kappa'\;i\;e) \iff \text{False}
\end{array}
$$
and homomorphically elsewhere. A reference stays in its domain or is agnostic; a delay needs a domain; $\text{sync}\;\kappa'$ switches the domain of its operand. A design is well clocked when every realization is clocked in its own declaration's domain. Typing is unchanged and blind to domains: the direct wire between two domains at the same value type is well typed and rejected only by $\text{Clocked}$. Placing the domain in the type instead was tried and set aside: every domain-agnostic relationship would then need clock polymorphism (`clocked_type_forces_polymorphism`), and nothing the type rejects is missed by the judgment.

## Multi-domain evaluation

The judgment $\rho \vdash^{\kappa}_{t} e \Downarrow v$ — in domain $\kappa$ at global tick $t$, with $S$, $\Delta$, $I$ ambient — is $\text{Ev}$ with the two temporal rules replaced by four (`MEv`):
$$
\frac{\text{prevAct}\;S\;\kappa\;t = \text{none} \quad \rho \vdash^{\kappa}_{t} i \Downarrow v}{\rho \vdash^{\kappa}_{t} \text{delay}\;i\;e \Downarrow v}
\qquad
\frac{\text{prevAct}\;S\;\kappa\;t = \text{some}\;t' \quad \rho \vdash^{\kappa}_{t'} e \Downarrow v}{\rho \vdash^{\kappa}_{t} \text{delay}\;i\;e \Downarrow v}
$$
$$
\frac{\text{prevAct}\;S\;\kappa'\;t = \text{none} \quad \rho \vdash^{\kappa}_{t} i \Downarrow v}{\rho \vdash^{\kappa}_{t} \text{sync}\;\kappa'\;i\;e \Downarrow v}
\qquad
\frac{\text{prevAct}\;S\;\kappa'\;t = \text{some}\;t' \quad \rho \vdash^{\kappa'}_{t'} e \Downarrow v}{\rho \vdash^{\kappa}_{t} \text{sync}\;\kappa'\;i\;e \Downarrow v}
$$
$\text{delay}$ reads the previous activation of the current domain; $\text{sync}\;\kappa'$ reads the previous activation of $\kappa'$ and evaluates its operand *there*, in $\kappa'$. All other rules carry $\kappa$ unchanged.

**Proposition 13 (One temporal primitive; `delay_is_sync_own`, `clocked_delay_iff_sync_own`, `single_domain_embedding`).** $\rho \vdash^{\kappa}_{t} \text{delay}\;i\;e \Downarrow v$ iff $\rho \vdash^{\kappa}_{t} \text{sync}\;\kappa\;i\;e \Downarrow v$, and $\text{delay}\;i\;e$ is clocked in $\kappa$ iff $\text{sync}\;\kappa\;i\;e$ is. Under the always-active schedule, $\rho \vdash^{\kappa}_{t} e \Downarrow v$ iff $\rho \vdash_t e \Downarrow v$, for every $\kappa$.

The kernel therefore has one temporal primitive — read a domain at its previous activation — and $\text{delay}$ is notation for its diagonal; a $\text{delay}$ in a slow domain reads three global ticks back where a $\text{delay}$ in a fast one reads one, with the same syntax. The single-domain semantics of §6.1 is the one-domain special case of this one rather than a replaced machine.

**Theorem 14 (Determinism and totality in every domain; `MEv.det`, `mfundamental`, `multi_domain_total`).** Multi-domain evaluation is a partial function, for every schedule. In a causal, globally well formed design with inputs well typed in every domain, every declared relationship has a value in every domain at every tick, related to its expected type.

The proof reuses the logical relation of §6.3 with the application relation $\text{MApply}\;S\;\Delta\;I\;\kappa\;t$, and the same lexicographic induction: a transport at $t$ evaluates its operand at $t' < t$ under any rank. Causality is the *same* $\text{Causal}\;\Delta$: a transport's operand is never instantaneous, so no cross-domain cycle can be. An interpreter $\text{mevalF}$ is proved sound (`mevalF_sound`). Tag provenance holds across domains (`MEv.tag_provenance`): transport changes timing, not identity, and a crossing from `Tilt@fast` to `Tilt@slow` authorizes neither `Tilt -> MotorAngle` nor $\text{q}\;\text{Length} \to \text{q}\;\text{Time}$, by the typing rule.

## Strictly before: preserving the authored temporal structure

*Why not expose scheduler order?* A transport sees only source activations strictly before the destination tick. The rule exists to preserve the designer's declared temporal relationship — "`heat` reads the light as it stood before this tick" — without adding a fact the designer never authored, namely which of two simultaneously active domains the implementation happens to run first. That is a choice with an observable alternative, and the alternative was built.

**Theorem 15 (Same-tick visibility exposes the scheduler; `scheduling_order_observable`).** Let $\text{MEv}_{\le}$ be the semantics in which a transport may also see a simultaneously active source, resolved by a priority between domains. There is a two-domain design, a schedule and an input such that two priorities give two different values to the same declaration at the same tick.

At tick 1 both domains are active for the first time; with the source first the transport delivers the source's current value, with the destination first it delivers the initial value. The strictly-before rule has no such parameter, and Theorem 14 has no order between simultaneously active domains in its statement. Every crossing costs one destination-visible step; "synchronous sub-domains evaluated in one instant" are, in this model, the same domain.

Rate and identity are distinct. A clone of a domain with the identical schedule is a different domain, and a direct wire between them is rejected (`equal_rate_not_same_domain`); a domain at the same rate but shifted in phase reads different values through a transport. Rate changes are validation-only: they change the induced schedule and the observed values, but no client's well-formedness. This is where the calculus departs from synchronous languages that recover clocks by inference [@colaco2003clocks; @biernacki2008clock]: the domain is authored, because the information needed to infer it — the realization binding — arrives at the point where a designer is least able to make the decision.

# Derived structure

The calculus deliberately has no primitive for most of what a designer names. This section records what *is* in the kernel for computation over data — one recursor, products, equality — and then two negative design results that follow the same method: before adding a primitive, ask whether the behavior is already derivable from declarations, memory, transport and lists. Every temporal operator of the surface language is, and so is the one construction most likely to be proposed as primitive, the lossless cross-domain window.

## The recursor, products and equality

$\text{fold}\;f\;z\;l$ is a *term former*, not a registered operator. The kernel has no recursion, deliberately; a total language needs an eliminator for its inductive data, and $\text{fold}$ is the one construct that applies a function value in the course of evaluation. Registered operators never apply closures. The alternative of one primitive per collection operation was rejected because a primitive cannot apply a closure and each would need its own evaluation rule; the alternative of bounded unrolling was rejected because lists — the cross-domain window — are unbounded.

The recursor is total on related values (`fold_total`, `mfold_total`), by an induction on the list separate from Theorem 11, which invokes it in its $\text{fold}$ case. Every collection operation — `map`, `filter`, `any`, `all`, `contains`, `append`, `sum`, `zip`, and through $\text{toList}$ the option eliminators — is a definition over $\text{fold}$, and each is proved to compute the mathematical function it names through one general lemma: the recursor computes $\text{List.foldr}\;g$ whenever the step closure implements $g$ on the reachable accumulators (`fold_spec`; then `any_spec`, `all_spec`, `map_spec`, `filter_spec`, `min_spec`, `clamp_spec`, …). Finite quantification is a fold — $\forall x \in \mathit{xs}.\,P\,x$ iff `all xs P` evaluates to true (`forall_in_list`, `exists_in_list`) — and a finite-set literal means membership with duplicates irrelevant (`oneOf_mem`, `oneOf_dup_irrelevant`), so there is no `Set` type and no uniqueness convention.

$\tau \times \sigma$ with $\text{pair}$, $\text{fst}$, $\text{snd}$ entered the kernel after the Church encoding was tried and refuted twice. A Church pair is an arrow, and arrows are not data: nothing of function type can be delayed or transported (`arrow_not_delayable`), so paired *state* — a delayed reading with its timestamp — needs a data product. And a Church pair used as a first-class value needs rank-2 types: in a toy System F with a rank measure, the type of $\text{fst}$ on Church pairs has rank 2 (`church_fst_rank`), and in the prenex fragment a pair instantiated at one result type serves only one projection (`church_pair_prenex_one_projection`). Products are value composition only; they are never a component interface or an output bundle (§9 shows what a tuple-returning declaration does to the dependency graph).

$\text{eq}_\tau^{\mathit{pf}}$ is structural equality at every data type — booleans, numbers, $\text{none}$/$\text{some}$, pairs and lists componentwise, concept values by tag and representation — with the proof $h : \tau.\text{Data}$ carried *in the syntax*. This is the kernel's only capability evidence: an equality on a function type is unwritable rather than ill typed, which keeps T-Prim unconditional. On first-order values structural equality is equality (`Value.beq_iff`, by a mutual induction over the nested value type).

Order is deliberately not generalized. A first formulation gave `<` a structural meaning at every data type — booleans, options, pairs and lists lexicographically — and it was formally consistent. An audit rejected it on the grounds that no such order has a design meaning: `mode1 < mode2` would order modes by a constructor tag, `None < Some x` is an artifact. The structural order was deleted and $\text{lt}_d$ restored to quantities only. So $\text{Data} \Rightarrow \text{Eq}$ holds (`Cap.eq_iff_data`) but $\text{Eq} \not\Rightarrow \text{Ord}$; order on a *concept* is a surface capability — a concept the designer declared ordered and represented by a quantity compares as $\text{lt}_d$ on $\text{rep}$, a term the kernel already admits (`lt_only_on_quantities`, `lt_rejected`, `min_mode_rejected`). Enumerations follow the same rule: equality is natural, declaration order is never silently behavioral order.

## Polymorphism by families, and the library as combinators

Five models of polymorphism were compared: a monomorphic kernel; per-type duplication; rank-1 parametric polymorphism; System F; higher rank. The one adopted is rank-1 *as definitional families*: every library entry is a function $\text{Ty} \to \text{Expr}$ (or $\text{Dim} \to \text{Expr}$) in the metalanguage, and a scheme is a pattern over type and dimension variables with capability constraints. The kernel sees only the instances (`instances_are_monomorphic`: three uses of `min` are three kernel terms), and T-Prim, T-App and Proposition 1 are unchanged.

Why this needs no kernel support: a use site always has *closed* argument types. Every declaration's expected type is frozen and closed, and inference is bottom-up, so finding the instance of a scheme is one-way *matching* of the scheme's pattern against closed types — decidable, returning the unique substitution on the pattern's variables (`matchTy_sound`, `matchTy_complete`). There is no unification of two open types, no let-generalization inside expressions [@damas1982principal], and no principal-type search; those problems arise when a definition's type is inferred from its body, and every definition here carries its signature. The situation is that of local type inference [@pierce2000local] with no bidirectionality needed. Capability constraints are checked after matching (`Scheme.instantiate_sound`), and the two failure points have designer-level explanations: *no instance* and *capability failed*. System F was rejected by measuring what it would add — the prenex fragment *is* instantiation of families — and every candidate higher-rank use has a rank-1 replacement (`applyBoth_rank`, `applyBoth_replacement`). Dimension polymorphism (`sum : list (q d) → q d`) uses the same mechanism with dimension pattern variables; no kind system, because the dimension algebra already lives in the operator table.

Nominality survives all of it. *Any* family typed at $\alpha \to \alpha \to \alpha$, instantiated at concept $C$, rejects an argument of concept $C' \neq C$, the representations never consulted (`generic_preserves_identity`); the same for $\text{q}\;d$ versus $\text{q}\;d'$ (`generic_preserves_dimension`). This is Reynolds's abstraction [@reynolds1983types] and Wadler's free theorems [@wadler1989free] at the level of syntax: a family cannot inspect what it is instantiated at, because it is instantiated by substitution into a closed term.

Every library entry is a **combinator**: variables, literals, lambdas, applications, registered operators, the recursor and $\text{rep}$ — no reference, no state, no transport, no $\text{mk}$. For combinators four facts are proved once and combine into an inlining statement (`lib_expansion`): typing is independent of the design and the grant and reads $\Theta$ only through write-once bindings (`HasType.comb_irrelevant`); the value is the same in every design at every tick under every input (`lib_eval_context_free`, from `Ev.pure`); the term is clocked in every domain (`lib_clocked`); nothing is constructed (`Comb.noConstruct`). This is what lets an implementation inline an equation at each use without creating a declaration — a library entry as a declaration would be monomorphic and would enter the dependency graph.

The expressiveness ceiling, stated once: total first-order-data computation over booleans, quantities, concepts, options, lists and pairs, with higher-order functions and one list recursor; generic definitions instantiated at closed types; no general recursion, no type abstraction in terms, no sums (an enumeration with a payload is encoded as a tag paired with an optional payload, and a kernel sum would cost one more eliminator term former exactly like $\text{fold}$), no unbounded quantification. This is a design conclusion backed by executed cases and the proved library; it is not a minimality theorem.

## The window: a negative design result

Within one domain an occurrence is a stream of optional type (§7.4). Across domains this fails: $\text{sync}$ is a zero-order hold, so a slow consumer of a fast event source sees the last value only. Two fast events at ticks 1 and 2 and one event at tick 2 are indistinguishable at the slow activation at tick 3, and a single event at tick 1 followed by a quiet fast tick is dropped outright (`opt_loses_multiplicity_under_sync`). The counterexample is against $\text{sync}$ as an *event transport*, not against optional types; it says that multiplicity and order are observable across domains and that keeping them requires buffering.

What the destination should see is the source's activations since the destination's own previous activation — the *window*, $\text{windowTicks}\;S\;\mathit{src}\;\mathit{dst}\;t$, the source ticks in $[\text{prevAct}\;S\;\mathit{dst}\;t,\ t)$. The window equals the source's accumulated log read at the current tick minus its length at the previous destination activation (`buffer_from_log_and_cursor`): two single-instant reads, a $\text{sync}$ of a source-side accumulator and a $\text{delay}$ of a cursor. With list data this is five ordinary declarations:
```
log     @src :  cons src (delay nil log)             -- source-side accumulator
logD    @dst :  sync src nil log                     -- the log, transported
seen    @dst :  length logD                          -- log length now
cursor  @dst :  delay 0 seen                         -- log length at the previous activation
window  @dst :  reverse (take (seen - cursor) logD)  -- the new entries, oldest first
```

**Theorem 16 (The window is derivable; `buffer_window_correspondence`).** For every schedule, input, destination domain and tick, if the five declarations are realized as above and $\mathit{src}$ is an input, then $[\,] \vdash^{\mathit{dst}}_{t} \text{window} \Downarrow \text{list}\,(\text{map}\,(I\,\mathit{src})\,(\text{windowTicks}\;S\;\mathit{src}\;\mathit{dst}\;t))$.

The elaboration is well typed and well clocked (`buffer_elaboration_well_typed`, `buffer_elaboration_well_clocked`); the list is injective on windows, ordered by tick, and multiplicity-preserving for every predicate (`buffer_lossless`, `window_to_list_preserves_order`, `window_to_list_preserves_multiplicity`). The general negative result is that any summary depending only on the newest $k$ entries, for any fixed $k$, identifies a $k$-entry window with a $(k{+}1)$-entry window (`bounded_summary_not_lossless`); a lossless summary is injective and therefore unbounded (`lossless_iff_injective`). Capacity is thus a deployment obligation on the schedule — for periodic schedules one destination period of source activations suffices (`periodic_capacity_sufficient`) — and the only overflow policy that preserves the semantics is to reject the deployment; dropping is a semantic change (`bounded_buffer_agrees`, `negE`).

The point for the calculus is what was *not* added, and the method by which it was not added — a candidate primitive was formalized, its behavior was derived from the existing kernel, and the derivation was proved correct: no event type, no buffer primitive, no scheduler order, no same-tick visibility, no implicit overflow rule. An event stream is a data-typed declaration in a domain; an occurrence is its value at an activation; a lossless view of it across domains is the five declarations; `latest`, `count`, `coalesce` are ordinary computations over `window`.

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

*Table 3. Derived temporal operators (`Experiments/ReactiveAlternatives.lean`).*

There is no signal type in $\text{Ty}$: under this semantics a signal type would be inhabited by exactly the terms of the underlying type and would reject nothing. There is no event type: within one domain an input delivers at most one value per tick by construction, so an occurrence is a stream of optional type, and the streams of type $\text{opt}\;\tau$ are exactly the streams of multiplicity at most one. What separates an occurrence from an optional value can only be seen when a source ticks faster than its observer, which is the cross-domain question of §7.3. State has no identity of its own: a cell is a $\text{delay}$ in a declaration body, consumers refer to the declaration, and there is consequently no notion of two writers to one cell.

# Physical effect

A relationship, realized and evaluated, yields a value; a value is not yet an effect. The chain the calculus draws is *relationship → realized value → explicit drive edge → physical effect*, and this section is the last arrow. A declaration computes a value; it does not move hardware. Physical effect happens only through an explicit **drive edge** from a declaration to a nominally identified **output** — a logical actuator channel, a resource in a different sort from both concepts and declarations: "the desired steering angle" — a declaration of concept type, one instance of the concept — is a value; "the steering motor" is a resource.

- $\Omega : \text{OutputId} \to \text{Option}\;\langle \mathit{accepts}, \mathit{clock}\rangle$ — each output's accepted type and domain;
- $\beta : \text{DeclId} \to \text{Option}\;\text{OutputId}$ — the drive edges, a write-once per-declaration projection of the same shape as $\mathrm{K}$;
- $\text{DriveWF}\;\Omega\;\mathrm{K}\;\Delta\;\beta := \forall \delta\,o.\;\beta\;\delta = \text{some}\;o \to \exists \mathit{spec}.\;\Omega\;o = \text{some}\;\mathit{spec} \wedge \Delta^{\mathrm{ty}}(\delta) = \text{some}\;\mathit{spec}.\mathit{accepts} \wedge \mathrm{K}\;\delta = \text{some}\;\mathit{spec}.\mathit{clock}$;
- $\text{SingleDriver}\;\beta := \forall \delta_1\,\delta_2\,o.\;\beta\;\delta_1 = \text{some}\;o \to \beta\;\delta_2 = \text{some}\;o \to \delta_1 = \delta_2$;
- $\text{CompleteOutputs}\;\beta\;\mathit{req}$ — every required output is driven.

Nothing was added to types, typing, the domain judgment, evaluation or the grant. The edge neither coerces nor converts nor synchronizes: the driver's type *equals* the accepted type and its domain *is* the output's. A declaration typed `Tilt` cannot drive a `MotorAngle` output; an output that accepts a representation type needs an explicit $\text{rep}$-typed declaration in front of it; a slow driver reading a fast value must $\text{sync}$ it upstream. A driver of a concept-accepting output is necessarily a value, not a function (`driver_is_unit_domain`).

**Definition.** $\text{PhysicalOutput}\;S\;\Delta\;I\;\Omega\;\beta\;o\;t\;v := \exists \delta\,\mathit{spec}.\;\beta\;\delta = \text{some}\;o \wedge \Omega\;o = \text{some}\;\mathit{spec} \wedge [\,] \vdash^{\mathit{spec}.\mathit{clock}}_{t} \text{declRef}\;\delta \Downarrow v$.

**Theorem 17 (One driver, one output; `single_driver_output_deterministic`, `multiple_direct_drivers_rejected`).** Under $\text{SingleDriver}\;\beta$, $\text{PhysicalOutput}$ is a partial function of $o$ and $t$. Two declarations driving one output — each well typed, well clocked, causal and individually well formed — violate $\text{SingleDriver}$ and nothing else, and there is a tick at which the output receives two values.

*Why not hide output arbitration?* The principle is *many contributors, one explicit final driver*. Contributors are dependencies: `base + corr -> final -> motor` passes every check; priority is a conditional in the single driver; blend, maximum and clamp are ordinary declarations of the target type. Why arbitration must be explicit is shown rather than argued: first-wins, last-wins and maximum over the same value graph give three different physical outputs (`hidden_arbitration_observable`). Binding an unbound declaration to an undriven output is a refinement and preserves $\text{SingleDriver}$ (`first_output_binding_is_monotone`); binding to a driven output is invalid; retargeting, renaming or detaching an edge invalidates an unchanged design.

Two alternatives were formalized in toy form. Direct effect rows — the set of outputs a declaration drives — are exactly the drive edges, and single-driver is exactly their pairwise disjointness; propagated rows flag a valid design in which a display reads the driver; action values move the conflict into the collector that consumes them, which must then be a policy, which is the single driver by another name. None of this bears on richer effect systems [@plotkin2013handlers]; it says these formulations add no rejection the single-driver rule lacks.

Finally, the dual form, which shows that the boundary between semantic behavior and physical realization is not a matter of taste. Once zero-input relationships have the canonical interface type `() -> A` (normalized above the kernel to `A`, with the unit eliminated before any term is typed — the kernel has no unit type, and `delay` inside a zero-input declaration is why: a unit binder would forbid memory there, `delay_not_under_binder`), the form `A -> ()` suggests itself as a consumer. It cannot name one: in a pure total language every function into the one-point type is the same function (`unit_codomain_collapse`, by function extensionality), so two "consumers" are indistinguishable (`consumers_indistinguishable`), and the evaluation relation has no effect component (`eval_independent_of_drives`). Naming a receiver needs an output semantics, and the calculus already has exactly one. Semantic behavior and physical realization are related by the drive edge and are not identical.

# Reuse of relational structure

A second lamp should reuse the first's behavior without copying it. What is reused is not a code module but a *structured set of relationships* — the lamp's concepts, its declared relationships, their clocks and their outputs — with some relationships left open as ports. This section shows that everything a component needs is derivable from what §4 already provides, realization plus renaming: instantiation gives the relationships fresh identities, binding connects an instance into a larger design by ordinary realization steps, and flattening yields an ordinary design accepted by the unchanged judgments, so that composition adds no semantic machinery.

## Equivariance

A renaming $r$ bundles four maps — on declaration, semantic, clock and output identities. Renaming acts on types (through $\text{sem}$), on terms, on interfaces, on declarations and pointwise on environments; $\Delta.\text{RenamedBy}\;r\;\Delta'$ says $\Delta'$ stores the renamed declaration of $\Delta$ at the renamed identity.

**Proposition 18 (Equivariance; `HasType.rename`, `Satisfies.rename`, `Clocked.rename`).** If $\Theta;\Delta;G;\Gamma \vdash e : \tau$ and $\Theta', \Delta', G'$ are the images of $\Theta, \Delta, G$ under $r$ (agreement on the image, with no injectivity required), then $\Theta';\Delta';G';\Gamma^{r} \vdash e^{r} : \tau^{r}$; likewise for satisfaction, and for the domain judgment under a clock environment that agrees on the declared identities.

Evidence must be equivariant as well (`Evidence.Equivariant`), an abstract condition beside monotonicity. Nothing else is new in the composition theory; the rest is definitions over Proposition 18 and §4.

## Components, instances and flattening

A **port** is a template declaration by local identity with the public part of its interface and its parameter clock. A **behavior interface** has required ports (unrealized declarations a composer binds), provided ports, elaboration-time parameters (unrealized data-typed declarations bound to closed constants at instantiation) and clock parameters. A **component** is an interface, a template design over local identities below a width $W$, and a partition of its concepts and outputs into private (freshened per instance) and shared. $\text{Realizes}\;\mathit{ev}\;\mathcal{C}$ is a predicate over the existing judgments: the template is a well-formed design (`Design.WF`: $\text{GlobalWF}$, $\Theta.\text{WF}$, well clocked, causal, $\text{DriveWF}$, $\text{SingleDriver}$), every required port is an unrealized declaration of the stated interface, every provided port is declared with it, parameters are unrealized, data-typed and clock-free.

Instance $k$ of a component maps local identity $n$ to $\text{fresh}\;W\;k\;n = W\cdot(k{+}1) + n$, with $\text{decode}$ its inverse; distinct instances never share an identity (`inst_decl_disjoint`). The encoding is a device — any injective allocator would do. A **binding** realizes a destination port of one instance from a source — a port of another instance or a closed constant — with an optional transport: none for a direct reference in the same or an agnostic domain, $\text{some}\;\mathit{init}$ for $\text{sync}$ from the source's domain. A **system** is a width, a list of instances, a list of bindings, the shared concept environment and the external outputs. **Flattening** is the union of the renamed instances followed by the bindings applied as §4 realization steps: the destination port is realized as $\text{declRef}\;\mathit{src}$ or $\text{sync}\;\kappa\;\mathit{init}\;(\text{declRef}\;\mathit{src})$. The result is a design, consumed by every existing judgment unchanged.

**Theorem 19 (Composition adds no machinery; `binding_satisfies`, `flatten_WF`, `flatten_causal`, `flatten_wellClocked`, `flatten_singleDriver`, `open_port_stays_open`).** Under $\text{ComposeWF}$ — every instance realizes its interface; every binding is well formed (types agree; a direct binding's source is in the destination's domain or agnostic; a transported binding's source has a domain); external outputs are driven by at most one instance — and with evidence that is monotone, equivariant and port-sound (a discharged commitment survives when a port copy is realized by a reference to a declaration of the same interface), the flattening is globally well formed, well clocked, single-driver, causal when the inter-instance graph is acyclic, and its open ports remain open.

**Theorem 20 (Modular semantics, restricted; `eval_flat_to_inst`, `eval_inst_to_flat`, `modular_iff_flat`).** For wiring designs with closure-free inputs and direct bindings, in one domain, the value of a declaration in an instance evaluated alone with a consistent modular input equals its value in the flattened system.

The restriction is exact and recorded: transported bindings under $\text{MEv}$ need a domain-indexed input for the transported port, and higher-order bodies are not covered — the same obstacle in both directions. Substitutability follows the usual contravariance: $B$ may replace $A$ when every port $A$ provides, $B$ provides at the same type and clock, and every port $B$ requires, $A$ required; replacing an instance by a refining component preserves $\text{ComposeWF}$ (`substitute_composeWF`).

The counterexamples that fixed the design (`Experiments/BehaviorAlternatives.lean`): a name-based identity collides on double instantiation; a shared clock captured inside a template cannot be re-bound; a binding across domains without transport is rejected by $\text{Clocked}$; two instances driving one external output violate $\text{SingleDriver}$.

## Groups are the identity, and extraction is a system

A *group* — a designer's selection of several declarations — is authoring metadata: a group identity and a member list beside the design. Every group operation acts on the list and leaves the design untouched, so every kernel judgment of the design is the *same proposition* before and after, each proved by reflexivity (`group_is_identity_on_design`). A group's boundary is a projection over a finite enumeration: the non-members some member depends on ($\text{crossIn}$), the members some non-member depends on ($\text{crossOut}$); the aggregate socket a collapsed group shows is these lists, none of which is a declaration, and $a \in \text{crossIn}$ says *some* member depends on $a$ and nothing about the others (`socket_no_fanout`). Two encodings of a socket as a declaration were refuted: as a declaration every member reads, a member acquires an instantaneous dependency it never had; as a tuple-returning declaration, the consumer of one member comes to depend on the inputs of all of them. The kernel has no tuples for boundaries, and this is a reason not to add them for that purpose.

Packaging a group as a component — the one semantic step in the hierarchy declaration → group → component → system — builds two *restrictions* of the design, the component with an unrealized copy of each crossing-in declaration as a required port and the residual with an unrealized copy of each crossing-out member, and forms a two-instance system with one direct binding per crossing. No realization is translated or copied across the boundary. Both templates realize their inferred interfaces (`restrict_realizes`, needing evidence that depends only on the interfaces of the referenced declarations, `Evidence.InterfaceLocal`); the system is a well-formed composition and its flattening a well-formed design (`system_composeWF`, `flat_WF`); causality needed its own argument, since a group with both inputs and outputs is never inter-instance-acyclic, yet the flattened instantaneous graph is the original with every crossing edge subdivided through a port copy, and doubling the original rank witnesses it (`flat_causal`); private members are unobservable from the residual (`private_unobservable`); and for wiring designs an original declaration and its home copy evaluate to the same value at every tick (`orig_iff_flat`).

# Mechanization

The development is 68 Lean 4 modules (Lean 4.33.1, no dependencies beyond core): 11 in `Core` (§3–6, §8), 12 in `Behavior` (§9), 19 in `Surface` (the definitional library, polymorphism, the window and the boundary constructions above the kernel), 2 in `Validation` (outside this paper), and 24 experiment modules holding alternatives, counterexamples and executed examples; about 26 500 lines and 1 545 theorem declarations. It builds with no `sorry`. The axioms are propositional extensionality and quotient soundness, the latter only through function extensionality and the choice-free rational quotient used by the unit laws; classical choice is absent, and the whole development was re-audited for it at every phase.

Three proof-engineering choices carried the metatheory. $\text{Ev}$ and $\text{MEv}$ are ordinary inductive relations with no mutual recursion, because the recursor's rule unrolls through the environment (§6.1); every induction on evaluation extends by one case when a construct is added, and the transport primitive and the recursor entered this way with every earlier theorem re-established without a change of statement. The logical relation is parameterized by an application relation so that the single- and multi-domain semantics share it, and is independent of that parameter at data types (`Red_data`), which is the fact that lets a value cross a tick. Every rejected alternative is a theorem whose content is a rejection, stated on a concrete design and discharged by `decide` or by running the interpreters $\text{evalF}$/$\text{mevalF}$ — proved sound for the relations — inside the checker; there is no test suite beside the proofs. Several results are recorded as trivial by definition and reported as such. Extraction is not part of the development; the production toolchain implements the calculus in Rust and is tested differentially against the interpreter's traces, a tested claim and not a theorem.

# Related work

*Modules and signatures.* ML-style module systems separate an interface from its implementation, and a signature may be written, checked and depended upon before a structure matches it [@leroy1994manifest; @harper1994modules]. $\lambda_{\mathrm{BDL}}$ does not claim that such systems cannot express an unrealized relationship. The difference is one of organization: here an unrealized declaration is an ordinary inhabitant of the *design environment* rather than a separate compilation unit; its clients are typed against it in the same environment and, by Theorem 3, remain typed when it is realized; and the same declaration is simultaneously the carrier of a nominal semantic signature (§5), a clock assignment (§6) and a drive edge (§8). The commitment list is a growable part of the interface whose growth is a first-class step on a declared-but-unrealized name, with a stability condition imposed on the layer that discharges it.

*Refinement types, contracts and specification.* Refinement type systems, contracts and specification languages already support progressively stronger constraints on a definition, and we do not claim to have invented refinement. BDL's commitments are atomic labels, deliberately weaker than a refinement predicate; what is specific is where they attach — to a persistent relationship declaration whose realization may be absent — and what is proved about them: that a client's discharged commitment survives later realization and strengthening under a monotonicity condition on evidence that is shown necessary (Theorems 4–5). The condition is the Kripke-style stability familiar from logical-relations proofs [@appel2001indexed; @ahmed2006stepindexed], imposed here on a validation layer rather than on a store.

*Synchronous and reactive languages.* The temporal interpretation of §6 is that of Lustre [@halbwachs1991lustre] and Esterel [@berry1992esterel]: a global logical tick, definitions as streams, memory as `pre` with an explicit initial value, causality as acyclicity of instantaneous dependencies; Vélus [@bourke2017velus] verifies a compiler for this model, Zélus [@bourke2013zelus] and mode extensions [@colaco2005state] extend it. Functional reactive programming [@elliott1997fran; @nilsson2002frp; @cooper2006frtime] makes signals first-class values, and typed FRP [@krishnaswami2013frp; @jeffrey2012ltl; @cave2014fair] controls memory through modal types. In all of these the central authored unit is a computation — a node, a stream definition, a signal function — and clocks are inferred from how it samples [@colaco2003clocks; @biernacki2008clock; @caspi1996kahn]. In $\lambda_{\mathrm{BDL}}$ the authored unit is a declared relationship, and the temporal machinery exists to interpret it in an authored domain: there is no signal type because a declaration already is a stream; the domain is a nominal identity chosen before any rate is known; and the one transport primitive with its strictly-before rule was chosen because the alternative exposes a scheduler the designer never authored (Theorem 15). The window buffer of §7.3 does the work that sub-sampling operators do in Lucid Synchrone, as a derived construction.

*Nominal and abstract types; units of measure.* Nominal type identity is the ordinary mechanism of a nominal type system [@pierce2002tapl], and the construction grant is the private constructor of an abstract type [@mitchell1988abstract; @reynolds1983types]. Dimension types are Kennedy's [@kennedy1997units; @kennedy2010units], monomorphic in the kernel and instantiated by matching in surface families (§7.2). None of these is claimed as novel. Their role here is to keep a relationship between meanings distinct from a relationship between representations, and to keep representation arithmetic coherent — supporting mechanisms of the relationship-first model, with the erasure and provenance results (Proposition 8, Theorem 12) and the refuted alternatives (§5.1–5.2) as the evidence that they do that job.

*Typed holes and live programming.* Hazelnut [@omar2017hazelnut; @omar2019live] gives a semantics to programs with holes and to the edit actions that fill them. An unrealized declaration is not a hole position in a term; it is a declaration whose realization is absent, referred to by identity and typed by its interface, and the refinement order plays the role of the edit-action calculus restricted to the operations under which clients are stable. The two are complementary: a hole is where a term is incomplete, an unrealized declaration is where a design is deliberately open.

*Design and modeling languages.* Block-diagram environments, model-based design and systems-modeling languages [@harel1987statecharts] also let a designer connect named quantities before every block is defined, and we do not claim that they lack relationships. What $\lambda_{\mathrm{BDL}}$ adds is a small mechanized calculus for the progressive-relationship model with explicit metatheory: what a client may depend on, what a realization may construct, when a value belongs to the design, and how reuse is derived — each as a theorem, and each rejected alternative as a counterexample.

*Effects and expressiveness.* The single-driver discipline is not an effect system [@plotkin2013handlers]; §8 records that effect rows and action values, in the toy forms tried, add no rejection the drive edge lacks. The negative results of §7 are statements about whether a construct is definable from the kernel by a local translation, in the spirit of Felleisen's expressiveness [@felleisen1990expressive], as mechanized theorems about specific candidates.

# Discussion and limits

*What "first-class" means here.* A relationship is first-class as a *design object*: it has a stable identity, it may be declared, depended upon, refined, clocked, driven and instantiated, and every judgment of the calculus is stated over it. It is not a first-class *value*. Terms refer to declarations by identity and never pass a declaration as an argument or return one; there is no type of relationships, no higher-order manipulation of declarations, and the paper claims none. What is higher-order in the calculus is ordinary: functions over data, and the one recursor.

*Design versus program.* A program describes one computation. A design in $\lambda_{\mathrm{BDL}}$ may contain decisions at different levels of commitment — a relationship with a signature only, one with commitments, one with a realization, one with a clock and an output — and the calculus preserves that partially committed structure rather than requiring it to be resolved before anything is checked. This is not a claim that conventional programs are fully specified, nor that their signatures lack meaning; it is that the *progression* from less to more committed is explicit here and has a metatheory.

*One direction of commitment.* The refinement order formalizes narrowing: more commitments, a realization, stronger verified commitments. It does not formalize the family of behaviors a design leaves open, and the calculus has no denotation of a set of possible products. Edits — changing a signature, dropping a commitment, replacing a realization — are outside the order, and the calculus promises nothing about them (Table 2).

The paper's formal claims are further bounded by the following, each recorded in the development.

- *Causality is conservative for lambda-guarded cycles.* `A := λx. A x` is rejected by $\text{Causal}$ although `declRef A` evaluates to a closure; Proposition 10 covers strict cycles only.
- *Modular semantics is proved for a fragment.* Theorem 20 holds for single-domain wiring designs with direct or constant bindings; transported bindings under $\text{MEv}$ and higher-order realizations are open.
- *Evidence is abstract.* The kernel imposes monotonicity, equivariance and port-soundness on the validation layer's evidence and proves nothing about a concrete discharge mechanism.
- *No sums.* Enumerations with payloads are encoded; a kernel sum would be one eliminator term former, and its absence is a decision to stop where the executed cases stopped.
- *Magnitudes are naturals.* The executable kernel's quantities are natural numbers; the unit laws are proved over an abstract scalar domain and instantiated symbolically, and floating-point implementations are held to toleranced versions above the kernel.
- *No minimality theorem.* "Minimal" means minimal among the formalized candidates.
- *Nothing about designers.* The calculus was shaped by a design workflow's requirements; whether it serves designers is an empirical question no theorem addresses, and no claim about cognitive load, productivity or ease is made.

# Conclusion

$\lambda_{\mathrm{BDL}}$ is not interesting because it makes every implementation detail first-class. It is interesting because a typed semantic relationship can be declared, connected to concepts, depended upon by other parts of a product, placed in time and bound to a physical output while its computation is still undecided — and can then acquire that computation without disturbing anything built on it. The intermediate state is a design state, not a broken program state, and the calculus gives it a semantics in which it is typable, referenceable, composable, refinable, stable for clients and eventually realizable.

The results are the constraints on that one object, each with its theorem. Refinement preserves earlier reasoning: a client typed against a relationship's promise survives its realization unconditionally, and a client's discharged commitment survives it whenever evidence is positive in the environment, a condition that cannot be dropped (Theorems 3–5). Grants preserve semantic integrity: a realization may construct exactly the concept its signature announces, representation is not meaning, and no tag is manufactured by evaluation, memory or transport (Theorems 7, 12). Clocks preserve temporal meaning: a relationship's value belongs to an authored domain, evaluation is deterministic and total on causal designs, and no scheduler order is observable (Theorems 9, 11, 14, 15). Outputs make physical effect explicit and single (Theorem 17). Renaming preserves relational structure under reuse, and composition adds no machinery (Theorems 19, 20). The mechanized counterexamples — a scheduler made visible, an evidence relation destroyed by a valid realization, a hidden crossing between concepts, three physical outputs from one design, a lossy summary for every bounded buffer — record why each constraint takes the form it does. That these constraints are all statements about a relationship, and that they have been proved to compose, is the conceptual unity of the calculus.

# Appendix A — Theorem index {-}

Every name is a Lean declaration in `KCN-judu/BDL_FV`; the file is given per group, and names are unqualified where the namespace is `BDL`.

```{=typst}
#block(width: 100%)[
#set text(size: 8pt)
#table(
  columns: (0.55fr, 2.6fr, 1.75fr), align: left, inset: (x: 3pt, y: 2.6pt),
  stroke: (x: none, y: 0.3pt),
  table.header([*paper*], [*Lean name*], [*file*]),
  [Prop 1], [`infer_sound`, `infer_complete`, `HasType.unique`], [`Core/Typing`],
  [§3.4], [`HasType.mono_env`, `HasType.mono_concept`, `HasType.mono_grant`, `HasType.weaken_append`], [`Core/Typing`],
  [§4.1], [`InterfaceRefines_iff_semantic`, `naive_breaks_wellformedness`], [`Core/Satisfaction`, `Experiments/DeclCounterexamples`],
  [Prop 2], [`DeclRefinesStar_iff`, `EnvRefines_update`], [`Core/Satisfaction`, `Core/Decl`],
  [Thm 3], [`local_refinement_preserves_global_typing`], [`Core/Env`],
  [Thm 4], [`local_refinement_preserves_global_wf`, `local_lifecycle_preserves_global_wf`], [`Core/Env`],
  [Thm 5], [`badEv_not_mono`, `probe6_breaks`], [`Experiments/DeclCounterexamples`],
  [Prop 6], [`Unfolds.det`, `Unfolds.exists_of_acyclic`, `Unfolds.not_of_cyclic`, `Unfolds.refFree_of_fullyRealized`], [`Core/Dependency`],
  [Thm 7], [`HasType.constructs_granted`, `hidden_crossing_rejected_under_grant`], [`Core/Typing`, `Experiments/RepresentationBindingAlternatives`],
  [Prop 8], [`HasType.erase`, `erase_not_injective`, `baseline_is_erased_modelA`], [`Experiments/SemanticTypeAlternatives`],
  [§5.3], [`dimension_mismatch_rejected`, `counterexampleB_baseline_accepts_length_plus_time`, `same_dimension_does_not_imply_same_semantic_identity`], [`Experiments/DimensionAlternatives`],
  [Thm 9], [`Ev.det`, `evalF_sound`], [`Core/Reactive`],
  [Prop 10], [`Ev.not_of_strictCyclic`, `Causal_iff_acyclic_of_delayFree`], [`Core/Reactive`, `Core/Dependency`],
  [Thm 11], [`fundamental`, `reactive_total`, `Ev.red`, `Red_data`, `Red_prim`], [`Core/Reactive`],
  [§6.4], [`arrow_not_delayable`, `delay_not_under_binder`, `sync_not_under_binder`, `first_tick_undefined_without_init`], [`Experiments/PolyAlternatives`, `Surface/UnitDomain`, `Experiments/ReactiveAlternatives`],
  [Thm 12], [`Ev.tag_provenance`, `temporal_state_preserves_semantic_identity`], [`Core/Reactive`],
  [§6.5], [`unfolds_preserves_eval`, `Ev.pure`, `Ev.env_irrelevant`, `Ev.noClo`], [`Core/Reactive`],
  [Prop 13], [`delay_is_sync_own`, `clocked_delay_iff_sync_own`, `single_domain_embedding`], [`Core/Clock`],
  [Thm 14], [`MEv.det`, `mfundamental`, `multi_domain_total`, `mevalF_sound`, `MEv.tag_provenance`], [`Core/Clock`],
  [Thm 15], [`scheduling_order_observable`, `equal_rate_not_same_domain`, `clocked_type_forces_polymorphism`], [`Experiments/ClockAlternatives`],
  [Thm 16], [`buffer_window_correspondence`, `buffer_from_log_and_cursor`, `bounded_summary_not_lossless`, `lossless_iff_injective`], [`Surface/Buffer`, `Core/Clock`, `Experiments/BufferAlternatives`],
  [§7.1], [`fold_total`, `mfold_total`, `fold_spec`], [`Core/Reactive`, `Core/Clock`, `Surface/Stdlib`],
  [§7.1], [`church_fst_rank`, `church_pair_prenex_one_projection`, `Value.beq_iff`, `Cap.eq_iff_data`, `lt_only_on_quantities`], [`Experiments/PolyAlternatives`, `Surface/Generic`, `Surface/Poly`, `Experiments/EquationExamples`],
  [§7.2], [`matchTy_sound`, `matchTy_complete`, `Scheme.instantiate_sound`, `generic_preserves_identity`, `lib_expansion`], [`Surface/Poly`, `Surface/Generic`, `Surface/Stdlib`],
  [Thm 17], [`single_driver_output_deterministic`, `multiple_direct_drivers_rejected`, `hidden_arbitration_observable`, `first_output_binding_is_monotone`], [`Core/Output`, `Experiments/OutputAlternatives`],
  [§8], [`driver_is_unit_domain`, `unit_codomain_collapse`, `consumers_indistinguishable`, `eval_independent_of_drives`], [`Surface/UnitDomain`],
  [Prop 18], [`HasType.rename`, `Satisfies.rename`, `Clocked.rename`], [`Behavior/Rename`],
  [Thm 19], [`inst_decl_disjoint`, `binding_satisfies`, `flatten_WF`, `flatten_causal`, `flatten_wellClocked`, `flatten_singleDriver`, `open_port_stays_open`], [`Behavior/Instantiate`, `Behavior/Preservation`],
  [Thm 20], [`eval_flat_to_inst`, `eval_inst_to_flat`, `modular_iff_flat`, `substitute_composeWF`], [`Behavior/Semantics`, `Behavior/Substitution`],
  [§9.3], [`group_is_identity_on_design`, `socket_no_fanout`, `restrict_realizes`, `system_composeWF`, `flat_WF`, `flat_causal`, `private_unobservable`, `orig_iff_flat`], [`Behavior/Group`, `Behavior/Boundary`, `Behavior/Extract`, `Behavior/ExtractPreservation`],
)
]
```
