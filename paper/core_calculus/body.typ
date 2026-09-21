#heading(level: 1, numbering: none)[Abstract]
<abstract>
When the behavior of an interactive physical product is designed, the
designer often knows #emph[that] one product quantity determines another
before knowing #emph[how]: a lamp's brightness follows its tilt, and
other parts of the design can be built on that relationship long before
its formula is chosen. This paper presents $lambda_(upright(B D L))$,
the core calculus of the Behavior Design Language, in which a typed
semantic relationship is the primary design object. A relationship is a
persistent declaration --- a stable identity, a signature between
nominal #emph[concepts], a growable set of public commitments --- that
may exist and be depended upon while its realization is absent; a
realization, when it arrives, #emph[refines] the declaration rather than
replacing it. The calculus gives this intermediate design state a
precise semantics and proves that design progression respects it:
refining a declaration preserves every client's typing unconditionally
and every client's discharged commitment under a monotonicity condition
on evidence that a mechanized counterexample shows necessary. Nominal
concepts keep a relationship between #emph[meanings] distinct from a
relationship between the representations those meanings share, and a
realization may construct only the concepts its own signature announces,
so that realization cannot silently cross a semantic boundary the
designer did not draw. Because relationships in a physical product hold
over time, the calculus interprets declarations as streams in authored
clock domains with one temporal primitive, and is deterministic and
total on causal designs without exposing any scheduler order; because a
computed value is not yet an effect, a relationship reaches the world
only through an explicit drive edge with a single driver. Reusable
behavior is a structured set of relationships instantiated by renaming,
and composition adds no semantic machinery. All definitions, theorems
and counterexamples are mechanized in Lean 4 with no `sorry` and no
classical choice.

#strong[Keywords:] design calculi, refinement, nominal types, reactive
semantics, clock domains, logical relations, mechanized metatheory, Lean
4

= Introduction
<introduction>
Consider a designer working out the behavior of a tilt-dimmed lamp.
Early in the work they know five things that are not yet code.
Brightness depends on tilt --- a relationship whose formula is undecided
and may stay undecided for weeks. Other parts of the design already rest
on that relationship: the light is driven by it, a warming base reads
it, a second lamp will reuse it. When the formula does arrive, it must
not retroactively change what the earlier declaration meant to those
parts. A tilt and a motor angle are both angles, and a brightness and an
opacity are both numbers between zero and one, yet the relationship
#emph[tilt to brightness] is not the relationship #emph[motor angle to
brightness], and no formula should be able to turn one into the other by
accident. And the relationship will eventually hold over time, in a
timing domain, and move a physical light --- facts that must attach to
it without collapsing the design into its implementation.

The first of these is the one that a programming-language presentation
handles least naturally. In a functional language, writing

$ f : A arrow.r B $

is normally the first line of a definition; the signature anticipates,
and is soon accompanied by, a computation $f thin x = dots.h$. The
signature has meaning on its own --- it is checked, it documents, it
constrains --- but the object being authored is the function. In the
design workflow above, the first line alone is already the artifact.
`dimByTilt : Tilt -> Brightness` states that a relationship exists, what
it connects, and which semantic boundary it draws; it says nothing about
how the relationship is computed, and the designer has not yet decided.
This is not an unfinished program. It is a complete design commitment at
one level of detail, deliberately left open at the next.

This paper is about giving that state a semantics. We present
$lambda_(upright(B D L))$, the core calculus of the Behavior Design
Language (BDL), a language for designing the behavior of interactive
physical products. Its organizing thesis is #strong[relation before
realization]: the primary authored object is a typed semantic
relationship, represented in the calculus as a #emph[persistent
declaration] with a stable identity, a signature, and public
commitments; a computation is one possible #emph[realization] of that
relationship, supplied later as a refinement. The calculus exists to
make the intermediate state --- declared, typed, depended upon,
unrealized --- typable, referenceable, composable, refinable, stable for
its clients, and eventually realizable, without pretending that the
computation already exists.

We are careful about what this claim is. Existing mechanisms provide
every piece of the story: module signatures separate interface from
implementation; abstract types hide representations; refinement and
contract systems attach progressively stronger constraints; synchronous
languages interpret definitions as clocked streams.
$lambda_(upright(B D L))$ does not show that any of these cannot express
a declared-but-unrealized relationship. What it contributes is a direct,
compositional semantics for a workflow in which #emph[concept identity,
interface commitment, delayed realization, temporal structure and
physical effect coexist as facts about one object], together with
mechanized proofs that they interact as the workflow needs. A
relationship is representationally a declaration in an environment,
referred to by identity from terms; it is a first-class #emph[design]
object, not a first-class value that terms pass around, and the paper
says so wherever the distinction matters.

== One object, six constraints
<one-object-six-constraints>
A likely first reaction to the calculus is that it bundles unrelated
mechanisms --- a refinement order, nominal types, dimensions, clocks,
output bindings, renaming. The answer that organizes this paper is that
each is a constraint on the same object:

- #strong[Refinement] governs how a relationship acquires commitments
  and a realization (§4). The refinement order is the mathematical form
  of design progression, and the stability theorems say that progress
  does not destroy the meaning of earlier decisions.
- #strong[Nominal concepts and the construction grant] govern #emph[what
  meanings] a relationship connects and #emph[what] a realization is
  authorized to produce (§5). Representation is not meaning; a
  signature's result concept is the only concept its realization may
  construct.
- #strong[Dimensions] govern the arithmetic of representations once a
  concept is observed, and are orthogonal to concept identity (§5.3).
- #strong[Clock domains] govern #emph[when] a relationship's value
  belongs to the design (§6). A relationship participates in an authored
  temporal structure, and the semantics must respect it without exposing
  a scheduler.
- #strong[Outputs] govern when a relationship's value becomes physical
  effect (§8). A computed value is not an effect; the drive edge is
  where the design meets the world, once per output.
- #strong[Composition] governs how relationship structures are reused
  (§9). A behavior is a structured set of relationships; instantiation
  renames, binding connects, and flattening shows that nothing new is
  needed.

The same choice recurs on three of these axes: identity is nominal ---
of a concept, of a clock domain, of an output --- and crossing an
identity is always a visible artifact (a declared relationship, a
transport with an initial value, a drive edge), never a coercion the
implementation performs on the designer's behalf.

== Contributions
<contributions>
The contributions, in the order the paper develops them, each answer a
design question with a formal mechanism and a theorem.

+ #strong[Relationship-first declarations and refinement] (§2, §4). A
  design is an environment of declarations each of which may lack a
  realization; typing reads declarations through their signatures only.
  The refinement order (add a commitment, supply a realization,
  strengthen a realized interface with re-verification) formalizes
  progressive commitment. Theorem 3 shows that a client typed against a
  relationship before its realization is typed after it, with no
  hypothesis; Theorem 4 shows that a client's discharged commitments
  survive refinement when the validation layer's evidence is monotone in
  the environment; Theorem 5 is a mechanized counterexample showing the
  condition necessary.
+ #strong[Semantic integrity of realizations] (§5). A relationship
  connects concepts, not representations. Nominal concept types with
  write-once representation bindings keep `Tilt -> Brightness` distinct
  from `MotorAngle -> Brightness`\; the construction grant, derived from
  the declaration's own signature, is the authority a realization has to
  produce a concept (Theorem 7); erasure to representations is sound,
  and no evaluation, memory or transport creates a concept tag (Theorem
  12).
+ #strong[Temporal interpretation of relationships] (§6). Declarations
  are interpreted as streams in nominal clock domains with one temporal
  primitive --- read a domain at its last activation strictly before
  now. Evaluation is deterministic (Theorems 9, 14) and total on causal
  designs by a tick-indexed logical relation (Theorems 11, 14); the
  strictly-before rule keeps the scheduler unobservable, and its
  alternative is mechanically shown to expose it (Theorem 15).
+ #strong[Derived rather than primitive design structure] (§7). Lists,
  products and one recursor suffice for the collection equations a
  designer writes, and the lossless cross-domain window --- the
  construction most likely to be proposed as a primitive --- is five
  declarations over memory, transport and lists, correct for every
  schedule (Theorem 16).
+ #strong[Explicit physical effect] (§8). A relationship becomes effect
  only through a drive edge to a nominally identified output with a
  single driver; the physical output is then a function of the tick
  (Theorem 17), and hidden arbitration is shown to make three outputs
  from one design.
+ #strong[Compositional reuse] (§9). Components, instances and bindings
  are derived from renaming and realization; the flattened composition
  is an ordinary design accepted by the unchanged judgments (Theorem
  19), and modular and flat evaluation agree on a stated fragment
  (Theorem 20).
+ #strong[Mechanization.] Every definition, theorem and counterexample
  is a Lean 4 declaration in `KCN-judu/BDL_FV` @moura2021lean\; the
  development has no `sorry`, uses only propositional extensionality and
  quotient soundness (through function extensionality), and no classical
  choice. Each result is cited by its Lean name where it is stated;
  Appendix A indexes them.

Two conventions bound every claim. #emph[Minimal] means minimal among
the alternatives that were formalized and refuted, never a minimality
theorem. Where a theorem holds for a fragment, the fragment is part of
the statement. The paper is not about the surface language, the
authoring environment, the toolchain, hardware validation or deployment,
all of which live above the kernel and are described in the BDL
monograph of which this paper is the formal core; and it makes no claim
about designers --- that a workflow is well served by this semantics is
an empirical question no theorem here addresses.

= The design problem
<the-design-problem>
== A relationship as a design object
<a-relationship-as-a-design-object>
We fix vocabulary for the rest of the paper. A #strong[relationship] is
the design-level commitment: #emph[brightness follows tilt]. A
#strong[declaration] is the formal object that represents it --- a
stable identity $delta$, an #strong[interface] (the relationship's
public promise: an expected type between concepts and a list of
commitments), and an optional #strong[realization] (a computation
implementing the promise). #strong[Refinement] is the progressive
strengthening of a declaration --- more commitments, then a realization,
then stronger commitments re-verified --- under which clients that
relied on the earlier state remain valid. A #strong[design] is an
environment of declarations. In the Lean development a declaration
without a realization is `unresolved`\; the paper says
#emph[unrealized], because the word matters: nothing is missing from
such a declaration. Its identity, its concepts, its commitments and,
later, its timing domain and output are all present. What is postponed
is the computation, and postponing it is the designer's decision.

Three kinds of declaration will appear. A relationship with inputs,
`dimByTilt : Tilt -> Brightness`, has an arrow signature. A relationship
with no inputs, `light : Brightness`, is a value the design computes.
And a declaration that will #emph[never] receive a realization,
`tilt : Tilt`, is an #emph[input]: a relationship the environment
realizes, whose value the product reads. The kernel distinguishes none
of these by kind; all are declarations, and the last two differ only in
whether a realization is present. That an input is "a relationship
realized by the world" is not a metaphor here --- it is exactly how the
semantics of §6 reads it.

In type-theoretic terms the whole design state is a #emph[global
environment] of named constants, and that is the vocabulary the rest of
the paper uses. A #strong[concept] is a #emph[nominal base type]: a type
constant $C$, distinct from every other by name, whose values are formed
by an injection $upright("sem") thick C$ from a representation type $R$
that the environment $Theta$ binds to it --- an abstract type with a
private constructor (§5). A #strong[declaration] is a #emph[typed
constant] $delta : tau$ in the global environment $Delta$, with an
optional #emph[definiens]: exactly a proof assistant's `Parameter`
before its `Definition`, except that here the parameter state is the
normal one and giving the definiens is the design step. A declaration of
base type, $delta : upright("sem") thick C$, is one #emph[inhabitant] of
the concept --- one value at each tick --- and its definiens, when
present, is the one term that produces that value; a declaration without
a definiens is an #emph[axiom] the environment discharges (the product's
#emph[Source]). A declaration of function type is a template applied
wherever another definiens names it. Several constants of one base type
are ordinary (`sensorA : Temperature`, `sensorB : Temperature`,
`roomTemp : Temperature := if available then sensorA else sensorB`); a
term refers to a constant by name and never to a type, so nothing is
ever resolved "by concept". The product speaks the same ladder as
#emph[concept] (the type), #emph[Sem block] (a constant of concept type,
holding one value) and #emph[mapping block] (its definiens); the
calculus needs only #emph[type], #emph[constant] and #emph[definiens],
and it keeps the product's word #emph[relationship] for a constant read
as a design object.

== Unrealized but usable
<unrealized-but-usable>
The claim that an unrealized declaration is a complete design state is
only worth making if the state is #emph[usable]. In
$lambda_(upright(B D L))$ it is. Let the design $Delta_0$ contain

$ italic(d i m B y T i l t) = chevron.l delta_1\,med chevron.l upright("sem") thick upright("Tilt") arrow.r upright("sem") thick upright("Brightness")\,med\[thin\]chevron.r\,med upright("none") chevron.r\,\
italic(t i l t) = chevron.l delta_2\,med chevron.l upright("sem") thick upright("Tilt")\,med\[thin\]chevron.r\,med upright("none") chevron.r\, $

and let the designer now declare and #emph[realize] the light:
$ italic(l i g h t) = chevron.l delta_3\,med chevron.l upright("sem") thick upright("Brightness")\,med\[thin\]chevron.r\,med upright("some") thick\(\(upright("declRef") thick delta_1\)thick\(upright("declRef") thick delta_2\)\)chevron.r . $
The realization of `light` is well typed in $Delta_0$, by T-Ref twice
--- using only
$Delta_0^(upright(t y))\(delta_1\)= upright("some") thick\(upright("sem") thick upright("Tilt") arrow.r upright("sem") thick upright("Brightness")\)$
and
$Delta_0^(upright(t y))\(delta_2\)= upright("some") thick\(upright("sem") thick upright("Tilt")\)$
--- and T-App once:
$ upright("(T-Ref)") & Theta\;Delta_0\;G\;\[thin\]tack.r upright("declRef") thick delta_1 : upright("sem") thick upright("Tilt") arrow.r upright("sem") thick upright("Brightness")\
upright("(T-Ref)") & Theta\;Delta_0\;G\;\[thin\]tack.r upright("declRef") thick delta_2 : upright("sem") thick upright("Tilt")\
upright("(T-App)") & Theta\;Delta_0\;G\;\[thin\]tack.r\(upright("declRef") thick delta_1\)thick\(upright("declRef") thick delta_2\): upright("sem") thick upright("Brightness") $

The derivation consults $Delta_0$ only through the #emph[type view]
$Delta^(upright(t y))$ --- the expected type of each declared identity
--- and never asks whether $delta_1$ has a realization. `light` is a
well-formed, typed, referenceable part of the design while `dimByTilt`
has no formula. This is the calculus's thesis made formal, and the
theorem that completes it is stated in §4: when `dimByTilt` is later
realized, or given a commitment, every judgment about `light` in
$Delta_0$ holds in the refined design (Theorem 3). The client did not
depend on a body, so no body can invalidate it.

== Design progression as refinement
<design-progression-as-refinement>
The running example progresses through eight commitments, in the order a
designer might make them; each is a step in the calculus and each is
taken up in a later section.

#figure(
  align(center)[#table(
    columns: (25%, 25%, 25%, 25%),
    align: (auto,auto,auto,auto,),
    table.header([step], [the designer commits to], [the calculus
      records], [§],),
    table.hline(),
    [1], [a relationship `dimByTilt : Tilt -> Brightness` exists], [an
    unrealized declaration with that signature], [2.2, 4],
    [2], [`light` is what `dimByTilt` yields for the current tilt], [a
    realized declaration referring to `dimByTilt` by identity], [2.2],
    [3], [`Tilt` is represented by an angle, `Brightness` by a
    scalar], [write-once bindings in the concept environment
    $Theta$], [5],
    [4], [a formula for `dimByTilt`], [a realization, typed under the
    grant of its own signature], [4, 5],
    [5], [`dimByTilt` promises `monotone`], [a commitment, with evidence
    re-verified], [4],
    [6], [`light` updates with the interaction, in domain `fast`], [a
    clock assignment and the domain judgment], [6],
    [7], [the lamp's LED shows `light`], [a drive edge to an output with
    a single driver], [8],
    [8], [a second lamp reuses the whole behavior], [a component
    instantiated by renaming and bound], [9],
  )]
  , kind: table
  )

#emph[Table 1. The running example as progressive commitment.]

Conceptually, a design before all its realizations are chosen describes
a constrained family of completed behaviors, and each step narrows the
family: a commitment excludes realizations that lack the property, a
realization fixes one computation, a clock assignment fixes when values
are observed, a drive edge fixes what the product does. We use this
reading as motivation only. The calculus does not denote a set of
possible products; what it has is a #emph[refinement relation] on
declarations and environments (§4.2), and the theorems are about that
relation --- one direction of progressive commitment, from less
determined to more. Steps that do not narrow --- changing a signature,
dropping a commitment, replacing a realization --- are #emph[edits], and
the calculus promises nothing about them (§4.4).

= The calculus
<the-calculus>
The term language of $lambda_(upright(B D L))$ is a simply typed
λ-calculus with registered first-order operators. What makes it a
calculus of relationships rather than of functions is not its terms but
the environments they are typed and evaluated against, and the
projections through which each judgment may read them. This section
fixes the syntax, the environments and the typing judgment; the design
content of each environment is developed in the sections that follow.

== Syntax
<syntax>
Figure 1 gives the syntax. Types are those of a simply typed calculus
with booleans, counts and arrows, extended by nominal concept types
$upright("sem") thick C$ over an identity $C$, physical quantities
$upright("q") thick d$ over a dimension $d$, and the data formers
$upright("opt")$, $upright("list")$ and $times$. A dimension is an
exponent vector over a fixed finite set of base dimensions (length,
time, angle, mass, temperature in the development); dimensions form an
abelian group under pointwise addition, which is the only structure the
calculus uses.

$  & C in upright("ConceptId") #h(2em) d in upright("Dim") #h(2em) kappa in upright("ClockId") #h(2em) delta in upright("DeclId") #h(2em) o in upright("OutputId")\
tau\,sigma thick upright("::=") thick & upright("bool") divides upright("nat") divides tau arrow.r sigma divides upright("sem") thick C divides upright("q") thick d divides upright("opt") thick tau divides upright("list") thick tau divides tau times sigma\
e thick upright("::=") thick & x divides upright("true") divides upright("false") divides n divides lambda x : tau . thin e divides e thick e divides upright("declRef") thick delta divides upright("rep") thick e divides upright("mk") thick C thick e divides p\
divides thick & upright("delay") thick e thick e divides upright("sync") thick kappa thick e thick e divides upright("fold") thick e thick e thick e\
p thick upright("::=") thick & upright("lit")_d thin n divides upright("add")_d divides upright("sub")_d divides upright("mul")_(d_1 d_2) divides upright("div")_(d_1 d_2) divides upright("lt")_d divides upright("eq")_tau^(italic(p f)) divides not divides and divides or divides upright("ite")_tau\
divides thick & upright("none")_tau divides upright("some")_tau divides upright("isSome")_tau divides upright("getD")_tau divides upright("nil")_tau divides upright("cons")_tau divides upright("length")_tau divides upright("take")_tau divides upright("drop")_tau divides upright("reverse")_tau divides upright("head")_tau\
divides thick & upright("toList")_tau divides upright("pair")_(tau sigma) divides upright("fst")_(tau sigma) divides upright("snd")_(tau sigma) $

#emph[Figure 1. Syntax of $lambda_(upright(B D L))$. Variables are de
Bruijn indices in the development; the paper writes names. $italic(p f)$
in $upright("eq")_tau^(italic(p f))$ is a proof that $tau$ is a data
type.]

#emph[Notation.] Each letter is bound once, where its object first
appears, and is never rebound: $C$ a concept (a nominal type, the level
of $upright("ConceptId")$), $delta$ a declaration identity and $h$ a
declaration record (§3.2), $v\,w$ values --- a value of concept $C$ is
$upright("sem") thick C thick v$ (§6) --- $kappa$ a clock domain
(lowercase $c$ is avoided, so that no letter reads as an instance of the
concept $C$), $o$ an output, $d$ a dimension, $tau\,sigma$ types, $R$ a
representation (a concept-free data type), $e\,b$ terms, $x$ variables,
$t$ a tick, $p$ a property. Environments: $Theta$ concepts, $Delta$ the
design, $G$ the grant, $Gamma$ the context, $upright(K)$ clocks, $S$ the
schedule, $I$ the input, $rho$ the evaluation environment, $Omega$
outputs and $beta$ drive edges (§3.2, §8);
$cal(P) = chevron.l tau\,cal(K) chevron.r$ an interface with its
commitment list (§4), $italic(e v)$ evidence, $eta$ an erasure (§5.2),
$cal(C)$ a component and $k$ an instance index (§9). The ladder of §2
reads, in these letters: $R$ is the type of a type, $C$ is a type, $h$
(named $delta$) is one instance holding one $v$ per $t$.

Terms are those of the λ-calculus plus five design-specific forms.
$upright("declRef") thick delta$ refers to a relationship by the
identity of its declaration; nothing about the declaration's interface
or realization is in the syntax, which is what lets a term refer to a
relationship that has no realization yet. $upright("rep") thick e$
observes the representation of a concept value and
$upright("mk") thick C thick e$ constructs one.
$upright("delay") thick i thick e$ is the value of $e$ at the previous
activation of the current domain, $i$ before any;
$upright("sync") thick kappa thick i thick e$ is the value of $e$ in
domain $kappa$ at $kappa$'s last activation strictly before now, $i$ if
none. $upright("fold") thick f thick z thick l$ is the list recursor,
$upright("fold") thick f thick z thick\[x_1\,dots.h\,x_n\]= f thick x_1 thick\(dots.h.c\(f thick x_n thick z\)\)$.
Registered operators $p$ are first-order constants with types; they
never apply a closure.

Two predicates on types recur. A type is #strong[data],
$tau . upright("Data")$, when no arrow occurs in it; a type is
#strong[concept-free], $tau . upright("SemFree")$, when no
$upright("sem")$ occurs in it. Both are decidable by structural
recursion, and
$\(tau times sigma\). upright("Data") arrow.l.r.double tau . upright("Data") and sigma . upright("Data")$,
$\(upright("list") thick tau\). upright("Data") arrow.l.r.double tau . upright("Data")$
hold definitionally (`Ty.prod_data`, `Ty.list_data`).

== Environments
<environments>
A term is typed and evaluated against several environments, each read
through a stated projection and nothing else. This discipline ---
#emph[which environment a judgment may see] --- is what the stability
results of §4 rest on: a client sees a relationship's signature and
never its realization, so the realization can change without the client
noticing.

- A #strong[declaration] is a triple
  $ upright("DesignDecl") = chevron.l thin italic(i d) : upright("DeclId")\,med italic(i n t e r f a c e) : chevron.l italic(e x p e c t e d T y p e) : upright("Ty")\,med italic(c o m m i t m e n t s) : upright("PropertyId")^(*) chevron.r\,med italic(r e a l i z a t i o n) : upright("Option") thick upright("Expr") thin chevron.r . $
  A #strong[design] is a declaration environment
  $Delta : upright("DeclId") arrow.r upright("Option") thick upright("DesignDecl")$.
  Its #emph[type view]
  $Delta^(upright(t y))\(delta\)=\(Delta thick delta\). upright("map")\(dot.op . italic(i n t e r f a c e) . italic(e x p e c t e d T y p e)\)$
  is all that typing sees; its #emph[realization view]
  $Delta^(upright(r e a l))\(delta\)=\(Delta thick delta\). upright("bind")\(dot.op . italic(r e a l i z a t i o n)\)$
  is all that evaluation sees. An #strong[unrealized] declaration is one
  whose realization is $upright("none")$\; nothing else distinguishes
  it. - A #strong[concept environment]
  $Theta : upright("ConceptId") arrow.r upright("Option") thick upright("Ty")$
  binds each concept to a representation. It is well formed,
  $Theta . upright("WF")$, when every bound representation is
  concept-free and data:
  $Theta thick C = upright("some") thick R arrow.r.double R . upright("SemFree") and R . upright("Data")$.
- A #strong[grant] $G : upright("ConceptId") arrow.r upright("Prop")$
  says which concepts a term may construct. $upright("Grant.none")$
  permits nothing; $upright("Grant.of") thick tau$ permits the concepts
  in result position of $tau$,
  $upright("grant")\(upright("sem") thick C\)=\[C\]$,
  $upright("grant")\(tau arrow.r sigma\)= upright("grant")\(sigma\)$,
  $upright("grant")\(\_\)=\[thin\]$.
- A #strong[clock environment]
  $upright(K) : upright("DeclId") arrow.r upright("Option") thick upright("ClockId")$
  assigns each declaration a domain; $upright("none")$ marks a
  domain-agnostic relationship usable in any domain. A #strong[schedule]
  $S : upright("ClockId") arrow.r bb(N) arrow.r upright("Bool")$ says at
  which global ticks each domain activates. An #strong[input]
  $I : upright("DeclId") arrow.r bb(N) arrow.r upright("Value")$
  supplies a value for every unrealized declaration at every tick ---
  the environment's realization of the design's inputs.
- An #strong[output environment]
  $Omega : upright("OutputId") arrow.r upright("Option") thick chevron.l italic(a c c e p t s) : upright("Ty")\,italic(c l o c k) : upright("ClockId") chevron.r$
  and the #strong[drive edges]
  $beta : upright("DeclId") arrow.r upright("Option") thick upright("OutputId")$
  are introduced in §8.

Typing sees $Theta$, $Delta^(upright(t y))$ and $G$. Evaluation sees
$Delta^(upright(r e a l))$, $I$ and (in several domains) $S$. The domain
judgment sees $upright(K)$. Outputs see $Omega$, $upright(K)$,
$Delta^(upright(t y))$ and $beta$. Commitments and evidence are seen by
the satisfaction relation of §4 and by nothing else.

== Typing
<typing>
The typing judgment $Theta\;Delta\;G\;Gamma tack.r e : tau$ is given in
Figure 2. Rules T-Var, T-Bool, T-Nat, T-Lam and T-App are those of the
simply typed λ-calculus. T-Ref is the only rule that reads $Delta$, and
it reads the type view. T-Rep and T-Mk read $Theta$ through the binding
$Theta thick C = upright("some") thick R$\; T-Mk additionally requires
the grant. T-Prim assigns each registered operator its type; the
dimension algebra is entirely in that table (Figure 3), so an
application of $upright("mul")_(d_1 d_2)$ is checked by T-App like any
other. T-Delay and T-Sync require the type to be data and the context to
be empty; T-Fold types the recursor.

$ frac(Gamma\(x\)= tau, Theta\;Delta\;G\;Gamma tack.r x : tau) med upright("(T-Var)") #h(2em) frac(, Theta\;Delta\;G\;Gamma tack.r b : upright("bool")) med upright("(T-Bool)") #h(2em) frac(, Theta\;Delta\;G\;Gamma tack.r n : upright("nat")) med upright("(T-Nat)") $

$ frac(Theta\;Delta\;G\;Gamma\,x : tau tack.r e : sigma, Theta\;Delta\;G\;Gamma tack.r lambda x : tau . thin e : tau arrow.r sigma) med upright("(T-Lam)") #h(2em) frac(Theta\;Delta\;G\;Gamma tack.r f : tau arrow.r sigma quad Theta\;Delta\;G\;Gamma tack.r a : tau, Theta\;Delta\;G\;Gamma tack.r f thick a : sigma) med upright("(T-App)") $

$ frac(Delta^(upright(t y))\(delta\)= upright("some") thick tau, Theta\;Delta\;G\;Gamma tack.r upright("declRef") thick delta : tau) med upright("(T-Ref)") #h(2em) frac(, Theta\;Delta\;G\;Gamma tack.r p : upright("ty")\(p\)) med upright("(T-Prim)") $

$ frac(Theta thick C = upright("some") thick R quad Theta\;Delta\;G\;Gamma tack.r e : upright("sem") thick C, Theta\;Delta\;G\;Gamma tack.r upright("rep") thick e : R) med upright("(T-Rep)") #h(2em) frac(G thick C quad Theta thick C = upright("some") thick R quad Theta\;Delta\;G\;Gamma tack.r e : R, Theta\;Delta\;G\;Gamma tack.r upright("mk") thick C thick e : upright("sem") thick C) med upright("(T-Mk)") $

$ frac(tau . upright("Data") quad Theta\;Delta\;G\;\[thin\]tack.r i : tau quad Theta\;Delta\;G\;\[thin\]tack.r e : tau, Theta\;Delta\;G\;\[thin\]tack.r upright("delay") thick i thick e : tau) med upright("(T-Delay)") $

$ frac(tau . upright("Data") quad Theta\;Delta\;G\;\[thin\]tack.r i : tau quad Theta\;Delta\;G\;\[thin\]tack.r e : tau, Theta\;Delta\;G\;\[thin\]tack.r upright("sync") thick kappa thick i thick e : tau) med upright("(T-Sync)") $

$ frac(Theta\;Delta\;G\;Gamma tack.r f : tau arrow.r sigma arrow.r sigma quad Theta\;Delta\;G\;Gamma tack.r z : sigma quad Theta\;Delta\;G\;Gamma tack.r l : upright("list") thick tau, Theta\;Delta\;G\;Gamma tack.r upright("fold") thick f thick z thick l : sigma) med upright("(T-Fold)") $

#emph[Figure 2. Typing (`HasType`). T-Ref is the only rule reading
$Delta$\; T-Rep and T-Mk the only rules reading $Theta$\; T-Mk the only
rule reading $G$.]

#figure(
  align(center)[#table(
    columns: (25%, 25%, 25%, 25%),
    align: (auto,auto,auto,auto,),
    table.header([operator], [type], [operator], [type],),
    table.hline(),
    [$upright("lit")_d thin n$], [$upright("q") thick d$], [$upright("eq")_tau^(italic(p f))$], [$tau arrow.r tau arrow.r upright("bool")$],
    [$upright("add")_d\,med upright("sub")_d$], [$upright("q") thick d arrow.r upright("q") thick d arrow.r upright("q") thick d$], [$upright("ite")_tau$], [$upright("bool") arrow.r tau arrow.r tau arrow.r tau$],
    [$upright("mul")_(d_1 d_2)$], [$upright("q") thick d_1 arrow.r upright("q") thick d_2 arrow.r upright("q") thick\(d_1 + d_2\)$], [$upright("some")_tau$], [$tau arrow.r upright("opt") thick tau$],
    [$upright("div")_(d_1 d_2)$], [$upright("q") thick d_1 arrow.r upright("q") thick d_2 arrow.r upright("q") thick\(d_1 - d_2\)$], [$upright("getD")_tau$], [$upright("opt") thick tau arrow.r tau arrow.r tau$],
    [$upright("lt")_d$], [$upright("q") thick d arrow.r upright("q") thick d arrow.r upright("bool")$], [$upright("toList")_tau$], [$upright("opt") thick tau arrow.r upright("list") thick tau$],
    [$upright("length")_tau$], [$upright("list") thick tau arrow.r upright("q") thick 0$], [$upright("cons")_tau$], [$tau arrow.r upright("list") thick tau arrow.r upright("list") thick tau$],
    [$upright("head")_tau$], [$upright("list") thick tau arrow.r upright("opt") thick tau$], [$upright("take")_tau\,med upright("drop")_tau$], [$upright("q") thick 0 arrow.r upright("list") thick tau arrow.r upright("list") thick tau$],
    [$upright("fst")_(tau sigma)$], [$tau times sigma arrow.r tau$], [$upright("pair")_(tau sigma)$], [$tau arrow.r sigma arrow.r tau times sigma$],
  )]
  , kind: table
  )

#emph[Figure 3. Types of the registered operators (`Prim.ty`), abridged.
Dimension algebra lives here and nowhere else. $upright("eq")$ is
available at every data type and $upright("lt")$ at quantities only.]

Three features of Figure 2 carry the rest of the paper.

#emph[The typing boundary.] Typing depends on the type view of
declarations and the representation view of concepts and on nothing else
--- not on realizations, commitments, evidence, clocks or drive edges.
This is the formal content of #emph[relation before realization]: a
reference is typed by the relationship's promise, and the stability of
clients under later realization (Theorem 3) is a direct consequence.

#emph[The construction boundary.] Client code is typed under
$upright("Grant.none")$\; a declaration's realization is typed under
$upright("Grant.of")$ its own expected type (§4.1). A value of
$upright("sem") thick C$ is therefore constructed only inside a
declaration whose signature announces $upright("sem") thick C$: the
signature is the realization's authority, and §5 shows what each weaker
alternative admits.

#emph[The temporal boundary.] $upright("delay")$ and $upright("sync")$
are typed only in the empty context and only at data types. Both
restrictions were forced by the totality proof of §6, not chosen: a
delayed closure would have to be transported across ticks, and a delay
under a binder would re-evaluate its operand at the previous tick in an
environment created at the current one. Temporal state therefore belongs
to declarations --- memory is a property of a relationship, not of a
function --- and relationships with inputs are pointwise --- the
arrangement of `pre` in Lustre, where it lives in nodes rather than in
functions @halbwachs1991lustre.

== Inference, uniqueness and monotonicity
<inference-uniqueness-and-monotonicity>
Inference is syntax-directed. A function
$upright("infer") thick Theta thick Delta thick G thick Gamma thick e : upright("Option") thick upright("Ty")$
follows the rules of Figure 2 and needs only decidability of $G$, of
type equality and of $tau . upright("Data")$.

#strong[Proposition 1 (Inference; `infer_sound`, `infer_complete`,
`HasType.unique`).]
$upright("infer") thick Theta thick Delta thick G thick Gamma thick e = upright("some") thick tau$
iff $Theta\;Delta\;G\;Gamma tack.r e : tau$\; hence typing is decidable
and every term has at most one type.

Uniqueness matters beyond decidability: it is why the surface language's
polymorphism can be #emph[matching] rather than unification (§7.2), and
why a nominal mismatch is reported as "Brightness and Opacity are
different concepts" and never as a unification residue. Typing is
moreover monotone in each of its three environments --- under
environment refinement (§4.2), under binding more concepts, and under a
larger grant (`HasType.mono_env`, `HasType.mono_concept`,
`HasType.mono_grant`); each monotonicity is one direction of progressive
commitment.

Weakening holds for the delay-free fragment by appending to the context
(`HasType.weaken_append`); a stateful term cannot be moved under a
binder at all, so no stronger weakening is needed.

= Progressive realization
<progressive-realization>
A declaration evolves: it is declared with a signature, it acquires
commitments, it acquires a realization, its commitments are
strengthened. Throughout, other declarations refer to it. This section
gives design progression its mathematical form --- a #emph[refinement
order] generated by three steps --- and proves that progression
preserves what was established before it: clients typed against a
relationship stay typed (Theorem 3), and clients whose commitments were
discharged through it stay discharged, provided the validation layer's
evidence is monotone (Theorem 4), a proviso that Theorem 5 shows cannot
be dropped.

== Interfaces, evidence and satisfaction
<interfaces-evidence-and-satisfaction>
An interface $cal(P) = chevron.l tau\,cal(K) chevron.r$ is the
relationship's public promise: an expected type and a list of
commitments --- atomic labels such as `total`, `monotone`, `bounded`
that a client may rely on. Interfaces are ordered by monotone
refinement:
$ cal(P) subset.eq.sq cal(P)' thick := thick cal(P) . tau = cal(P)' . tau thick and thick cal(P) . cal(K) subset.eq cal(P)' . cal(K)\, $
a decidable preorder, frozen on the type and growing on commitments
(`InterfaceRefines`). Nothing else is an interface refinement.

What discharges a commitment is not the kernel's business; it is the
validation layer's. The kernel abstracts it as an #strong[evidence]
relation
$italic(e v) : upright("DeclEnv") arrow.r upright("Expr") arrow.r upright("PropertyId") arrow.r upright("Prop")$.
Evidence takes the environment because compositional discharge needs it
--- "$A$ is monotone because $B$ is committed to be monotone" consults
$B$'s interface. A realization $e$ #strong[satisfies] $cal(P)$ in
$Theta\,Delta\,Gamma$ when it has the expected type under the grant of
that type and every commitment is discharged:
$ upright("Satisfies") thick italic(e v) thick Theta thick Delta thick Gamma thick e thick cal(P) thick := thick Theta\;Delta\;upright("Grant.of")\(cal(P) . tau\)\;Gamma tack.r e : cal(P) . tau thick and thick forall p in cal(P) . cal(K) . thick italic(e v) thick Delta thick e thick p . $
A declaration is well formed when its body, if any, satisfies its
interface; a design is #strong[globally well formed],
$upright("GlobalWF") thick italic(e v) thick Theta thick Delta$, when
every stored declaration sits under its own identity and is well formed
in $Delta$ at top level. An unrealized declaration is always well
formed.

The refinement order is complete for abstract evidence:
$cal(P) subset.eq.sq cal(P)'$ iff every realization of $cal(P)'$ in
every environment under every evidence relation realizes $cal(P)$
(`InterfaceRefines_iff_semantic`). The proof of the converse
instantiates evidence at "the property is in $cal(P)'$'s list" and the
body at a reference to a single declaration.

== The refinement order and the lifecycle
<the-refinement-order-and-the-lifecycle>
Design progression is generated by three steps (`DeclRefines`), each
preserving the identity by construction and each checked against the
current environment $Delta$:
$ frac(S subset.eq.sq cal(P)', chevron.l delta\,cal(P)\,upright("none") chevron.r arrow.r.squiggly chevron.l delta\,cal(P)'\,upright("none") chevron.r) #h(2em) frac(upright("Satisfies") thick italic(e v) thick Theta thick Delta thick Gamma thick e thick cal(P), chevron.l delta\,cal(P)\,upright("none") chevron.r arrow.r.squiggly chevron.l delta\,cal(P)\,upright("some") thick e chevron.r) #h(2em) frac(S subset.eq.sq cal(P)' quad upright("Satisfies") thick italic(e v) thick Theta thick Delta thick Gamma thick e thick cal(P)', chevron.l delta\,cal(P)\,upright("some") thick e chevron.r arrow.r.squiggly chevron.l delta\,cal(P)'\,upright("some") thick e chevron.r) $
An unrealized declaration may have its interface refined; an unrealized
declaration may be realized by a satisfying computation; a realized
declaration may have its interface strengthened provided the realization
is #emph[re-verified] against the new interface. Strengthening without
re-verification breaks well-formedness, and the counterexample is
mechanized (`naive_breaks_wellformedness`).

Separately from the steps there is a purely structural order with no
satisfaction condition: $upright("DeclLeq") thick h thick h'$ requires
the same identity, $h . cal(P) subset.eq.sq h' . cal(P)$, and a
write-once realization
($h . italic(r e a l i z a t i o n) = upright("some") thick e arrow.r.double h' . italic(r e a l i z a t i o n) = upright("some") thick e$);
$upright("EnvRefines") thick Delta thick Delta'$ lifts it pointwise and
permits new declarations. Storing a refined declaration back under its
identity is an environment refinement ---
$Delta thick h . italic(i d) = upright("some") thick h and upright("DeclLeq") thick h thick h' arrow.r.double upright("EnvRefines") thick Delta thick\(Delta\[h'\]\)$
(`EnvRefines_update`) --- and this is the one place identity does any
work: it makes the update land on the slot every reference resolves to,
which is what a name does in any environment semantics.

#strong[Proposition 2 (The lifecycle is the structural order;
`DeclRefinesStar_iff`).] The reflexive--transitive closure of the three
steps, all side conditions checked in $Delta$, relates $h$ to $h'$ iff
$upright("DeclLeq") thick h thick h'$ and $h'$ is well formed in
$Delta$.

== Client stability
<client-stability>
Another part of the product may already depend on a relationship before
that relationship is realized (§2.2). Can the relationship then be
realized, or strengthened, without editing those clients and without
invalidating what was established about them? The answer has two halves
with deliberately different hypotheses, and together they are the
paper's central result: progress in the design does not destroy the
meaning of earlier design decisions.

#strong[Theorem 3 (Clients survive realization --- typing;
`local_refinement_preserves_global_typing`).] If
$Delta thick B = upright("some") thick h$ and
$upright("DeclLeq") thick h thick h'$, then every judgment
$Theta\;Delta\;G\;Gamma tack.r e : tau$ holds in $Delta\[h'\]$.

The proof is one line: typing reads $Delta$ through the type view, and
the type view is invariant under $upright("DeclLeq")$. That the proof is
short is the point, not a weakness. The theorem says that the decision
to let clients see a relationship's promise and never its realization is
#emph[sufficient] for every client to survive every realization and
every added commitment, with no side condition. It is also necessary:
change $B$'s expected type while keeping its identity and every client
breaks, which is why the type is frozen in $subset.eq.sq$ and why
changing it is an edit (§4.4).

The commitment half needs more.

#strong[Definition (Monotone evidence).] $italic(e v)$ is
#strong[monotone] when
$upright("EnvRefines") thick Delta_1 thick Delta_2 and italic(e v) thick Delta_1 thick e thick p arrow.r.double italic(e v) thick Delta_2 thick e thick p$.
Evidence that ignores the environment is monotone; evidence that
consults only the #emph[presence] of commitments and realizations is
monotone; evidence that consults their #emph[absence] is not.

#strong[Theorem 4 (Clients survive realization --- commitments;
`local_refinement_preserves_global_wf`,
`local_lifecycle_preserves_global_wf`).] If $italic(e v)$ is monotone,
$upright("GlobalWF") thick italic(e v) thick Theta thick Delta$,
$Delta thick B = upright("some") thick h$ and $h arrow.r.squiggly h'$
with side conditions checked in $Delta$, then
$upright("GlobalWF") thick italic(e v) thick Theta thick\(Delta\[h'\]\)$.
The same holds for a whole lifecycle $h arrow.r.squiggly^(*) h'$ checked
against the original $Delta$.

#strong[Theorem 5 (Monotonicity is necessary; `badEv_not_mono`).] There
is an evidence relation $italic(e v)_(upright(b a d))$, a globally well
formed two-declaration design, and a valid realization step of one
declaration after which the design is not globally well formed;
consequently $italic(e v)_(upright(b a d))$ is not monotone.

The relation $italic(e v)_(upright(b a d))$ discharges "$A$ is total"
whenever the declaration $A$ reads is still unrealized --- evidence from
absence. Realizing that declaration is a perfectly valid step, and it
destroys the discharge. The monotonicity hypothesis was not part of the
original design; it appeared when Theorem 4 was attacked, and it is a
Kripke-style stability condition imposed by the kernel on the validation
layer: any discharge mechanism meant to survive design progression must
be positive in the environment. Its design reading is direct --- a
commitment may be justified by what other relationships promise, never
by what they have not yet decided.

Binding a representation to a previously unbound concept is likewise a
refinement: typing, satisfaction and global well-formedness are monotone
in $Theta$ (`GlobalWF.of_conceptRefines`). Rebinding a concept to a
different representation is an edit that breaks existing realizations
(`representation_change_is_edit_not_refinement`).

== Refinement versus edit
<refinement-versus-edit>
Theorems 3--4 cover refinement only; they are what the calculus promises
about design progression, and the line between progression and
#emph[edit] is part of the design. Table 2 classifies the operations a
tool offers on a declaration $B$ read by a client $A$\; each row is
witnessed by a mechanized example on a two-declaration design.

#figure(
  align(center)[#table(
    columns: (33.33%, 33.33%, 33.33%),
    align: (auto,auto,auto,),
    table.header([operation on $B$], [kind], [effect on $A$],),
    table.hline(),
    [add a public commitment], [refinement], [typing and commitments
    preserved],
    [realize], [refinement], [preserved; $A$ now unfolds to a closed
    program],
    [strengthen a realized interface], [refinement, with
    re-verification], [preserved],
    [change the expected type, keep identity], [edit], [typing broken],
    [drop a commitment], [edit], [typing silent; $A$'s commitment
    broken],
    [replace $B$ by a new identity], [edit], [dangling reference],
    [detach or replace the realization], [edit], [evidence that
    consulted the body is void],
    [assign or change a clock domain (§6)], [edit], [domain judgment on
    clients broken],
    [retarget an output binding (§8)], [edit], [completeness or
    single-driver may break],
  )]
  , kind: table
  )

#emph[Table 2. Refinement versus edit.]

Two rows are instructive. Dropping a commitment changes no type, so the
type checker is silent, yet $A$'s own commitment was discharged through
$B$'s and is now unsupported: commitments are part of the interface in
the same load-bearing sense as the expected type. Detaching a
realization is an edit for the same reason: clients' typing is
unaffected, but evidence that consulted the body is void. The kernel
does not forbid edits; it declines to promise anything about them, and a
tool must reopen the validation of transitive dependents.

== Unfolding
<unfolding>
Before time enters, the semantics of a design is #emph[unfolding]:
replace each reference to a realized declaration by its realization,
recursively, stopping at unrealized declarations
($upright("Unfolds") thick Delta thick e thick e'$). Let
$upright("DependsOn") thick Delta thick a thick b$ hold when the body of
$a$ refers to $b$.

#strong[Proposition 6 (Unfolding; `Unfolds.det`,
`Unfolds.exists_of_acyclic`, `Unfolds.not_of_cyclic`,
`Unfolds.refFree_of_fullyRealized`).] Unfolding is deterministic; on the
delay-free fragment it exists iff the reference graph is acyclic; a
reference on a cycle through realized declarations has no unfolding at
all; and a fully realized well-typed design unfolds to a reference-free
program of the same type.

Acyclicity is witnessed by a rank that strictly decreases along edges,
$upright("Acyclic") thick Delta := exists thin italic(r a n k) . thick forall a thin b . thick upright("DependsOn") thick Delta thick a thick b arrow.r italic(r a n k) thick b < italic(r a n k) thick a$,
and excludes cycles (`Acyclic.not_cyclic`). The pure fragment has no
fixpoints, so a cyclic definition denotes nothing; §6 shows which cycles
become meaningful once $upright("delay")$ exists, and that unfolding
agrees with tick evaluation on the first-order fragment
(`unfolds_preserves_eval`).

= Semantic integrity
<semantic-integrity>
A relationship connects #emph[meanings].
`dimByTilt : Tilt -> Brightness` relates a product concept to a product
concept, and it is not the relationship `MotorAngle -> Brightness` even
though a tilt and a motor angle are both angles. Section 4 typed
declarations without saying what a type means; this section adds the two
things a product concept carries that a number does not --- an identity
that survives representation, and a physical dimension --- and shows
that a realization, when it arrives, is constrained to preserve the
semantic boundary the signature drew before it existed. The distinction
the section rests on is stated once: a #strong[concept] is what the
designer means, its #strong[representation] is the data it is carried
by, and the two are bound separately, later, and write-once.

== Nominal identity, and the grant as realization authority
<nominal-identity-and-the-grant-as-realization-authority>
#emph[Why not identify concepts by representation?] Suppose concepts
were represented only by their representation types, so that `Tilt` and
`MotorAngle` are both $upright("q") thick upright("Angle")$. Then the
wire `motorTarget := tiltSensor` is well typed and the design is
globally well formed, because nothing in the model records the
distinction the designer drew. Nominal types $upright("sem") thick C$
over an internal identity record it: two distinct identities are
distinct types regardless of representation, so the invalid wire is
rejected by T-App with no additional judgment. An explicit relationship
`tiltToMotor : Tilt -> MotorAngle` is an ordinary declaration of arrow
type --- signature-first, possibly unrealized --- and it appears in the
term wherever a crossing occurs. The kernel has no cast, coercion or
conversion.

#emph[Why not let any realization construct any concept of matching
representation?] Nominal identity alone leaves concept values opaque:
under T-Ref and T-App only, a value of $upright("sem") thick C$ can
originate only in a declaration of concept type
(`no_semantic_value_without_declaration`). That is the right state
#emph[before] a realization exists. To let a formula realize a
relationship, representation must be observable and constructible, and
the obvious way to add it destroys what identity just bought. With
global $upright("rep")_C : upright("sem") thick C arrow.r R$ and
$upright("mk")_C : R arrow.r upright("sem") thick C$ available
everywhere,
$lambda x . thick upright("mk")_(upright(M o t o r))\(upright("rep")_(upright(T i l t)) thick x\)$
is a well-typed `Tilt -> MotorAngle` in the empty environment with no
declared relationship
(`unrestricted_representation_binding_bypasses_semantic_identity`), and
the crossing can hide inside a body whose signature mentions no motor
(`hidden_crossing_inside_unrelated_body`). Observation alone is safe but
cannot realize a mapping.

The grant separates the two, and its design reading is #emph[realization
authority]: the signature the designer wrote before any computation
existed is what authorizes the computation's result. $upright("rep")$ is
typed everywhere (T-Rep); $upright("mk") thick C$ is typed only where
$G thick C$ (T-Mk); client code is typed under $upright("Grant.none")$
and a realization under $upright("Grant.of")$ of its own signature (the
definition of $upright("Satisfies")$). A realization of
`Tilt -> Brightness` may construct a `Brightness` and nothing else ---
not a `MotorAngle`, not an `Opacity`, whatever their representations.
Let $e . upright("constructs") thick C$ hold when
$upright("mk") thick C$ occurs in $e$.

#strong[Theorem 7 (Realization authority;
`HasType.constructs_granted`).] If
$Theta\;Delta\;G\;Gamma tack.r e : tau$ and
$e . upright("constructs") thick C$, then $G thick C$. Under
$upright("Grant.of") thick tau$: a value of $upright("sem") thick C$ is
built only inside a realization whose signature announces
$upright("sem") thick C$.

The hidden crossing above is rejected under the grant of an unrelated
declaration and becomes legal, and visible, once `tiltToMotor` is
declared (`hidden_crossing_rejected_under_grant`,
`representation_binding_does_not_enable_hidden_semantic_mapping`).

Two constraints on representations in $Theta . upright("WF")$ were not
anticipated. Representations must be concept-free: if `Tilt` may be
represented #emph[by] `MotorAngle`, then $upright("rep")$ itself is a
hidden mapping under every policy including observation-only. And they
must be data, a requirement that arrived from the reactive semantics: a
concept value may be delayed, and a function-typed representation would
carry a closure across ticks.

The grant is a known shape --- the private constructor of an abstract
type exported only to its defining module @mitchell1988abstract, or a
capability attached to a definition site. What is specific is that the
capability comes from the signature the designer already wrote, so no
annotation is added, and one consequence follows: after all bodies are
inlined into one program, that program is checked under the universal
grant, because each construction was authorized at its own declaration.
Semantic isolation is a property of the design graph and survives
inlining as provenance (Theorem 12), not as a type property of the
executable.

== Representation is not meaning: erasure
<representation-is-not-meaning-erasure>
Let $eta : upright("ConceptId") arrow.r upright("Ty")$ map each concept
to a data type, agreeing with $Theta$ on bound concepts. Erasure
$tau^eta$ replaces $upright("sem") thick C$ by $eta thick C$ throughout
a type; on terms, $upright("rep") thick e$ and
$upright("mk") thick C thick e$ erase to $e^eta$, and the type indices
of operators are erased.

#strong[Proposition 8 (Erasure is sound; `HasType.erase`).] If
$Theta . upright("WF")$, $eta$ agrees with $Theta$, and
$Theta\;Delta\;G\;Gamma tack.r e : tau$, then
$Theta\;Delta^eta\;G'\;Gamma^eta tack.r e^eta : tau^eta$ for every grant
$G'$.

Erasure is not injective --- `Tilt` and `MotorAngle` erase to the same
type (`erase_not_injective`) --- and the untyped baseline is exactly
what erasure leaves: the design the nominal calculus rejects is accepted
after erasure (`baseline_is_erased_modelA`). Generated code is therefore
ordinary code; the semantic layer has no runtime residue. This is the
precise sense in which representation is not meaning: the meaning lives
in the design's declarations and is checked there, and the
representation is all that runs.

Three alternatives were formalized and refuted. A model in which the
display name #emph[is] the identity makes renaming destructive
(`rename_under_name_identity_breaks_client`), whereas here a rename
preserves identity (`semantic_rename_preserves_identity`). Treating a
concept as an ordinary declaration admits category errors: the concept
becomes usable as a value and can be realized by a number. Keeping
identity out of the type as interface metadata checked by a direct-wire
rule is evaded by η-expansion, since
$\(lambda x . thin x\)thick italic(t i l t)$ has the same flow with no
direct wire (`bweak_evaded_by_eta`); a compositional role judgment
strong enough to close that gap has the rule shapes of typing over
$upright("sem")$ and duplicates it.

== Dimensions: coherent arithmetic on representations
<dimensions-coherent-arithmetic-on-representations>
Dimensions play a narrower role than concept identity. Once a concept is
observed through $upright("rep")$, the arithmetic on its representation
must remain physically coherent, and that is all dimensions do. A
physical quantity has type $upright("q") thick d$. There is no
dimension-specific typing rule:
$upright("add")_d : upright("q") thick d arrow.r upright("q") thick d arrow.r upright("q") thick d$,
$upright("mul")_(d_1 d_2) : upright("q") thick d_1 arrow.r upright("q") thick d_2 arrow.r upright("q") thick\(d_1 + d_2\)$
and $upright("div")_(d_1 d_2)$ with $d_1 - d_2$ are registered
operators, and an application is checked by T-App. `length + time` is
ill typed (`dimension_mismatch_rejected`); erasing every dimension to
the zero vector is a sound translation that accepts it
(`counterexampleB_baseline_accepts_length_plus_time`), so the untyped
numeric baseline is the erasure of dimensional typing in the same sense
that it is the erasure of nominal typing.

Dimension and identity are orthogonal, and the orthogonality is what the
relationship-first reading needs: `Tilt` and `MotorAngle` both bound to
$upright("q") thick upright("Angle")$ remain distinct types
(`same_dimension_does_not_imply_same_semantic_identity`); a relationship
realized by the dimensioned formula
$lambda x . thick upright("mk") thick upright("Brightness") thick\(upright("rep") thick x dot.op italic(g a i n)\)$
with $italic(g a i n) : upright("q") thick\(0 - upright("Angle")\)$ is
typed, a dimension error inside it is caught by the same typing, and the
formula cannot manufacture a `MotorAngle` despite the shared dimension
(`explicit_semantic_mapping_uses_dimensioned_formula`). The association
between a concept and its dimension lives in $Theta$, not in the
identity and not in the type constructor: the designer says #emph[tilt
to brightness] first and #emph[tilt is an angle] separately.

Units are not in the calculus at all. A literal `90 deg` elaborates to
$upright("lit")_(upright("Angle"))$ of a scaled magnitude; a coordinate
$upright("inUnit")\(q\,u\)$ is $q$ divided by a scale constant and has
dimension zero; $upright("withUnit")\(x\,u\)$ is the converse; a
conversion is their composition. Each is elaboration, none is a kernel
construct, and a unit choice never reaches a type: `1 m` and `100 cm`
are equal values of one type. The unit laws are proved above the kernel
over an abstract scalar domain and instantiated exactly by a symbolic
group in which π is a generator, so that a degree is exactly π/180
radian; we do not develop them here. Dimensional typing is thus
Kennedy's discipline @kennedy1997units@kennedy2010units without unit
polymorphism in the kernel: dimension variables appear only in the
surface's definitional families (§7.2), where matching against closed
dimensions instantiates them.

= Relationships in time
<relationships-in-time>
A relationship in an interactive physical product does not hold only in
a type space; it holds #emph[over time], and it holds in an authored
temporal structure --- the tilt moves with the interaction, the room
temperature with the environment. This section interprets declarations
in time. Its order follows the thesis: first what it means for a
declared relationship to have a value at a tick (a stream, with
unrealized declarations read from the environment), then how memory
enters a relationship, then which timing domain a relationship's value
belongs to, and finally why the one rule that governs reading across
domains is the one that keeps the designer's temporal structure intact.

== Declarations as streams
<declarations-as-streams>
Values are booleans, naturals (which also carry every
$upright("q") thick d$\; the executable kernel's magnitudes are
naturals), tagged concept values $upright("sem") thick C thick v$,
$upright("none")$, $upright("some") thick v$, lists, pairs, closures
$upright("clo") thick rho thick e$ over a value environment, and
partially applied operators $upright("prim") thick p thick arrow(v)$. An
operator is computed when saturated:
$upright("applyPrim") thick p thick arrow(v)$ is
$upright("compute") thick p thick arrow(v)$ if $\|arrow(v)\|$ equals
$p$'s arity and $upright("prim") thick p thick arrow(v)$ otherwise.

The judgment $rho scripts(tack.r)_t e arrow.b.double v$ --- the value of $e$ at
tick $t$ under local environment $rho$, with the design $Delta$ and the
input $I$ ambient --- is defined in Figure 4 (`Ev`).

$ frac(rho\(x\)= v, rho scripts(tack.r)_t x arrow.b.double v) #h(2em) frac(, rho scripts(tack.r)_t lambda x : tau . thin e arrow.b.double upright("clo") thick rho thick e) #h(2em) frac(, rho scripts(tack.r)_t p arrow.b.double upright("applyPrim") thick p thick\[thin\]) $

$ frac(rho scripts(tack.r)_t f arrow.b.double upright("clo") thick rho' thick b quad rho scripts(tack.r)_t a arrow.b.double w quad w thin upright("::") thin rho' scripts(tack.r)_t b arrow.b.double v, rho scripts(tack.r)_t f thick a arrow.b.double v) #h(2em) frac(rho scripts(tack.r)_t f arrow.b.double upright("prim") thick p thick arrow(u) quad rho scripts(tack.r)_t a arrow.b.double w, rho scripts(tack.r)_t f thick a arrow.b.double upright("applyPrim") thick p thick\(arrow(u) + #h(-0.167em) #h(-0.167em) +\[w\]\)) $

$ frac(Delta^(upright(r e a l))\(delta\)= upright("some") thick b quad\[thin\]scripts(tack.r)_t b arrow.b.double v, rho scripts(tack.r)_t upright("declRef") thick delta arrow.b.double v) med upright("(E-Real)") #h(2em) frac(Delta^(upright(r e a l))\(delta\)= upright("none"), rho scripts(tack.r)_t upright("declRef") thick delta arrow.b.double I thick delta thick t) med upright("(E-Input)") $

$ frac(rho scripts(tack.r)_t e arrow.b.double upright("sem") thick C thick w, rho scripts(tack.r)_t upright("rep") thick e arrow.b.double w) #h(2em) frac(rho scripts(tack.r)_t e arrow.b.double w, rho scripts(tack.r)_t upright("mk") thick C thick e arrow.b.double upright("sem") thick C thick w) $

$ frac(rho scripts(tack.r)_0 i arrow.b.double v, rho scripts(tack.r)_0 upright("delay") thick i thick e arrow.b.double v) med upright("(E-Delay0)") #h(2em) frac(rho scripts(tack.r)_t e arrow.b.double v, rho scripts(tack.r)_(t + 1) upright("delay") thick i thick e arrow.b.double v) med upright("(E-DelayS)") $

$ frac(rho scripts(tack.r)_t f arrow.b.double v_f quad rho scripts(tack.r)_t z arrow.b.double v_z quad rho scripts(tack.r)_t l arrow.b.double upright("list") thin\[thin\], rho scripts(tack.r)_t upright("fold") thick f thick z thick l arrow.b.double v_z) med upright("(E-FoldNil)") $

$ frac(rho scripts(tack.r)_t f arrow.b.double v_f quad rho scripts(tack.r)_t z arrow.b.double v_z quad rho scripts(tack.r)_t l arrow.b.double upright("list") thin\(x thin upright("::") thin italic(x s)\)\
 \[upright("list") thin italic(x s)\,thin v_z\,thin v_f\]scripts(tack.r)_t upright("fold") thick\#2 thick\#1 thick\#0 arrow.b.double r #h(2em)\[r\,thin x\,thin v_f\]scripts(tack.r)_t\#2 thick\#1 thick\#0 arrow.b.double v, rho scripts(tack.r)_t upright("fold") thick f thick z thick l arrow.b.double v) med upright("(E-FoldCons)") $

#emph[Figure 4. Single-domain evaluation (`Ev`), with $Delta$ and $I$
ambient. In one domain $upright("sync") thick kappa$ evaluates exactly
as $upright("delay")$ (rules `syncZero`, `syncSucc`), which §6.7
justifies. Literals evaluate to themselves. $\#i$ is de Bruijn index
$i$.]

Three points of Figure 4 deserve comment. An unrealized declaration is
an #emph[input]: E-Input reads $I thick delta thick t$, the
environment's realization of the relationship. A realized declaration is
evaluated from its realization at the current tick in the #emph[empty]
environment (E-Real): a reference's value never depends on the local
environment of the reader, which is what makes a relationship a stream
the design observes rather than a function of its call site
(`Ev.declRef_env_irrelevant`). And $upright("delay")$ shifts the tick:
read at $t + 1$, it evaluates its operand at $t$\; at $0$ it evaluates
the initial value.

The recursor's rule unrolls syntactically. Rather than a recursive
definition of a fold on values, the rule evaluates the syntactic term
$upright("fold") thick\#2 thick\#1 thick\#0$ in an environment holding
the tail, the seed and the function, and then the term
$\#2 thick\#1 thick\#0$ in an environment holding the result, the head
and the function. This keeps $upright("Ev")$ an ordinary inductive
relation with no mutual recursion, so every proof by induction on
$upright("Ev")$ that predated the recursor extends by one case, and
totality is a separate lemma by induction on the list (§7.1).

#strong[Theorem 9 (Determinism; `Ev.det`).] If
$rho scripts(tack.r)_t e arrow.b.double v_1$ and
$rho scripts(tack.r)_t e arrow.b.double v_2$ then $v_1 = v_2$.

Evaluation is a partial function with no hidden evaluation order ---
there are no effects to order --- and this holds unconditionally.

An executable interpreter $upright("evalF")$ with a fuel parameter is
proved sound for the relation (`evalF_sound`, `Ev.of_evalF`). Every
trace in the development and in this paper was computed by it inside the
proof checker.

== Cycles and causality
<cycles-and-causality>
Let $e . upright("instRefs")$ be the declarations $e$ refers to
#emph[instantaneously]: those not under the delayed operand of a
$upright("delay")$ or $upright("sync")$ (the initial value is read at
tick $0$ and counts as instantaneous).
$upright("InstDependsOn") thick Delta thick a thick b$ holds when
$b in upright("instRefs")$ of $a$'s body.

#strong[Definition (Causal).]
$upright("Causal") thick Delta := exists thin italic(r a n k) thin R . thick\(forall delta . thick italic(r a n k) thick delta < R\)and forall a thin b . thick upright("InstDependsOn") thick Delta thick a thick b arrow.r italic(r a n k) thick b < italic(r a n k) thick a$.

On the delay-free fragment $upright("InstDependsOn")$ is
$upright("DependsOn")$, so causality is exactly bounded acyclicity
(`Causal_iff_acyclic_of_delayFree`): the earlier condition is the
timeless special case rather than a replaced requirement. A structural
cycle every path of which passes through a delayed operand ---
`A := delay 0 B; B := A`, or a self-delayed accumulator --- is causal. A
cycle that is partly delayed is not.

#strong[Proposition 10 (Strict cycles have no value;
`Ev.not_of_strictCyclic`).] If $a$ lies on a cycle of references passing
through neither a delayed operand nor a lambda, then for every tick and
environment there is no $v$ with
$rho scripts(tack.r)_t upright("declRef") thick a arrow.b.double v$.

Not "some default", not "one of several": no derivation exists. A gap
should be recorded. A cycle guarded by a lambda, `A := λx. A x`, is
rejected by $upright("Causal")$ yet `declRef A` does evaluate --- to a
closure; only applying it diverges. $upright("Causal")$ is conservative
for lambda-guarded cycles and Proposition 10 covers strict cycles only.

== The logical relation and totality
<the-logical-relation-and-totality>
Totality is proved by a logical relation indexed by the tick. The
relation is stated generically in an #emph[application relation]
$A : upright("Value") arrow.r upright("Value") arrow.r upright("Value") arrow.r upright("Prop")$
--- how a function value applied to an argument yields a result --- so
that the single-domain and multi-domain semantics share one relation. At
a fixed tick, $A$ is $upright("Apply") thick Delta thick I thick t$:
$v_f$ applied to $w$ yields $v$ when $v_f$ is a closure whose body
evaluates to $v$ at $t$ under $w$, or a partial operator whose
saturation is $v$.

$ cal(R)_Theta^A\[upright("bool")\]thick v arrow.l.r.double & exists b . thick v = upright("bool") thick b\
cal(R)_Theta^A\[upright("nat")\]thick v thick = thick cal(R)_Theta^A\[upright("q") thick d\]thick v arrow.l.r.double & exists n . thick v = upright("nat") thick n\
cal(R)_Theta^A\[upright("opt") thick tau\]thick v arrow.l.r.double & v = upright("none") thick or thick exists w . thick v = upright("some") thick w and cal(R)_Theta^A\[tau\]thick w\
cal(R)_Theta^A\[upright("list") thick tau\]thick v arrow.l.r.double & exists arrow(w) . thick v = upright("list") thick arrow(w) and forall w in arrow(w) . thick cal(R)_Theta^A\[tau\]thick w\
cal(R)_Theta^A\[tau times sigma\]thick v arrow.l.r.double & exists x thin y . thick v = upright("pair") thick x thick y and cal(R)_Theta^A\[tau\]thick x and cal(R)_Theta^A\[sigma\]thick y\
cal(R)_Theta^A\[tau arrow.r sigma\]thick v arrow.l.r.double & forall w . thick cal(R)_Theta^A\[tau\]thick w arrow.r exists v' . thick A thick v thick w thick v' and cal(R)_Theta^A\[sigma\]thick v'\
cal(R)_Theta^A\[upright("sem") thick C\]thick v arrow.l.r.double & exists w . thick v = upright("sem") thick C thick w and forall R . thick Theta thick C = upright("some") thick R arrow.r cal(R)^A\[R\]thick w $

The concept clause says that a concept value is a tagged representation
value. Its inner use of the relation at the representation $R$ is the
concept-free relation $upright("RedSF")$\; because
$Theta . upright("WF")$ makes $R$ concept-free, the definition is well
founded on the type without appeal to $Theta$ (`Red_semFree`). At data
types the relation is independent of $A$ (`Red_data`), which is what
allows a delayed value to be transported between ticks. Registered
operators are related at their types for any $A$ that saturates them
(`Red_prim`).

Well-typed inputs are inputs related to the type view:
$Delta^(upright(t y))\(delta\)= upright("some") thick tau and Delta^(upright(r e a l))\(delta\)= upright("none") arrow.r.double cal(R)_Theta^(upright("Apply") thick Delta thick I thick t)\[tau\]thick\(I thick delta thick t\)$
for every $t$.

#strong[Theorem 11 (Totality under causality; `fundamental`,
`reactive_total`, `Ev.red`).] Let $Theta . upright("WF")$, let
$italic(r a n k)\,R$ witness $upright("Causal") thick Delta$, let
$upright("GlobalWF") thick italic(e v) thick Theta thick Delta$ and let
$I$ be well typed. Then for every tick $t$, bound $r$, grant $G$, and
$Theta\;Delta\;G\;Gamma tack.r e : tau$, and every $rho$ related to
$Gamma$ such that every instantaneous reference of $e$ has rank below
$r$, there is $v$ with $rho scripts(tack.r)_t e arrow.b.double v$ and
$cal(R)_Theta^(upright("Apply") thick Delta thick I thick t)\[tau\]thick v$.

Consequently, in a causal, globally well formed design with well-typed
inputs, every declared relationship has a value at every tick, and that
value --- unique by Theorem 9 --- is related to its expected type.

#emph[Proof sketch.] Lexicographic induction on
$\(t\,r\,upright("derivation")\)$. A delayed operand at tick $t + 1$ is
evaluated at tick $t$ under #emph[any] rank (the first component
decreases); an instantaneous reference to a realized declaration $delta$
is evaluated at the same tick under the smaller bound
$italic(r a n k) thick delta$ (the second decreases), and its
realization is well typed under the grant of its own signature by
$upright("GlobalWF")$\; every other case is the induction on the
derivation. The $upright("fold")$ case uses `fold_total` (§7.1).
$square.stroked.tiny$

The relation is a step-indexed logical relation in the sense of Appel
and McAllester @appel2001indexed and Ahmed @ahmed2006stepindexed, with
the tick as the index and the rank as a second, inner index; what
differs is that the index counts #emph[time] rather than #emph[steps],
so that the induction on it is the induction that makes a delayed
self-reference well defined.

== Two restrictions forced by totality
<two-restrictions-forced-by-totality>
T-Delay and T-Sync restrict their type to data and their context to
empty. Neither restriction was a design decision; each is what the
induction of Theorem 11 needs. A delayed closure would be a value at
tick $t$ related by
$cal(R)^(upright("Apply") thick Delta thick I thick t)$ that must be
transported to tick $t + 1$, and the arrow clause is tick-indexed and
cannot be transported; `Red_data` is exactly the statement that data
clauses can. A delay under a binder would evaluate its operand at the
previous tick in an environment created at the current one. The
restrictions have two corollaries stated as theorems: nothing of
function type can be delayed or transported (`arrow_not_delayable`, by
inversion), and memory and transport are typed only in the empty context
(`delay_not_under_binder`, `sync_not_under_binder`). Temporal state
therefore belongs to declarations --- a relationship may remember, a
function may not --- and a reusable stateful behavior is instantiated
into fresh declarations (§9) rather than abstracted over.

Initialization is semantic, not validation. Every $upright("delay")$
carries an explicit initial value. Two toy relations without one show
why: the first tick is either undefined
(`first_tick_undefined_without_init`) or nondeterministic
(`first_tick_nondeterministic_without_init`).

== Provenance through time
<provenance-through-time>
State carries semantic tags; it never creates them. Let
$v . upright("Taints") thick C$ hold when the tag $C$ occurs anywhere
inside $v$ --- including inside closures' environments and bodies.

#strong[Theorem 12 (Semantic integrity over time; `Ev.tag_provenance`,
`temporal_state_preserves_semantic_identity`).] If no realization in
$Delta$ constructs $C$, no input value is tainted by $C$, $e$ does not
construct $C$ and $rho$ is clean, then every value
$rho scripts(tack.r)_t e arrow.b.double v$ is clean. In particular a delayed
value carries exactly the tag of the value delayed.

Combined with Theorem 7 this is the runtime half of semantic integrity:
a concept appears in a value only if some signature announces it or some
input carries it, at every tick. The typing rule
$upright("delay") : tau arrow.r tau arrow.r tau$ at data $tau$ gives the
static half --- a delayed tilt is a tilt, and a backward difference over
a time step has dimension $upright("Length") - upright("Time")$ with no
derivative primitive.

On the first-order fragment a compiler cares about --- #emph[wiring]
designs, whose realizations contain no lambda --- closures never arise,
evaluation is independent of the local environment, and unfolding a
reference to its realization preserves the value at every tick
(`Ev.noClo`, `Ev.env_irrelevant`, `unfolds_preserves_eval`); #emph[pure]
terms, with no reference, memory or transport, have the same value in
every design at every tick (`Ev.pure`), which §7.2 uses for the
definitional library.

== Clock domains as design context
<clock-domains-as-design-context>
A clock domain is part of a relationship's design context: it says
#emph[when the relationship's value belongs to the design], and the
designer authors it as an identity --- "moves with the interaction",
"moves with the environment" --- before any rate is known. The time
model is one global base tick and a schedule
$S : upright("ClockId") arrow.r bb(N) arrow.r upright("Bool")$ saying at
which global ticks each domain activates. A period $n$ induces the
schedule $t med mod med n = 0$ (`Sched.periodic`); the schedule lives
outside the design. Domain-local time is not a separate counter but the
sequence of a domain's activations. The last activation of $kappa$
strictly before $t$ is
$ upright("prevAct") thick S thick kappa thick 0 = upright("none")\,#h(2em) upright("prevAct") thick S thick kappa thick\(t + 1\)= upright("if") thick S thick kappa thick t thick upright("then") thick upright("some") thick t thick upright("else") thick upright("prevAct") thick S thick kappa thick t\, $
with
$upright("prevAct") thick S thick kappa thick t = upright("some") thick t' arrow.r.double t' < t and S thick kappa thick t'$.

Each declaration is assigned a domain by the clock environment
$upright(K)$, or none if it is a domain-agnostic relationship usable
anywhere. The clock is interface data in every sense that matters ---
clients' validity depends on it, it is frozen under refinement, and
changing it is an edit (Table 2) --- and it is stored as a projection
beside the interface, as a concept's representation is stored in $Theta$
rather than in the type.

The #strong[domain judgment]
$upright("Clocked") thick upright(K) thick kappa thick e$, for
$kappa : upright("Option") thick upright("ClockId")$, says that $e$ may
be evaluated in domain $kappa$:
$ upright("Clocked") thick upright(K) thick kappa thick\(upright("declRef") thick delta\)arrow.l.r.double & upright(K) thick delta = upright("none") thick or thick upright(K) thick delta = kappa\
upright("Clocked") thick upright(K) thick\(upright("some") thick kappa\)thick\(upright("delay") thick i thick e\)arrow.l.r.double & upright("Clocked") thick upright(K) thick\(upright("some") thick kappa\)thick i and upright("Clocked") thick upright(K) thick\(upright("some") thick kappa\)thick e\
upright("Clocked") thick upright(K) thick\(upright("some") thick kappa\)thick\(upright("sync") thick kappa' thick i thick e\)arrow.l.r.double & upright("Clocked") thick upright(K) thick\(upright("some") thick kappa\)thick i and upright("Clocked") thick upright(K) thick\(upright("some") thick kappa'\)thick e\
upright("Clocked") thick upright(K) thick upright("none") thick\(upright("delay") thick i thick e\)arrow.l.r.double & upright("False") #h(2em) #h(2em) upright("Clocked") thick upright(K) thick upright("none") thick\(upright("sync") thick kappa' thick i thick e\)arrow.l.r.double upright("False") $
and homomorphically elsewhere. A reference stays in its domain or is
agnostic; a delay needs a domain; $upright("sync") thick kappa'$
switches the domain of its operand. A design is well clocked when every
realization is clocked in its own declaration's domain. Typing is
unchanged and blind to domains: the direct wire between two domains at
the same value type is well typed and rejected only by
$upright("Clocked")$. Placing the domain in the type instead was tried
and set aside: every domain-agnostic relationship would then need clock
polymorphism (`clocked_type_forces_polymorphism`), and nothing the type
rejects is missed by the judgment.

== Multi-domain evaluation
<multi-domain-evaluation>
The judgment $rho scripts(tack.r)_t^kappa e arrow.b.double v$ --- in domain
$kappa$ at global tick $t$, with $S$, $Delta$, $I$ ambient --- is
$upright("Ev")$ with the two temporal rules replaced by four (`MEv`):
$ frac(upright("prevAct") thick S thick kappa thick t = upright("none") quad rho scripts(tack.r)_t^kappa i arrow.b.double v, rho scripts(tack.r)_t^kappa upright("delay") thick i thick e arrow.b.double v) #h(2em) frac(upright("prevAct") thick S thick kappa thick t = upright("some") thick t' quad rho scripts(tack.r)_(t')^kappa e arrow.b.double v, rho scripts(tack.r)_t^kappa upright("delay") thick i thick e arrow.b.double v) $
$ frac(upright("prevAct") thick S thick kappa' thick t = upright("none") quad rho scripts(tack.r)_t^kappa i arrow.b.double v, rho scripts(tack.r)_t^kappa upright("sync") thick kappa' thick i thick e arrow.b.double v) #h(2em) frac(upright("prevAct") thick S thick kappa' thick t = upright("some") thick t' quad rho scripts(tack.r)_(t')^(kappa') e arrow.b.double v, rho scripts(tack.r)_t^kappa upright("sync") thick kappa' thick i thick e arrow.b.double v) $
$upright("delay")$ reads the previous activation of the current domain;
$upright("sync") thick kappa'$ reads the previous activation of $kappa'$
and evaluates its operand #emph[there], in $kappa'$. All other rules
carry $kappa$ unchanged.

#strong[Proposition 13 (One temporal primitive; `delay_is_sync_own`,
`clocked_delay_iff_sync_own`, `single_domain_embedding`).]
$rho scripts(tack.r)_t^kappa upright("delay") thick i thick e arrow.b.double v$
iff
$rho scripts(tack.r)_t^kappa upright("sync") thick kappa thick i thick e arrow.b.double v$,
and $upright("delay") thick i thick e$ is clocked in $kappa$ iff
$upright("sync") thick kappa thick i thick e$ is. Under the
always-active schedule, $rho scripts(tack.r)_t^kappa e arrow.b.double v$ iff
$rho scripts(tack.r)_t e arrow.b.double v$, for every $kappa$.

The kernel therefore has one temporal primitive --- read a domain at its
previous activation --- and $upright("delay")$ is notation for its
diagonal; a $upright("delay")$ in a slow domain reads three global ticks
back where a $upright("delay")$ in a fast one reads one, with the same
syntax. The single-domain semantics of §6.1 is the one-domain special
case of this one rather than a replaced machine.

#strong[Theorem 14 (Determinism and totality in every domain; `MEv.det`,
`mfundamental`, `multi_domain_total`).] Multi-domain evaluation is a
partial function, for every schedule. In a causal, globally well formed
design with inputs well typed in every domain, every declared
relationship has a value in every domain at every tick, related to its
expected type.

The proof reuses the logical relation of §6.3 with the application
relation
$upright("MApply") thick S thick Delta thick I thick kappa thick t$, and
the same lexicographic induction: a transport at $t$ evaluates its
operand at $t' < t$ under any rank. Causality is the #emph[same]
$upright("Causal") thick Delta$: a transport's operand is never
instantaneous, so no cross-domain cycle can be. An interpreter
$upright("mevalF")$ is proved sound (`mevalF_sound`). Tag provenance
holds across domains (`MEv.tag_provenance`): transport changes timing,
not identity, and a crossing from `Tilt@fast` to `Tilt@slow` authorizes
neither `Tilt -> MotorAngle` nor
$upright("q") thick upright("Length") arrow.r upright("q") thick upright("Time")$,
by the typing rule.

== Strictly before: preserving the authored temporal structure
<strictly-before-preserving-the-authored-temporal-structure>
#emph[Why not expose scheduler order?] A transport sees only source
activations strictly before the destination tick. The rule exists to
preserve the designer's declared temporal relationship --- "`heat` reads
the light as it stood before this tick" --- without adding a fact the
designer never authored, namely which of two simultaneously active
domains the implementation happens to run first. That is a choice with
an observable alternative, and the alternative was built.

#strong[Theorem 15 (Same-tick visibility exposes the scheduler;
`scheduling_order_observable`).] Let $upright("MEv")_lt.eq$ be the
semantics in which a transport may also see a simultaneously active
source, resolved by a priority between domains. There is a two-domain
design, a schedule and an input such that two priorities give two
different values to the same declaration at the same tick.

At tick 1 both domains are active for the first time; with the source
first the transport delivers the source's current value, with the
destination first it delivers the initial value. The strictly-before
rule has no such parameter, and Theorem 14 has no order between
simultaneously active domains in its statement. Every crossing costs one
destination-visible step; "synchronous sub-domains evaluated in one
instant" are, in this model, the same domain.

Rate and identity are distinct. A clone of a domain with the identical
schedule is a different domain, and a direct wire between them is
rejected (`equal_rate_not_same_domain`); a domain at the same rate but
shifted in phase reads different values through a transport. Rate
changes are validation-only: they change the induced schedule and the
observed values, but no client's well-formedness. This is where the
calculus departs from synchronous languages that recover clocks by
inference @colaco2003clocks@biernacki2008clock: the domain is authored,
because the information needed to infer it --- the realization binding
--- arrives at the point where a designer is least able to make the
decision.

= Derived structure
<derived-structure>
The calculus deliberately has no primitive for most of what a designer
names. This section records what #emph[is] in the kernel for computation
over data --- one recursor, products, equality --- and then two negative
design results that follow the same method: before adding a primitive,
ask whether the behavior is already derivable from declarations, memory,
transport and lists. Every temporal operator of the surface language is,
and so is the one construction most likely to be proposed as primitive,
the lossless cross-domain window.

== The recursor, products and equality
<the-recursor-products-and-equality>
$upright("fold") thick f thick z thick l$ is a #emph[term former], not a
registered operator. The kernel has no recursion, deliberately; a total
language needs an eliminator for its inductive data, and
$upright("fold")$ is the one construct that applies a function value in
the course of evaluation. Registered operators never apply closures. The
alternative of one primitive per collection operation was rejected
because a primitive cannot apply a closure and each would need its own
evaluation rule; the alternative of bounded unrolling was rejected
because lists --- the cross-domain window --- are unbounded.

The recursor is total on related values (`fold_total`, `mfold_total`),
by an induction on the list separate from Theorem 11, which invokes it
in its $upright("fold")$ case. Every collection operation --- `map`,
`filter`, `any`, `all`, `contains`, `append`, `sum`, `zip`, and through
$upright("toList")$ the option eliminators --- is a definition over
$upright("fold")$, and each is proved to compute the mathematical
function it names through one general lemma: the recursor computes
$upright("List.foldr") thick g$ whenever the step closure implements $g$
on the reachable accumulators (`fold_spec`\; then `any_spec`,
`all_spec`, `map_spec`, `filter_spec`, `min_spec`, `clamp_spec`, …).
Finite quantification is a fold ---
$forall x in italic(x s) . thin P thin x$ iff `all xs P` evaluates to
true (`forall_in_list`, `exists_in_list`) --- and a finite-set literal
means membership with duplicates irrelevant (`oneOf_mem`,
`oneOf_dup_irrelevant`), so there is no `Set` type and no uniqueness
convention.

$tau times sigma$ with $upright("pair")$, $upright("fst")$,
$upright("snd")$ entered the kernel after the Church encoding was tried
and refuted twice. A Church pair is an arrow, and arrows are not data:
nothing of function type can be delayed or transported
(`arrow_not_delayable`), so paired #emph[state] --- a delayed reading
with its timestamp --- needs a data product. And a Church pair used as a
first-class value needs rank-2 types: in a toy System F with a rank
measure, the type of $upright("fst")$ on Church pairs has rank 2
(`church_fst_rank`), and in the prenex fragment a pair instantiated at
one result type serves only one projection
(`church_pair_prenex_one_projection`). Products are value composition
only; they are never a component interface or an output bundle (§9 shows
what a tuple-returning declaration does to the dependency graph).

$upright("eq")_tau^(italic(p f))$ is structural equality at every data
type --- booleans, numbers, $upright("none")$/$upright("some")$, pairs
and lists componentwise, concept values by tag and representation ---
with the proof $h : tau . upright("Data")$ carried #emph[in the syntax].
This is the kernel's only capability evidence: an equality on a function
type is unwritable rather than ill typed, which keeps T-Prim
unconditional. On first-order values structural equality is equality
(`Value.beq_iff`, by a mutual induction over the nested value type).

Order is deliberately not generalized. A first formulation gave `<` a
structural meaning at every data type --- booleans, options, pairs and
lists lexicographically --- and it was formally consistent. An audit
rejected it on the grounds that no such order has a design meaning:
`mode1 < mode2` would order modes by a constructor tag, `None < Some x`
is an artifact. The structural order was deleted and $upright("lt")_d$
restored to quantities only. So
$upright("Data") arrow.r.double upright("Eq")$ holds (`Cap.eq_iff_data`)
but $upright("Eq") ⇏ upright("Ord")$\; order on a #emph[concept] is a
surface capability --- a concept the designer declared ordered and
represented by a quantity compares as $upright("lt")_d$ on
$upright("rep")$, a term the kernel already admits
(`lt_only_on_quantities`, `lt_rejected`, `min_mode_rejected`).
Enumerations follow the same rule: equality is natural, declaration
order is never silently behavioral order.

== Polymorphism by families, and the library as combinators
<polymorphism-by-families-and-the-library-as-combinators>
Five models of polymorphism were compared: a monomorphic kernel;
per-type duplication; rank-1 parametric polymorphism; System F; higher
rank. The one adopted is rank-1 #emph[as definitional families]: every
library entry is a function $upright("Ty") arrow.r upright("Expr")$ (or
$upright("Dim") arrow.r upright("Expr")$) in the metalanguage, and a
scheme is a pattern over type and dimension variables with capability
constraints. The kernel sees only the instances
(`instances_are_monomorphic`: three uses of `min` are three kernel
terms), and T-Prim, T-App and Proposition 1 are unchanged.

Why this needs no kernel support: a use site always has #emph[closed]
argument types. Every declaration's expected type is frozen and closed,
and inference is bottom-up, so finding the instance of a scheme is
one-way #emph[matching] of the scheme's pattern against closed types ---
decidable, returning the unique substitution on the pattern's variables
(`matchTy_sound`, `matchTy_complete`). There is no unification of two
open types, no let-generalization inside expressions
@damas1982principal, and no principal-type search; those problems arise
when a definition's type is inferred from its body, and every definition
here carries its signature. The situation is that of local type
inference @pierce2000local with no bidirectionality needed. Capability
constraints are checked after matching (`Scheme.instantiate_sound`), and
the two failure points have designer-level explanations: #emph[no
instance] and #emph[capability failed]. System F was rejected by
measuring what it would add --- the prenex fragment #emph[is]
instantiation of families --- and every candidate higher-rank use has a
rank-1 replacement (`applyBoth_rank`, `applyBoth_replacement`).
Dimension polymorphism (`sum : list (q d) → q d`) uses the same
mechanism with dimension pattern variables; no kind system, because the
dimension algebra already lives in the operator table.

Nominality survives all of it. #emph[Any] family typed at
$alpha arrow.r alpha arrow.r alpha$, instantiated at concept $C$,
rejects an argument of concept $C' eq.not C$, the representations never
consulted (`generic_preserves_identity`); the same for
$upright("q") thick d$ versus $upright("q") thick d'$
(`generic_preserves_dimension`). This is Reynolds's abstraction
@reynolds1983types and Wadler's free theorems @wadler1989free at the
level of syntax: a family cannot inspect what it is instantiated at,
because it is instantiated by substitution into a closed term.

Every library entry is a #strong[combinator]: variables, literals,
lambdas, applications, registered operators, the recursor and
$upright("rep")$ --- no reference, no state, no transport, no
$upright("mk")$. For combinators four facts are proved once and combine
into an inlining statement (`lib_expansion`): typing is independent of
the design and the grant and reads $Theta$ only through write-once
bindings (`HasType.comb_irrelevant`); the value is the same in every
design at every tick under every input (`lib_eval_context_free`, from
`Ev.pure`); the term is clocked in every domain (`lib_clocked`); nothing
is constructed (`Comb.noConstruct`). This is what lets an implementation
inline an equation at each use without creating a declaration --- a
library entry as a declaration would be monomorphic and would enter the
dependency graph.

The expressiveness ceiling, stated once: total first-order-data
computation over booleans, quantities, concepts, options, lists and
pairs, with higher-order functions and one list recursor; generic
definitions instantiated at closed types; no general recursion, no type
abstraction in terms, no sums (an enumeration with a payload is encoded
as a tag paired with an optional payload, and a kernel sum would cost
one more eliminator term former exactly like $upright("fold")$), no
unbounded quantification. This is a design conclusion backed by executed
cases and the proved library; it is not a minimality theorem.

== The window: a negative design result
<the-window-a-negative-design-result>
Within one domain an occurrence is a stream of optional type (§7.4).
Across domains this fails: $upright("sync")$ is a zero-order hold, so a
slow consumer of a fast event source sees the last value only. Two fast
events at ticks 1 and 2 and one event at tick 2 are indistinguishable at
the slow activation at tick 3, and a single event at tick 1 followed by
a quiet fast tick is dropped outright
(`opt_loses_multiplicity_under_sync`). The counterexample is against
$upright("sync")$ as an #emph[event transport], not against optional
types; it says that multiplicity and order are observable across domains
and that keeping them requires buffering.

What the destination should see is the source's activations since the
destination's own previous activation --- the #emph[window],
$upright("windowTicks") thick S thick italic(s r c) thick italic(d s t) thick t$,
the source ticks in
$\[upright("prevAct") thick S thick italic(d s t) thick t\,med t\)$. The
window equals the source's accumulated log read at the current tick
minus its length at the previous destination activation
(`buffer_from_log_and_cursor`): two single-instant reads, a
$upright("sync")$ of a source-side accumulator and a $upright("delay")$
of a cursor. With list data this is five ordinary declarations:

```
log     @src :  cons src (delay nil log)             -- source-side accumulator
logD    @dst :  sync src nil log                     -- the log, transported
seen    @dst :  length logD                          -- log length now
cursor  @dst :  delay 0 seen                         -- log length at the previous activation
window  @dst :  reverse (take (seen - cursor) logD)  -- the new entries, oldest first
```

#strong[Theorem 16 (The window is derivable;
`buffer_window_correspondence`).] For every schedule, input, destination
domain and tick, if the five declarations are realized as above and
$italic(s r c)$ is an input, then
$\[thin\]scripts(tack.r)_t^(italic(d s t)) upright("window") arrow.b.double upright("list") thin\(upright("map") thin\(I thin italic(s r c)\)thin\(upright("windowTicks") thick S thick italic(s r c) thick italic(d s t) thick t\)\)$.

The elaboration is well typed and well clocked
(`buffer_elaboration_well_typed`, `buffer_elaboration_well_clocked`);
the list is injective on windows, ordered by tick, and
multiplicity-preserving for every predicate (`buffer_lossless`,
`window_to_list_preserves_order`,
`window_to_list_preserves_multiplicity`). The general negative result is
that any summary depending only on the newest $k$ entries, for any fixed
$k$, identifies a $k$-entry window with a $\(k + 1\)$-entry window
(`bounded_summary_not_lossless`); a lossless summary is injective and
therefore unbounded (`lossless_iff_injective`). Capacity is thus a
deployment obligation on the schedule --- for periodic schedules one
destination period of source activations suffices
(`periodic_capacity_sufficient`) --- and the only overflow policy that
preserves the semantics is to reject the deployment; dropping is a
semantic change (`bounded_buffer_agrees`, `negE`).

The point for the calculus is what was #emph[not] added, and the method
by which it was not added --- a candidate primitive was formalized, its
behavior was derived from the existing kernel, and the derivation was
proved correct: no event type, no buffer primitive, no scheduler order,
no same-tick visibility, no implicit overflow rule. An event stream is a
data-typed declaration in a domain; an occurrence is its value at an
activation; a lossless view of it across domains is the five
declarations; `latest`, `count`, `coalesce` are ordinary computations
over `window`.

== Derived temporal operators
<derived-temporal-operators>
Every temporal operator a surface language offers reduces to
$upright("delay")$ and registered operators. Table 2 lists the
elaborations; each is a declaration referring to itself --- a
self-delayed cycle, the class that structural acyclicity forbade and
causality licenses --- and each was typed, checked causal, and run on a
concrete trace. There is no independent kernel definition of `count` for
the reduction to be proved equal to; the claim is that the elaboration
has the intended trace.

#figure(
  align(center)[#table(
    columns: (50%, 50%),
    align: (auto,auto,),
    table.header([surface], [declaration body],),
    table.hline(),
    [`previous x`], [$upright("delay") thick italic(i n i t) thick x$],
    [`previous x` without an initial
    value], [$upright("delay") thick upright("none") thick\(upright("some") thick x\)$\;
    the absence is pushed to consumers],
    [`hold init e`], [$upright("getD") thick e thick\(upright("delay") thick italic(i n i t) thick italic(s e l f)\)$],
    [`count e`], [$upright("ite") thick\(upright("isSome") thick e\)thick\(1 + upright("delay") thick 0 thick italic(s e l f)\)thick\(upright("delay") thick 0 thick italic(s e l f)\)$],
    [`since e`], [$upright("ite") thick\(upright("isSome") thick e\)thick 0 thick\(1 + upright("delay") thick 0 thick italic(s e l f)\)$],
    [`once e`], [$upright("delay") thick upright("false") thick italic(s e l f) or upright("isSome") thick e$],
    [`every n`], [a modulo-$n$ counter over $upright("delay")$],
    [`rise b`], [$b and not thin upright("delay") thick upright("false") thick b$,
    as an optional Boolean],
  )]
  , kind: table
  )

#emph[Table 3. Derived temporal operators
(`Experiments/ReactiveAlternatives.lean`).]

There is no signal type in $upright("Ty")$: under this semantics a
signal type would be inhabited by exactly the terms of the underlying
type and would reject nothing. There is no event type: within one domain
an input delivers at most one value per tick by construction, so an
occurrence is a stream of optional type, and the streams of type
$upright("opt") thick tau$ are exactly the streams of multiplicity at
most one. What separates an occurrence from an optional value can only
be seen when a source ticks faster than its observer, which is the
cross-domain question of §7.3. State has no identity of its own: a cell
is a $upright("delay")$ in a declaration body, consumers refer to the
declaration, and there is consequently no notion of two writers to one
cell.

= Physical effect
<physical-effect>
A relationship, realized and evaluated, yields a value; a value is not
yet an effect. The chain the calculus draws is #emph[relationship →
realized value → explicit drive edge → physical effect], and this
section is the last arrow. A declaration computes a value; it does not
move hardware. Physical effect happens only through an explicit
#strong[drive edge] from a declaration to a nominally identified
#strong[output] --- a logical actuator channel, a resource in a
different sort from both concepts and declarations: "the desired
steering angle" --- a declaration of concept type, one instance of the
concept --- is a value; "the steering motor" is a resource.

- $Omega : upright("OutputId") arrow.r upright("Option") thick chevron.l italic(a c c e p t s)\,italic(c l o c k) chevron.r$
  --- each output's accepted type and domain;
- $beta : upright("DeclId") arrow.r upright("Option") thick upright("OutputId")$
  --- the drive edges, a write-once per-declaration projection of the
  same shape as $upright(K)$\;
- $upright("DriveWF") thick Omega thick upright(K) thick Delta thick beta := forall delta thin o . thick beta thick delta = upright("some") thick o arrow.r exists italic(s p e c) . thick Omega thick o = upright("some") thick italic(s p e c) and Delta^(upright(t y))\(delta\)= upright("some") thick italic(s p e c) . italic(a c c e p t s) and upright(K) thick delta = upright("some") thick italic(s p e c) . italic(c l o c k)$\;
- $upright("SingleDriver") thick beta := forall delta_1 thin delta_2 thin o . thick beta thick delta_1 = upright("some") thick o arrow.r beta thick delta_2 = upright("some") thick o arrow.r delta_1 = delta_2$\;
- $upright("CompleteOutputs") thick beta thick italic(r e q)$ --- every
  required output is driven.

Nothing was added to types, typing, the domain judgment, evaluation or
the grant. The edge neither coerces nor converts nor synchronizes: the
driver's type #emph[equals] the accepted type and its domain #emph[is]
the output's. A declaration typed `Tilt` cannot drive a `MotorAngle`
output; an output that accepts a representation type needs an explicit
$upright("rep")$-typed declaration in front of it; a slow driver reading
a fast value must $upright("sync")$ it upstream. A driver of a
concept-accepting output is necessarily a value, not a function
(`driver_is_unit_domain`).

#strong[Definition.]
$upright("PhysicalOutput") thick S thick Delta thick I thick Omega thick beta thick o thick t thick v := exists delta thin italic(s p e c) . thick beta thick delta = upright("some") thick o and Omega thick o = upright("some") thick italic(s p e c) and\[thin\]scripts(tack.r)_t^(italic(s p e c) . italic(c l o c k)) upright("declRef") thick delta arrow.b.double v$.

#strong[Theorem 17 (One driver, one output;
`single_driver_output_deterministic`,
`multiple_direct_drivers_rejected`).] Under
$upright("SingleDriver") thick beta$, $upright("PhysicalOutput")$ is a
partial function of $o$ and $t$. Two declarations driving one output ---
each well typed, well clocked, causal and individually well formed ---
violate $upright("SingleDriver")$ and nothing else, and there is a tick
at which the output receives two values.

#emph[Why not hide output arbitration?] The principle is #emph[many
contributors, one explicit final driver]. Contributors are dependencies:
`base + corr -> final -> motor` passes every check; priority is a
conditional in the single driver; blend, maximum and clamp are ordinary
declarations of the target type. Why arbitration must be explicit is
shown rather than argued: first-wins, last-wins and maximum over the
same value graph give three different physical outputs
(`hidden_arbitration_observable`). Binding an unbound declaration to an
undriven output is a refinement and preserves $upright("SingleDriver")$
(`first_output_binding_is_monotone`); binding to a driven output is
invalid; retargeting, renaming or detaching an edge invalidates an
unchanged design.

Two alternatives were formalized in toy form. Direct effect rows --- the
set of outputs a declaration drives --- are exactly the drive edges, and
single-driver is exactly their pairwise disjointness; propagated rows
flag a valid design in which a display reads the driver; action values
move the conflict into the collector that consumes them, which must then
be a policy, which is the single driver by another name. None of this
bears on richer effect systems @plotkin2013handlers\; it says these
formulations add no rejection the single-driver rule lacks.

Finally, the dual form, which shows that the boundary between semantic
behavior and physical realization is not a matter of taste. Once
zero-input relationships have the canonical interface type `() -> A`
(normalized above the kernel to `A`, with the unit eliminated before any
term is typed --- the kernel has no unit type, and `delay` inside a
zero-input declaration is why: a unit binder would forbid memory there,
`delay_not_under_binder`), the form `A -> ()` suggests itself as a
consumer. It cannot name one: in a pure total language every function
into the one-point type is the same function (`unit_codomain_collapse`,
by function extensionality), so two "consumers" are indistinguishable
(`consumers_indistinguishable`), and the evaluation relation has no
effect component (`eval_independent_of_drives`). Naming a receiver needs
an output semantics, and the calculus already has exactly one. Semantic
behavior and physical realization are related by the drive edge and are
not identical.

= Reuse of relational structure
<reuse-of-relational-structure>
A second lamp should reuse the first's behavior without copying it. What
is reused is not a code module but a #emph[structured set of
relationships] --- the lamp's concepts, its declared relationships,
their clocks and their outputs --- with some relationships left open as
ports. This section shows that everything a component needs is derivable
from what §4 already provides, realization plus renaming: instantiation
gives the relationships fresh identities, binding connects an instance
into a larger design by ordinary realization steps, and flattening
yields an ordinary design accepted by the unchanged judgments, so that
composition adds no semantic machinery.

== Equivariance
<equivariance>
A renaming $r$ bundles four maps --- on declaration, semantic, clock and
output identities. Renaming acts on types (through $upright("sem")$), on
terms, on interfaces, on declarations and pointwise on environments;
$Delta . upright("RenamedBy") thick r thick Delta'$ says $Delta'$ stores
the renamed declaration of $Delta$ at the renamed identity.

#strong[Proposition 18 (Equivariance; `HasType.rename`,
`Satisfies.rename`, `Clocked.rename`).] If
$Theta\;Delta\;G\;Gamma tack.r e : tau$ and $Theta'\,Delta'\,G'$ are the
images of $Theta\,Delta\,G$ under $r$ (agreement on the image, with no
injectivity required), then
$Theta'\;Delta'\;G'\;Gamma^r tack.r e^r : tau^r$\; likewise for
satisfaction, and for the domain judgment under a clock environment that
agrees on the declared identities.

Evidence must be equivariant as well (`Evidence.Equivariant`), an
abstract condition beside monotonicity. Nothing else is new in the
composition theory; the rest is definitions over Proposition 18 and §4.

== Components, instances and flattening
<components-instances-and-flattening>
A #strong[port] is a template declaration by local identity with the
public part of its interface and its parameter clock. A #strong[behavior
interface] has required ports (unrealized declarations a composer
binds), provided ports, elaboration-time parameters (unrealized
data-typed declarations bound to closed constants at instantiation) and
clock parameters. A #strong[component] is an interface, a template
design over local identities below a width $W$, and a partition of its
concepts and outputs into private (freshened per instance) and shared.
$upright("Realizes") thick italic(e v) thick cal(C)$ is a predicate over
the existing judgments: the template is a well-formed design
(`Design.WF`: $upright("GlobalWF")$, $Theta . upright("WF")$, well
clocked, causal, $upright("DriveWF")$, $upright("SingleDriver")$), every
required port is an unrealized declaration of the stated interface,
every provided port is declared with it, parameters are unrealized,
data-typed and clock-free.

Instance $k$ of a component maps local identity $n$ to
$upright("fresh") thick W thick k thick n = W dot.op\(k + 1\)+ n$, with
$upright("decode")$ its inverse; distinct instances never share an
identity (`inst_decl_disjoint`). The encoding is a device --- any
injective allocator would do. A #strong[binding] realizes a destination
port of one instance from a source --- a port of another instance or a
closed constant --- with an optional transport: none for a direct
reference in the same or an agnostic domain,
$upright("some") thick italic(i n i t)$ for $upright("sync")$ from the
source's domain. A #strong[system] is a width, a list of instances, a
list of bindings, the shared concept environment and the external
outputs. #strong[Flattening] is the union of the renamed instances
followed by the bindings applied as §4 realization steps: the
destination port is realized as $upright("declRef") thick italic(s r c)$
or
$upright("sync") thick kappa thick italic(i n i t) thick\(upright("declRef") thick italic(s r c)\)$.
The result is a design, consumed by every existing judgment unchanged.

#strong[Theorem 19 (Composition adds no machinery; `binding_satisfies`,
`flatten_WF`, `flatten_causal`, `flatten_wellClocked`,
`flatten_singleDriver`, `open_port_stays_open`).] Under
$upright("ComposeWF")$ --- every instance realizes its interface; every
binding is well formed (types agree; a direct binding's source is in the
destination's domain or agnostic; a transported binding's source has a
domain); external outputs are driven by at most one instance --- and
with evidence that is monotone, equivariant and port-sound (a discharged
commitment survives when a port copy is realized by a reference to a
declaration of the same interface), the flattening is globally well
formed, well clocked, single-driver, causal when the inter-instance
graph is acyclic, and its open ports remain open.

#strong[Theorem 20 (Modular semantics, restricted; `eval_flat_to_inst`,
`eval_inst_to_flat`, `modular_iff_flat`).] For wiring designs with
closure-free inputs and direct bindings, in one domain, the value of a
declaration in an instance evaluated alone with a consistent modular
input equals its value in the flattened system.

The restriction is exact and recorded: transported bindings under
$upright("MEv")$ need a domain-indexed input for the transported port,
and higher-order bodies are not covered --- the same obstacle in both
directions. Substitutability follows the usual contravariance: $B$ may
replace $A$ when every port $A$ provides, $B$ provides at the same type
and clock, and every port $B$ requires, $A$ required; replacing an
instance by a refining component preserves $upright("ComposeWF")$
(`substitute_composeWF`).

The counterexamples that fixed the design
(`Experiments/BehaviorAlternatives.lean`): a name-based identity
collides on double instantiation; a shared clock captured inside a
template cannot be re-bound; a binding across domains without transport
is rejected by $upright("Clocked")$\; two instances driving one external
output violate $upright("SingleDriver")$.

== Groups are the identity, and extraction is a system
<groups-are-the-identity-and-extraction-is-a-system>
A #emph[group] --- a designer's selection of several declarations --- is
authoring metadata: a group identity and a member list beside the
design. Every group operation acts on the list and leaves the design
untouched, so every kernel judgment of the design is the #emph[same
proposition] before and after, each proved by reflexivity
(`group_is_identity_on_design`). A group's boundary is a projection over
a finite enumeration: the non-members some member depends on
($upright("crossIn")$), the members some non-member depends on
($upright("crossOut")$); the aggregate socket a collapsed group shows is
these lists, none of which is a declaration, and
$a in upright("crossIn")$ says #emph[some] member depends on $a$ and
nothing about the others (`socket_no_fanout`). Two encodings of a socket
as a declaration were refuted: as a declaration every member reads, a
member acquires an instantaneous dependency it never had; as a
tuple-returning declaration, the consumer of one member comes to depend
on the inputs of all of them. The kernel has no tuples for boundaries,
and this is a reason not to add them for that purpose.

Packaging a group as a component --- the one semantic step in the
hierarchy declaration → group → component → system --- builds two
#emph[restrictions] of the design, the component with an unrealized copy
of each crossing-in declaration as a required port and the residual with
an unrealized copy of each crossing-out member, and forms a two-instance
system with one direct binding per crossing. No realization is
translated or copied across the boundary. Both templates realize their
inferred interfaces (`restrict_realizes`, needing evidence that depends
only on the interfaces of the referenced declarations,
`Evidence.InterfaceLocal`); the system is a well-formed composition and
its flattening a well-formed design (`system_composeWF`, `flat_WF`);
causality needed its own argument, since a group with both inputs and
outputs is never inter-instance-acyclic, yet the flattened instantaneous
graph is the original with every crossing edge subdivided through a port
copy, and doubling the original rank witnesses it (`flat_causal`);
private members are unobservable from the residual
(`private_unobservable`); and for wiring designs an original declaration
and its home copy evaluate to the same value at every tick
(`orig_iff_flat`).

= Mechanization
<mechanization>
The development is 68 Lean 4 modules (Lean 4.33.1, no dependencies
beyond core): 11 in `Core` (§3--6, §8), 12 in `Behavior` (§9), 19 in
`Surface` (the definitional library, polymorphism, the window and the
boundary constructions above the kernel), 2 in `Validation` (outside
this paper), and 24 experiment modules holding alternatives,
counterexamples and executed examples; about 26 500 lines and 1 545
theorem declarations. It builds with no `sorry`. The axioms are
propositional extensionality and quotient soundness, the latter only
through function extensionality and the choice-free rational quotient
used by the unit laws; classical choice is absent, and the whole
development was re-audited for it at every phase.

Three proof-engineering choices carried the metatheory. $upright("Ev")$
and $upright("MEv")$ are ordinary inductive relations with no mutual
recursion, because the recursor's rule unrolls through the environment
(§6.1); every induction on evaluation extends by one case when a
construct is added, and the transport primitive and the recursor entered
this way with every earlier theorem re-established without a change of
statement. The logical relation is parameterized by an application
relation so that the single- and multi-domain semantics share it, and is
independent of that parameter at data types (`Red_data`), which is the
fact that lets a value cross a tick. Every rejected alternative is a
theorem whose content is a rejection, stated on a concrete design and
discharged by `decide` or by running the interpreters
$upright("evalF")$/$upright("mevalF")$ --- proved sound for the
relations --- inside the checker; there is no test suite beside the
proofs. Several results are recorded as trivial by definition and
reported as such. Extraction is not part of the development; the
production toolchain implements the calculus in Rust and is tested
differentially against the interpreter's traces, a tested claim and not
a theorem.

= Related work
<related-work>
#emph[Modules and signatures.] ML-style module systems separate an
interface from its implementation, and a signature may be written,
checked and depended upon before a structure matches it
@leroy1994manifest@harper1994modules. $lambda_(upright(B D L))$ does not
claim that such systems cannot express an unrealized relationship. The
difference is one of organization: here an unrealized declaration is an
ordinary inhabitant of the #emph[design environment] rather than a
separate compilation unit; its clients are typed against it in the same
environment and, by Theorem 3, remain typed when it is realized; and the
same declaration is simultaneously the carrier of a nominal semantic
signature (§5), a clock assignment (§6) and a drive edge (§8). The
commitment list is a growable part of the interface whose growth is a
first-class step on a declared-but-unrealized name, with a stability
condition imposed on the layer that discharges it.

#emph[Refinement types, contracts and specification.] Refinement type
systems, contracts and specification languages already support
progressively stronger constraints on a definition, and we do not claim
to have invented refinement. BDL's commitments are atomic labels,
deliberately weaker than a refinement predicate; what is specific is
where they attach --- to a persistent relationship declaration whose
realization may be absent --- and what is proved about them: that a
client's discharged commitment survives later realization and
strengthening under a monotonicity condition on evidence that is shown
necessary (Theorems 4--5). The condition is the Kripke-style stability
familiar from logical-relations proofs
@appel2001indexed@ahmed2006stepindexed, imposed here on a validation
layer rather than on a store.

#emph[Synchronous and reactive languages.] The temporal interpretation
of §6 is that of Lustre @halbwachs1991lustre and Esterel
@berry1992esterel: a global logical tick, definitions as streams, memory
as `pre` with an explicit initial value, causality as acyclicity of
instantaneous dependencies; Vélus @bourke2017velus verifies a compiler
for this model, Zélus @bourke2013zelus and mode extensions
@colaco2005state extend it. Functional reactive programming
@elliott1997fran@nilsson2002frp@cooper2006frtime makes signals
first-class values, and typed FRP
@krishnaswami2013frp@jeffrey2012ltl@cave2014fair controls memory through
modal types. In all of these the central authored unit is a computation
--- a node, a stream definition, a signal function --- and clocks are
inferred from how it samples
@colaco2003clocks@biernacki2008clock@caspi1996kahn. In
$lambda_(upright(B D L))$ the authored unit is a declared relationship,
and the temporal machinery exists to interpret it in an authored domain:
there is no signal type because a declaration already is a stream; the
domain is a nominal identity chosen before any rate is known; and the
one transport primitive with its strictly-before rule was chosen because
the alternative exposes a scheduler the designer never authored (Theorem
15). The window buffer of §7.3 does the work that sub-sampling operators
do in Lucid Synchrone, as a derived construction.

#emph[Nominal and abstract types; units of measure.] Nominal type
identity is the ordinary mechanism of a nominal type system
@pierce2002tapl, and the construction grant is the private constructor
of an abstract type @mitchell1988abstract@reynolds1983types. Dimension
types are Kennedy's @kennedy1997units@kennedy2010units, monomorphic in
the kernel and instantiated by matching in surface families (§7.2). None
of these is claimed as novel. Their role here is to keep a relationship
between meanings distinct from a relationship between representations,
and to keep representation arithmetic coherent --- supporting mechanisms
of the relationship-first model, with the erasure and provenance results
(Proposition 8, Theorem 12) and the refuted alternatives (§5.1--5.2) as
the evidence that they do that job.

#emph[Typed holes and live programming.] Hazelnut
@omar2017hazelnut@omar2019live gives a semantics to programs with holes
and to the edit actions that fill them. An unrealized declaration is not
a hole position in a term; it is a declaration whose realization is
absent, referred to by identity and typed by its interface, and the
refinement order plays the role of the edit-action calculus restricted
to the operations under which clients are stable. The two are
complementary: a hole is where a term is incomplete, an unrealized
declaration is where a design is deliberately open.

#emph[Design and modeling languages.] Block-diagram environments,
model-based design and systems-modeling languages @harel1987statecharts
also let a designer connect named quantities before every block is
defined, and we do not claim that they lack relationships. What
$lambda_(upright(B D L))$ adds is a small mechanized calculus for the
progressive-relationship model with explicit metatheory: what a client
may depend on, what a realization may construct, when a value belongs to
the design, and how reuse is derived --- each as a theorem, and each
rejected alternative as a counterexample.

#emph[Effects and expressiveness.] The single-driver discipline is not
an effect system @plotkin2013handlers\; §8 records that effect rows and
action values, in the toy forms tried, add no rejection the drive edge
lacks. The negative results of §7 are statements about whether a
construct is definable from the kernel by a local translation, in the
spirit of Felleisen's expressiveness @felleisen1990expressive, as
mechanized theorems about specific candidates.

= Discussion and limits
<discussion-and-limits>
#emph[What "first-class" means here.] A relationship is first-class as a
#emph[design object]: it has a stable identity, it may be declared,
depended upon, refined, clocked, driven and instantiated, and every
judgment of the calculus is stated over it. It is not a first-class
#emph[value]. Terms refer to declarations by identity and never pass a
declaration as an argument or return one; there is no type of
relationships, no higher-order manipulation of declarations, and the
paper claims none. What is higher-order in the calculus is ordinary:
functions over data, and the one recursor.

#emph[Design versus program.] A program describes one computation. A
design in $lambda_(upright(B D L))$ may contain decisions at different
levels of commitment --- a relationship with a signature only, one with
commitments, one with a realization, one with a clock and an output ---
and the calculus preserves that partially committed structure rather
than requiring it to be resolved before anything is checked. This is not
a claim that conventional programs are fully specified, nor that their
signatures lack meaning; it is that the #emph[progression] from less to
more committed is explicit here and has a metatheory.

#emph[One direction of commitment.] The refinement order formalizes
narrowing: more commitments, a realization, stronger verified
commitments. It does not formalize the family of behaviors a design
leaves open, and the calculus has no denotation of a set of possible
products. Edits --- changing a signature, dropping a commitment,
replacing a realization --- are outside the order, and the calculus
promises nothing about them (Table 2).

The paper's formal claims are further bounded by the following, each
recorded in the development.

- #emph[Causality is conservative for lambda-guarded cycles.]
  `A := λx. A x` is rejected by $upright("Causal")$ although `declRef A`
  evaluates to a closure; Proposition 10 covers strict cycles only.
- #emph[Modular semantics is proved for a fragment.] Theorem 20 holds
  for single-domain wiring designs with direct or constant bindings;
  transported bindings under $upright("MEv")$ and higher-order
  realizations are open.
- #emph[Evidence is abstract.] The kernel imposes monotonicity,
  equivariance and port-soundness on the validation layer's evidence and
  proves nothing about a concrete discharge mechanism.
- #emph[No sums.] Enumerations with payloads are encoded; a kernel sum
  would be one eliminator term former, and its absence is a decision to
  stop where the executed cases stopped.
- #emph[Magnitudes are naturals.] The executable kernel's quantities are
  natural numbers; the unit laws are proved over an abstract scalar
  domain and instantiated symbolically, and floating-point
  implementations are held to toleranced versions above the kernel.
- #emph[No minimality theorem.] "Minimal" means minimal among the
  formalized candidates.
- #emph[Nothing about designers.] The calculus was shaped by a design
  workflow's requirements; whether it serves designers is an empirical
  question no theorem addresses, and no claim about cognitive load,
  productivity or ease is made.

= Conclusion
<conclusion>
$lambda_(upright(B D L))$ is not interesting because it makes every
implementation detail first-class. It is interesting because a typed
semantic relationship can be declared, connected to concepts, depended
upon by other parts of a product, placed in time and bound to a physical
output while its computation is still undecided --- and can then acquire
that computation without disturbing anything built on it. The
intermediate state is a design state, not a broken program state, and
the calculus gives it a semantics in which it is typable, referenceable,
composable, refinable, stable for clients and eventually realizable.

The results are the constraints on that one object, each with its
theorem. Refinement preserves earlier reasoning: a client typed against
a relationship's promise survives its realization unconditionally, and a
client's discharged commitment survives it whenever evidence is positive
in the environment, a condition that cannot be dropped (Theorems 3--5).
Grants preserve semantic integrity: a realization may construct exactly
the concept its signature announces, representation is not meaning, and
no tag is manufactured by evaluation, memory or transport (Theorems 7,
12). Clocks preserve temporal meaning: a relationship's value belongs to
an authored domain, evaluation is deterministic and total on causal
designs, and no scheduler order is observable (Theorems 9, 11, 14, 15).
Outputs make physical effect explicit and single (Theorem 17). Renaming
preserves relational structure under reuse, and composition adds no
machinery (Theorems 19, 20). The mechanized counterexamples --- a
scheduler made visible, an evidence relation destroyed by a valid
realization, a hidden crossing between concepts, three physical outputs
from one design, a lossy summary for every bounded buffer --- record why
each constraint takes the form it does. That these constraints are all
statements about a relationship, and that they have been proved to
compose, is the conceptual unity of the calculus.

#heading(level: 1, numbering: none)[Appendix A --- Theorem index]
<appendix-a-theorem-index>
Every name is a Lean declaration in `KCN-judu/BDL_FV`\; the file is
given per group, and names are unqualified where the namespace is `BDL`.

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
