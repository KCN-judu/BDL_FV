#import "env.typ": *

#heading(level: 1, numbering: none)[Abstract]
<abstract>
When the behavior of an interactive physical product is designed, the
designer often knows #emph[that] one product quantity determines another
before knowing #emph[how]: a lamp's brightness follows its tilt, and
other parts of the design can be built on that relationship long before
its formula is chosen. This paper presents $lambda_(upright("BDL"))$,
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
$lambda_(upright("BDL"))$, the core calculus of the Behavior Design
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
languages interpret definitions as clocked streams. The calculus does
not show that any of these cannot express a declared-but-unrealized
relationship. What it contributes is a direct, compositional semantics
for a workflow in which #emph[concept identity, interface commitment,
delayed realization, temporal structure and physical effect coexist as
facts about one object], together with mechanized proofs that they
interact as the workflow needs. A relationship is representationally a
declaration in an environment, referred to by identity from terms; it is
a first-class #emph[design] object, not a first-class value that terms
pass around, and the paper says so wherever the distinction matters.

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
by the injection $sans("mk")_C$ from a representation type $R$ that the
environment $Theta$ binds to it --- an abstract type with a private
constructor (§5). A #strong[declaration] is a #emph[typed constant]
$delta : tau$ in the global environment $Delta$, with an optional
#emph[definiens]: exactly a proof assistant's `Parameter` before its
`Definition`, except that here the parameter state is the normal one and
giving the definiens is the design step. A declaration of base type,
$delta : C$, is one #emph[inhabitant] of the concept --- one value at
each tick --- and its definiens, when present, is the one term that
produces that value; a declaration without a definiens is an
#emph[axiom] the environment discharges (the product's #emph[Source]). A
declaration of function type is a template applied wherever another
definiens names it. Several constants of one base type are ordinary
(`sensorA : Temperature`, `sensorB : Temperature`,
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
$lambda_(upright("BDL"))$ it is. Let the design $Delta_0$ contain

$ italic("dimByTilt") = chevron.l delta_1\,med chevron.l sans("Tilt") arrow.r sans("Brightness")\,med\[thin\]chevron.r\,med sans("none") chevron.r\,\
italic("tilt") = chevron.l delta_2\,med chevron.l sans("Tilt")\,med\[thin\]chevron.r\,med sans("none") chevron.r\, $

and let the designer now declare and #emph[realize] the light:
$ italic("light") = chevron.l delta_3\,med chevron.l sans("Brightness")\,med\[thin\]chevron.r\,med sans("some") thick\(\(delta_1\)thick\(delta_2\)\)chevron.r . $
The realization of `light` is well typed in $Delta_0$, by T-Ref twice
--- using only
$Delta_0 in.rev delta_1 :\(sans("Tilt") arrow.r sans("Brightness")\)$
and $Delta_0 in.rev delta_2 :\(sans("Tilt")\)$ --- and T-App once:
$ upright("(T-Ref)") & Theta\;Delta_0\;\[thin\]scripts(tack.r)_G delta_1 : sans("Tilt") arrow.r sans("Brightness")\
upright("(T-Ref)") & Theta\;Delta_0\;\[thin\]scripts(tack.r)_G delta_2 : sans("Tilt")\
upright("(T-App)") & Theta\;Delta_0\;\[thin\]scripts(tack.r)_G\(delta_1\)thick\(delta_2\): sans("Brightness") $

The derivation consults $Delta_0$ only through the #emph[type view]
$Delta_0 in.rev delta : tau$ --- the expected type of each declared
identity --- and never asks whether $delta_1$ has a realization. `light`
is a well-formed, typed, referenceable part of the design while
`dimByTilt` has no formula. This is the calculus's thesis made formal,
and the theorem that completes it is stated in §4: when `dimByTilt` is
later realized, or given a commitment, every judgment about `light` in
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
The term language of $lambda_(upright("BDL"))$ is a simply typed
λ-calculus with registered first-order operators. What makes it a
calculus of relationships rather than of functions is not its terms but
the environments they are typed and evaluated against, and the
projections through which each judgment may read them. This section
fixes the syntax, the environments and the typing judgment; the design
content of each environment is developed in the sections that follow.

== Syntax
<syntax>
Figure 1 gives the syntax. Types are those of a simply typed calculus
with booleans, counts and arrows, extended by nominal base types --- the
concepts $C$, type constants distinct by name --- physical quantities
$sans(Q)_d$ over a dimension $d$, and the data formers
$sans("Option")$, $sans("List")$ and $times$. A dimension is an
exponent vector over a fixed finite set of base dimensions (length,
time, angle, mass, temperature in the development); dimensions form an
abelian group under pointwise addition, which is the only structure the
calculus uses.

$  & C in sans("ConceptId") #h(2em) d in sans("Dim") #h(2em) kappa in sans("ClockId") #h(2em) delta in sans("DeclId") #h(2em) o in sans("OutputId")\
tau\,sigma thick upright("::=") thick & sans("Bool") divides sans("Nat") divides tau arrow.r sigma divides C divides sans(Q)_d divides sans("Option") thick tau divides sans("List") thick tau divides tau times sigma\
e thick upright("::=") thick & x divides sans("true") divides sans("false") divides n divides lambda x : tau . thin e divides e thick e divides delta divides sans("rep") thick e divides sans("mk")_C thick e divides p\
divides thick & sans("delay") thick e thick e divides sans("sync")_kappa thick e thick e divides sans("fold") thick e thick e thick e\
p thick upright("::=") thick & sans("lit")_d thin n divides sans("add")_d divides sans("sub")_d divides sans("mul")_(d_1 d_2) divides sans("div")_(d_1 d_2) divides sans("lt")_d divides sans("eq")_tau^(italic("pf")) divides not divides and divides or divides sans("ite")_tau\
divides thick & sans("none")_tau divides sans("some")_tau divides sans("isSome")_tau divides sans("getD")_tau divides sans("nil")_tau divides sans("cons")_tau divides sans("length")_tau divides sans("take")_tau divides sans("drop")_tau divides sans("reverse")_tau divides sans("head")_tau\
divides thick & sans("toList")_tau divides sans("pair")_(tau sigma) divides sans("fst")_(tau sigma) divides sans("snd")_(tau sigma) $

#figcaption[Figure 1. Syntax of $lambda_(upright("BDL"))$. Variables are de
Bruijn indices in the development; the paper writes names. The
superscript $italic("pf")$ on $sans("eq")_tau^(italic("pf"))$ is a proof
that $tau$ is a data type.]

#emph[Notation.] The conventions are those of type theory, and each
letter is bound once, where its object first appears, and never rebound.
Metavariables: $C$ a concept --- a nominal base type, the level of
$sans("ConceptId")$\; $delta$ a constant name (a declaration
identity) and $h$ a declaration record (§3.2); $tau\,sigma$ types and
$R$ a representation, a concept-free data type; $e\,b\,i$ terms, $x$
variables, $v\,w$ values --- a value of concept $C$ is
$sans("mk")_C thin v$ (§6); $kappa$ a clock domain (lowercase $c$ is
avoided, so that no letter reads as an inhabitant of the concept $C$),
$o$ an output, $d$ a dimension, $t$ a tick, $p$ a property, $n$ a
numeral. Environments: $Theta$ the signature of concepts
($Theta\(C\)= R$ binds a representation), $Delta$ the global environment
of constants ($Delta in.rev delta : tau$ declared,
$Delta in.rev delta := b$ defined), $Gamma$ the local context, $G$ the
grant (a set of concepts, written on the turnstile:
$Theta\;Delta\;Gamma scripts(tack.r)_G e : tau$), $upright(K)$ clocks, $S$ the
schedule, $I$ the input, $rho$ the evaluation environment, $Omega$
outputs and $beta$ drive edges (§3.2, §8);
$cal(P) = chevron.l tau\,cal(K) chevron.r$ an interface with its
commitment list (§4), $italic("ev")$ evidence, $eta$ an erasure (§5.2),
$cal(C)$ a component and $k$ an instance index (§9). Keywords and named
judgments are set in sans serif ($sans("mk")$, $sans("sync")_kappa$,
$sans("GlobalWF")$). The ladder of §2 reads, in these letters: $R$
is the type of a type, $C$ is a type, $delta$ is one inhabitant holding
one $v$ per $t$.

Terms are those of the λ-calculus plus five design-specific forms. A
constant name $delta$ refers to a relationship by the identity of its
declaration; nothing about the declaration's interface or realization is
in the syntax, which is what lets a term refer to a relationship that
has no realization yet. The term $sans("rep") thick e$ observes the
representation of a concept value and $sans("mk")_C thick e$ constructs
one --- the elimination and the introduction of the abstract type $C$\;
the value form is $sans("mk")_C thin v$. The term
$sans("delay") thick i thick e$ is the value of $e$ at the previous
activation of the current domain, $i$ before any;
$sans("sync")_kappa thick i thick e$ is the value of $e$ in domain
$kappa$ at $kappa$'s last activation strictly before now, $i$ if none.
The term $sans("fold") thick f thick z thick l$ is the list recursor:
$sans("fold") thick f thick z thick\[x_1\,dots.h\,x_n\]= f thick x_1 thick\(dots.h.c\(f thick x_n thick z\)\)$.
Registered operators $p$ are first-order constants with types; they
never apply a closure.

Two predicates on types recur. A type is #strong[data],
$tau . sans("Data")$, when no arrow occurs in it; a type is
#strong[concept-free], $tau . sans("SemFree")$, when no concept $C$
occurs in it. Both are decidable by structural recursion, and
$\(tau times sigma\). sans("Data") arrow.l.r.double tau . sans("Data") and sigma . sans("Data")$,
$\(sans("List") thick tau\). sans("Data") arrow.l.r.double tau . sans("Data")$
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
  $h = chevron.l delta\,cal(P)\,r chevron.r$: a constant name $delta$,
  an interface $cal(P) = chevron.l tau\,cal(K) chevron.r$ --- the
  expected type and a list of commitments, atomic property labels ---
  and an optional definiens $r$, which is $sans("none")$ or
  $sans("some") thick b$ for a term $b$. A #strong[design] is a global
  environment $Delta$ of declarations, a partial map from constant
  names. Two projections of it are the only views a judgment may take:
  the #emph[type view] $Delta in.rev delta : tau$ (the constant $delta$
  is declared at $tau$), which is all that typing sees, and the
  #emph[realization view] $Delta in.rev delta := b$ (its definiens is
  $b$), which is all that evaluation sees;
  $delta in.not upright("def")\(Delta\)$ says the constant has no
  definiens. An #strong[unrealized] declaration is one without a
  definiens; nothing else distinguishes it.
- A #strong[concept signature] $Theta$ binds each concept, write-once,
  to a representation, $Theta\(C\)= R$. It is well formed,
  $Theta . sans("WF")$, when every bound representation is concept-free
  and data:
  $Theta\(C\)= R arrow.r.double R . sans("SemFree") and R . sans("Data")$.
- A #strong[grant] $G$ is a set of concepts a term may construct. The
  empty grant $diameter$ permits nothing; $upright("grant")\(tau\)$
  permits the concepts in result position of $tau$:
  $upright("grant")\(C\)= { C }$,
  $upright("grant")\(tau arrow.r sigma\)= upright("grant")\(sigma\)$,
  and $upright("grant")\(tau\)= diameter$ otherwise.
- A #strong[clock environment]
  $upright(K) : sans("DeclId") arrow.r sans("Option") thick sans("ClockId")$
  assigns each declaration a domain; $sans("none")$ marks a
  domain-agnostic relationship usable in any domain. A #strong[schedule]
  $S : sans("ClockId") arrow.r bb(N) arrow.r sans("Bool")$ says at
  which global ticks each domain activates. An #strong[input]
  $I : sans("DeclId") arrow.r bb(N) arrow.r sans("Value")$ supplies
  a value for every unrealized declaration at every tick --- the
  environment's realization of the design's inputs.
- An #strong[output environment]
  $Omega : sans("OutputId") arrow.r sans("Option") thick chevron.l italic("accepts") : sans("Ty")\,italic("clock") : sans("ClockId") chevron.r$
  and the #strong[drive edges]
  $beta : sans("DeclId") arrow.r sans("Option") thick sans("OutputId")$
  are introduced in §8.

Typing sees $Theta$, the type view of $Delta$ and $G$. Evaluation sees
the realization view of $Delta$, $I$ and (in several domains) $S$. The
domain judgment sees $upright(K)$. Outputs see $Omega$, $upright(K)$,
the type view of $Delta$ and $beta$. Commitments and evidence are seen
by the satisfaction relation of §4 and by nothing else.

== Typing
<typing>
The typing judgment $Theta\;Delta\;Gamma scripts(tack.r)_G e : tau$ is given in
Figure 2. Rules T-Var, T-Bool, T-Nat, T-Lam and T-App are those of the
simply typed λ-calculus. T-Ref is the only rule that reads $Delta$, and
it reads the type view. T-Rep and T-Mk read $Theta$ through the binding
$Theta\(C\)= R$\; T-Mk additionally requires the grant. T-Prim assigns
each registered operator its type; the dimension algebra is entirely in
that table (Figure 3), so an application of $sans("mul")_(d_1 d_2)$ is
checked by T-App like any other. T-Delay and T-Sync require the type to
be data and the context to be empty; T-Fold types the recursor.

$ frac(Gamma\(x\)= tau, Theta\;Delta\;Gamma scripts(tack.r)_G x : tau) med upright("(T-Var)") #h(2em) frac(, Theta\;Delta\;Gamma scripts(tack.r)_G b : sans("Bool")) med upright("(T-Bool)") #h(2em) frac(, Theta\;Delta\;Gamma scripts(tack.r)_G n : sans("Nat")) med upright("(T-Nat)") $

$ frac(Theta\;Delta\;Gamma\,x : tau scripts(tack.r)_G e : sigma, Theta\;Delta\;Gamma scripts(tack.r)_G lambda x : tau . thin e : tau arrow.r sigma) med upright("(T-Lam)") #h(2em) frac(Theta\;Delta\;Gamma scripts(tack.r)_G f : tau arrow.r sigma quad Theta\;Delta\;Gamma scripts(tack.r)_G a : tau, Theta\;Delta\;Gamma scripts(tack.r)_G f thick a : sigma) med upright("(T-App)") $

$ frac(Delta in.rev delta : tau, Theta\;Delta\;Gamma scripts(tack.r)_G delta : tau) med upright("(T-Ref)") #h(2em) frac(, Theta\;Delta\;Gamma scripts(tack.r)_G p : sans("ty")\(p\)) med upright("(T-Prim)") $

$ frac(Theta\(C\)= R quad Theta\;Delta\;Gamma scripts(tack.r)_G e : C, Theta\;Delta\;Gamma scripts(tack.r)_G sans("rep") thick e : R) med upright("(T-Rep)") #h(2em) frac(C in G quad Theta\(C\)= R quad Theta\;Delta\;Gamma scripts(tack.r)_G e : R, Theta\;Delta\;Gamma scripts(tack.r)_G sans("mk")_C thick e : C) med upright("(T-Mk)") $

$ frac(tau . sans("Data") quad Theta\;Delta\;\[thin\]scripts(tack.r)_G i : tau quad Theta\;Delta\;\[thin\]scripts(tack.r)_G e : tau, Theta\;Delta\;\[thin\]scripts(tack.r)_G sans("delay") thick i thick e : tau) med upright("(T-Delay)") $

$ frac(tau . sans("Data") quad Theta\;Delta\;\[thin\]scripts(tack.r)_G i : tau quad Theta\;Delta\;\[thin\]scripts(tack.r)_G e : tau, Theta\;Delta\;\[thin\]scripts(tack.r)_G sans("sync")_kappa thick i thick e : tau) med upright("(T-Sync)") $

$ frac(Theta\;Delta\;Gamma scripts(tack.r)_G f : tau arrow.r sigma arrow.r sigma quad Theta\;Delta\;Gamma scripts(tack.r)_G z : sigma quad Theta\;Delta\;Gamma scripts(tack.r)_G l : sans("List") thick tau, Theta\;Delta\;Gamma scripts(tack.r)_G sans("fold") thick f thick z thick l : sigma) med upright("(T-Fold)") $

#figcaption[Figure 2. Typing (`HasType`). T-Ref is the only rule reading
$Delta$\; T-Rep and T-Mk the only rules reading $Theta$\; T-Mk the only
rule reading $G$.]

#figure(
  align(center)[#table(
    columns: (25%, 25%, 25%, 25%),
    align: (auto,auto,auto,auto,),
    table.header([operator], [type], [operator], [type],),
    table.hline(),
    [$sans("lit")_d thin n$], [$sans(Q)_d$], [$sans("eq")_tau^(italic("pf"))$], [$tau arrow.r tau arrow.r sans("Bool")$],
    [$sans("add")_d\,med sans("sub")_d$], [$sans(Q)_d arrow.r sans(Q)_d arrow.r sans(Q)_d$], [$sans("ite")_tau$], [$sans("Bool") arrow.r tau arrow.r tau arrow.r tau$],
    [$sans("mul")_(d_1 d_2)$], [$sans(Q)_(d_1) arrow.r sans(Q)_(d_2) arrow.r sans(Q)_(d_1 + d_2)$], [$sans("some")_tau$], [$tau arrow.r sans("Option") thick tau$],
    [$sans("div")_(d_1 d_2)$], [$sans(Q)_(d_1) arrow.r sans(Q)_(d_2) arrow.r sans(Q)_(d_1 - d_2)$], [$sans("getD")_tau$], [$sans("Option") thick tau arrow.r tau arrow.r tau$],
    [$sans("lt")_d$], [$sans(Q)_d arrow.r sans(Q)_d arrow.r sans("Bool")$], [$sans("toList")_tau$], [$sans("Option") thick tau arrow.r sans("List") thick tau$],
    [$sans("length")_tau$], [$sans("List") thick tau arrow.r sans(Q)_0$], [$sans("cons")_tau$], [$tau arrow.r sans("List") thick tau arrow.r sans("List") thick tau$],
    [$sans("head")_tau$], [$sans("List") thick tau arrow.r sans("Option") thick tau$], [$sans("take")_tau\,med sans("drop")_tau$], [$sans(Q)_0 arrow.r sans("List") thick tau arrow.r sans("List") thick tau$],
    [$sans("fst")_(tau sigma)$], [$tau times sigma arrow.r tau$], [$sans("pair")_(tau sigma)$], [$tau arrow.r sigma arrow.r tau times sigma$],
  )]
  , kind: table
  )

#figcaption[Figure 3. Types of the registered operators (`Prim.ty`), abridged.
Dimension algebra lives here and nowhere else. Equality $sans("eq")$ is
available at every data type and the order $sans("lt")$ at quantities
only.]

Three features of Figure 2 carry the rest of the paper.

#emph[The typing boundary.] Typing depends on the type view of
declarations and the representation view of concepts and on nothing else
--- not on realizations, commitments, evidence, clocks or drive edges.
This is the formal content of #emph[relation before realization]: a
reference is typed by the relationship's promise, and the stability of
clients under later realization (Theorem 3) is a direct consequence.

#emph[The construction boundary.] Client code is typed under
$diameter$\; a declaration's realization is typed under the grant
$upright("grant")\(tau\)$ of its own expected type $tau$ (§4.1). A
value of $C$ is therefore constructed only inside a declaration whose
signature announces $C$: the signature is the realization's authority,
and §5 shows what each weaker alternative admits.

#emph[The temporal boundary.] The forms $sans("delay")$ and
$sans("sync")$ are typed only in the empty context and only at data
types. Both restrictions were forced by the totality proof of §6, not
chosen: a delayed closure would have to be transported across ticks, and
a delay under a binder would re-evaluate its operand at the previous
tick in an environment created at the current one. Temporal state
therefore belongs to declarations --- memory is a property of a
relationship, not of a function --- and relationships with inputs are
pointwise --- the arrangement of `pre` in Lustre, where it lives in
nodes rather than in functions @halbwachs1991lustre.

== Inference, uniqueness and monotonicity
<inference-uniqueness-and-monotonicity>
Inference is syntax-directed. A function
$sans("infer") thick Theta thick Delta thick G thick Gamma thick e : sans("Option") thick sans("Ty")$
follows the rules of Figure 2 and needs only decidability of $G$, of
type equality and of $tau . sans("Data")$.

#thm("Proposition", "1")[Inference; `infer_sound`, `infer_complete`,
`HasType.unique`][$sans("infer") thick Theta thick Delta thick G thick Gamma thick e = sans("some") thick tau$
iff $Theta\;Delta\;Gamma scripts(tack.r)_G e : tau$\; hence typing is decidable
and every term has at most one type.]

#proof[Define $sans("infer")$ by structural recursion on $e$,
reading each rule of Figure 2 as an equation: a variable looks up
$Gamma$\; a constant $delta$ looks up $Delta in.rev delta : tau$\; an
application infers $f$ and $a$ and requires the inferred type of $f$ to
be an arrow $tau arrow.r sigma$ with $tau$ the inferred type of $a$\;
$sans("rep") thick e$ requires the inferred type to be a concept $C$ and
returns $Theta\(C\)$\; $sans("mk")_C thick e$ requires $C in G$ and the
inferred type to be $Theta\(C\)$\; a primitive returns its registered
type. #emph[Soundness] ($sans("infer") = sans("some") thick tau$
implies a derivation) is by induction on $e$: in each case the
equation's premises are exactly the rule's premises, and the induction
hypotheses supply the sub-derivations. #emph[Completeness] (a derivation
implies $sans("infer")$ returns its type) is by induction on the
derivation: each rule's premises determine the recursive calls, and the
side conditions the rule checked are the ones $sans("infer")$ tests.
Uniqueness follows from completeness: two derivations of $e : tau_1$ and
$e : tau_2$ give
$sans("infer") thick e = sans("some") thick tau_1 = sans("some") thick tau_2$.
Decidability follows from soundness and completeness together, since
$sans("infer")$ is a total computable function whose result is
compared with $tau$.]

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
relation $italic("ev") thick Delta thick e thick p$ between a design, a
term and a property. Evidence takes the environment because
compositional discharge needs it --- "$A$ is monotone because $B$ is
committed to be monotone" consults $B$'s interface. A realization $e$
#strong[satisfies] $cal(P)$ in $Theta\,Delta\,Gamma$ when it has the
expected type under the grant of that type and every commitment is
discharged:
$ sans("Satisfies") thick italic("ev") thick Theta thick Delta thick Gamma thick e thick cal(P) thick := thick Theta\;Delta\;Gamma scripts(tack.r)_(upright("grant")\(cal(P) . tau\)) e : cal(P) . tau thick and thick forall p in cal(P) . cal(K) . thick italic("ev") thick Delta thick e thick p . $
A declaration is well formed when its body, if any, satisfies its
interface; a design is #strong[globally well formed],
$sans("GlobalWF") thick italic("ev") thick Theta thick Delta$, when
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
$ frac(cal(P) subset.eq.sq cal(P)', chevron.l delta\,cal(P)\,sans("none") chevron.r arrow.r.squiggly chevron.l delta\,cal(P)'\,sans("none") chevron.r) #h(2em) frac(sans("Satisfies") thick italic("ev") thick Theta thick Delta thick Gamma thick e thick cal(P), chevron.l delta\,cal(P)\,sans("none") chevron.r arrow.r.squiggly chevron.l delta\,cal(P)\,sans("some") thick e chevron.r) #h(2em) frac(cal(P) subset.eq.sq cal(P)' quad sans("Satisfies") thick italic("ev") thick Theta thick Delta thick Gamma thick e thick cal(P)', chevron.l delta\,cal(P)\,sans("some") thick e chevron.r arrow.r.squiggly chevron.l delta\,cal(P)'\,sans("some") thick e chevron.r) $
An unrealized declaration may have its interface refined; an unrealized
declaration may be realized by a satisfying computation; a realized
declaration may have its interface strengthened provided the realization
is #emph[re-verified] against the new interface. Strengthening without
re-verification breaks well-formedness, and the counterexample is
mechanized (`naive_breaks_wellformedness`).

Separately from the steps there is a purely structural order with no
satisfaction condition: $sans("DeclLeq") thick h thick h'$ requires
the same name, $h . cal(P) subset.eq.sq h' . cal(P)$, and a write-once
definiens (if $h$ has definiens $e$ then so has $h'$); the pointwise
lifting $Delta subset.eq.sq Delta'$ ($sans("EnvRefines")$)
permits new declarations besides. Storing a refined declaration back
under its name is an environment refinement: if $Delta$ holds $h$ at its
name and $sans("DeclLeq") thick h thick h'$, then
$Delta subset.eq.sq Delta\[h'\]$ (`EnvRefines_update`). This is the one
place identity does any work: it makes the update land on the slot every
reference resolves to, which is what a name does in any environment
semantics.

#thm("Proposition", "2")[The lifecycle is the structural order;
`DeclRefinesStar_iff`][The reflexive--transitive closure of the three
steps, all side conditions checked in $Delta$, relates $h$ to $h'$ iff
$sans("DeclLeq") thick h thick h'$ and $h'$ is well formed in
$Delta$.]

#proof[($arrow.r.double$) Each step preserves the identity,
refines the interface (the type unchanged, the commitment list extended)
and never removes a definiens --- so each step is below
$sans("DeclLeq")$, which is transitive, and each step's side
condition is exactly that the target is well formed. ($arrow.l.double$)
Given $sans("DeclLeq") thick h thick h'$ and $h'$ well formed, write
$h = chevron.l delta\,cal(P)\,r chevron.r$ and
$h' = chevron.l delta\,cal(P)'\,r' chevron.r$ with
$cal(P) subset.eq.sq cal(P)'$. If $r = sans("none")$ and
$r' = sans("none")$, one $sans("refine")$ step suffices. If
$r = sans("none")$ and $r' = sans("some") thick e$, take a
$sans("refine")$ to
$chevron.l delta\,cal(P)'\,sans("none") chevron.r$ followed by a
$sans("realize")$ with $e$, whose side condition --- $e$ satisfies
$cal(P)'$ --- is the well-formedness of $h'$. If
$r = sans("some") thick e$ then $r' = sans("some") thick e$ (a
definiens is never dropped), and one $sans("strengthen")$ step to
$cal(P)'$ suffices, its side condition again being the well-formedness
of $h'$.]

== Client stability
<client-stability>
Another part of the product may already depend on a relationship before
that relationship is realized (§2.2). Can the relationship then be
realized, or strengthened, without editing those clients and without
invalidating what was established about them? The answer has two halves
with deliberately different hypotheses, and together they are the
paper's central result: progress in the design does not destroy the
meaning of earlier design decisions.

#thm("Theorem", "3")[Clients survive realization --- typing;
`local_refinement_preserves_global_typing`][Let $B$ be declared in
$Delta$ with record $h$, and let $h'$ be above $h$ in the structural
order, $sans("DeclLeq") thick h thick h'$. Then every judgment
$Theta\;Delta\;Gamma scripts(tack.r)_G e : tau$ holds in $Delta\[h'\]$, the
design with $B$'s record replaced by $h'$.]

#proof[Let $Delta' = Delta\[h'\]$. For every constant $delta'$,
the type view agrees: if $delta' eq.not B$ then
$Delta' thick delta' = Delta thick delta'$, and if $delta' = B$ then
$Delta' in.rev B : tau$ exactly when $Delta in.rev B : tau$, because
$sans("DeclLeq") thick h thick h'$ keeps the expected type. Now
proceed by induction on the derivation of
$Theta\;Delta\;Gamma scripts(tack.r)_G e : tau$: T-Ref is the only rule that
reads $Delta$, and it reads the type view, which is the same in
$Delta'$\; every other rule is reproduced with the induction hypotheses.
(This is the monotonicity lemma `HasType.mono_env`: typing is preserved
by any change of $Delta$ that preserves the type view.)]

The proof is one line: typing reads $Delta$ through the type view, and
the type view is invariant under $sans("DeclLeq")$. That the proof
is short is the point, not a weakness. The theorem says that the
decision to let clients see a relationship's promise and never its
realization is #emph[sufficient] for every client to survive every
realization and every added commitment, with no side condition. It is
also necessary: change $B$'s expected type while keeping its identity
and every client breaks, which is why the type is frozen in
$subset.eq.sq$ and why changing it is an edit (§4.4).

The commitment half needs more.

#thm("Definition", "")[Monotone evidence][An evidence relation
$italic("ev")$ is #strong[monotone] when, for all designs
$Delta_1 subset.eq.sq Delta_2$ (pointwise refinement,
$sans("EnvRefines")$), every term $e$ and every property $p$,
$italic("ev") thick Delta_1 thick e thick p$ implies
$italic("ev") thick Delta_2 thick e thick p$. Evidence that ignores the
environment is monotone; evidence that consults only the #emph[presence]
of commitments and realizations is monotone; evidence that consults
their #emph[absence] is not.]

#thm("Theorem", "4")[Clients survive realization --- commitments;
`local_refinement_preserves_global_wf`,
`local_lifecycle_preserves_global_wf`][Let $italic("ev")$ be monotone,
let $Delta$ be globally well formed under $italic("ev")$ and $Theta$, let
$B$ be declared in $Delta$ with record $h$, and let
$h arrow.r.squiggly h'$ be a lifecycle step whose side conditions are
checked in $Delta$. Then $Delta\[h'\]$ is globally well formed. The same
holds for a whole lifecycle $h arrow.r.squiggly^(*) h'$ checked against
the original $Delta$.]

#proof[Write $Delta' = Delta\[h'\]$ and note first that
$Delta subset.eq.sq Delta'$ pointwise (`EnvRefines`): every declaration
of $Delta$ is below the corresponding one of $Delta'$, since only $B$
changed and it moved up by $sans("DeclLeq")$. Global well-formedness
of $Delta'$ asks, for every $delta$ with $Delta' in.rev delta := b$,
that $b$ satisfies $delta$'s interface #emph[in $Delta'$]. Two cases. If
$delta = B$, the step's side condition gives that $h'$'s definiens
satisfies $h'$'s interface in $Delta$\; satisfaction is a typing
judgment plus evidence for each commitment, the typing transfers to
$Delta'$ by Theorem 3, and the evidence transfers because $italic("ev")$
is monotone along $Delta subset.eq.sq Delta'$. If $delta eq.not B$, the
declaration is unchanged and was well formed in $Delta$ by hypothesis;
the same two transfers move that fact to $Delta'$. For the lifecycle
version, induct on the sequence of steps with the invariant "the current
environment refines $Delta$, is globally well formed, and still holds
$B$'s record as the steps expect": each step is a single-step instance
whose side conditions, checked in $Delta$, transfer to the current
environment by monotonicity, and updating twice at one name is updating
once.]

#thm("Theorem", "5")[Monotonicity is necessary; `badEv_not_mono`][There
is an evidence relation $italic("ev")_(upright("bad"))$, a globally well
formed two-declaration design, and a valid realization step of one
declaration after which the design is not globally well formed;
consequently $italic("ev")_(upright("bad"))$ is not monotone.]

#proof[Take two declarations
$A : sans("Nat") arrow.r sans("Bool")$, realized and committed to
`total`, and $B : sans("Nat") arrow.r sans("Nat")$, unrealized, with
$A$'s definiens applying $B$. Let
$italic("ev")_(upright("bad")) thick Delta thick e thick p$ hold exactly
when $p$ is `total`, $e$ is $A$'s definiens and $B$ has no definiens in
$Delta$. The two-declaration design is globally well formed under
$italic("ev")_(upright("bad"))$ (a finite check). Realizing $B$ with the
identity function is a valid $sans("realize")$ step: its side
condition is checked in the original environment, where $B$ is
unrealized. In the updated environment $B$ has a definiens, so
$italic("ev")_(upright("bad"))$ no longer discharges `total` for $A$, and
the design is not globally well formed. Were
$italic("ev")_(upright("bad"))$ monotone, Theorem 4 would contradict
this; hence it is not.]

The relation $italic("ev")_(upright("bad"))$ discharges "$A$ is total"
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
($sans("Unfolds") thick Delta thick e thick e'$). Let
$sans("DependsOn") thick Delta thick a thick b$ hold when the body
of $a$ refers to $b$.

#thm("Proposition", "6")[Unfolding; `Unfolds.det`,
`Unfolds.exists_of_acyclic`, `Unfolds.not_of_cyclic`,
`Unfolds.refFree_of_fullyRealized`][Unfolding is deterministic; on the
delay-free fragment it exists iff the reference graph is acyclic; a
reference on a cycle through realized declarations has no unfolding at
all; and a fully realized well-typed design unfolds to a reference-free
program of the same type.]

#proof[Unfolding is the least relation that copies every
syntactic form, leaves an unrealized constant in place, and replaces a
realized constant by the unfolding of its definiens. #emph[Determinism]:
induction on one unfolding derivation, inverting the other; at a
constant, the definiens is determined by $Delta$. #emph[Existence under
acyclicity]: an acyclic $Delta$ comes with a rank that strictly
decreases along every reference edge; prove, by strong induction on a
bound $n$, that every term whose referenced constants all have rank
below $n$ unfolds --- the structural cases pass the bound to their
subterms, and a realized constant $delta$ of rank below $n$ has a
definiens whose references have rank below
$italic("rank")\(delta\)< n$, so the inner induction hypothesis
applies. #emph[No unfolding on a cycle]: an unfolding of $delta$ carries
a derivation whose referenced constants are not on a cycle through
$delta$ (proved by induction on the derivation: the only way to pass
through a realized constant is to unfold it, and the result's references
are those of the definiens, so a reference back to $delta$ would give a
smaller derivation of the same shape, which is impossible); a constant
reaching itself contradicts this. #emph[Reference-freeness]: if every
constant is realized, no `refStuck` case can occur, so the result
mentions no constant; its type is preserved because each unfolding step
replaces a constant by a definiens of the same type, typed under the
universal grant.]

Acyclicity is witnessed by a rank that strictly decreases along edges,
$sans("Acyclic") thick Delta := exists thin italic("rank") . thick forall a thin b . thick sans("DependsOn") thick Delta thick a thick b arrow.r italic("rank") thick b < italic("rank") thick a$,
and excludes cycles (`Acyclic.not_cyclic`). The pure fragment has no
fixpoints, so a cyclic definition denotes nothing; §6 shows which cycles
become meaningful once $sans("delay")$ exists, and that unfolding
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
`MotorAngle` are both $sans(Q)_(sans("Angle"))$. Then the wire
`motorTarget := tiltSensor` is well typed and the design is globally
well formed, because nothing in the model records the distinction the
designer drew. Nominal types $C$ over an internal identity record it:
two distinct identities are distinct types regardless of representation,
so the invalid wire is rejected by T-App with no additional judgment. An
explicit relationship `tiltToMotor : Tilt -> MotorAngle` is an ordinary
declaration of arrow type --- signature-first, possibly unrealized ---
and it appears in the term wherever a crossing occurs. The kernel has no
cast, coercion or conversion.

#emph[Why not let any realization construct any concept of matching
representation?] Nominal identity alone leaves concept values opaque:
under T-Ref and T-App only, a value of $C$ can originate only in a
declaration of concept type (`no_semantic_value_without_declaration`).
That is the right state #emph[before] a realization exists. To let a
formula realize a relationship, representation must be observable and
constructible, and the obvious way to add it destroys what identity has
bought. With global $sans("rep")_C : C arrow.r R$ and
$sans("mk")_C : R arrow.r C$ available everywhere,
$lambda x . thick sans("mk")_(upright("Motor"))\(sans("rep")_(upright("Tilt")) thick x\)$
is a well-typed `Tilt -> MotorAngle` in the empty environment with no
declared relationship
(`unrestricted_representation_binding_bypasses_semantic_identity`), and
the crossing can hide inside a body whose signature mentions no motor
(`hidden_crossing_inside_unrelated_body`). Observation alone is safe but
cannot realize a mapping.

The grant separates the two, and its design reading is #emph[realization
authority]: the signature the designer wrote before any computation
existed is what authorizes the computation's result. Observation
$sans("rep")$ is typed everywhere (T-Rep); construction $sans("mk")_C$ is
typed only where $C in G$ (T-Mk); client code is typed under $diameter$
and a realization of type $tau$ under $upright("grant")\(tau\)$, the
grant of its own signature (the definition of
$sans("Satisfies")$). A realization of `Tilt -> Brightness` may
construct a `Brightness` and nothing else --- not a `MotorAngle`, not an
`Opacity`, whatever their representations. Let
$e . sans("constructs") thick C$ hold when $sans("mk")_C$ occurs
in $e$.

#thm("Theorem", "7")[Realization authority;
`HasType.constructs_granted`][If
$Theta\;Delta\;Gamma scripts(tack.r)_G e : tau$ and
$e . sans("constructs") thick C$, then $C in G$. Under
$upright("grant")\(tau\)$: a value of $C$ is built only inside a
realization whose signature announces $C$.]

#proof[By induction on the typing derivation, with
$e . sans("constructs") thick C$ meaning that $sans("mk")_C$
occurs somewhere in $e$. The only rule that introduces $sans("mk")_C$ is
T-Mk, whose premise is $C in G$\; every other rule leaves the grant
unchanged for its subterms, so an occurrence inside a subterm is handled
by the induction hypothesis at the same $G$. Under
$G = upright("grant")\(tau\)$ for a definiens of type $tau$,
$C in upright("grant")\(tau\)$ says that $C$ is the result concept of
$tau$, i.e.~that the signature announces it.]

The hidden crossing above is rejected under the grant of an unrelated
declaration and becomes legal, and visible, once `tiltToMotor` is
declared (`hidden_crossing_rejected_under_grant`,
`representation_binding_does_not_enable_hidden_semantic_mapping`).

Two constraints on representations in $Theta . sans("WF")$ were not
anticipated. Representations must be concept-free: if `Tilt` may be
represented #emph[by] `MotorAngle`, then $sans("rep")$ itself is a
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
Let $eta : sans("ConceptId") arrow.r sans("Ty")$ map each concept
to a data type, agreeing with $Theta$ on bound concepts. Erasure
$tau^eta$ replaces each concept $C$ by $eta\(C\)$ throughout a type; on
terms, $sans("rep") thick e$ and $sans("mk")_C thick e$ erase to $e^eta$,
and the type indices of operators are erased.

#thm("Proposition", "8")[Erasure is sound; `HasType.erase`][If
$Theta . sans("WF")$, $eta$ agrees with $Theta$, and
$Theta\;Delta\;Gamma scripts(tack.r)_G e : tau$, then
$Theta\;Delta^eta\;Gamma^eta scripts(tack.r)_(G') e^eta : tau^eta$ for every
grant $G'$.]

#proof[By induction on the derivation. Erasure maps each concept
$C$ to $eta\(C\)$, agreeing with $Theta$ where the latter is defined,
and replaces $sans("mk")_C thick e$ by $e^eta$ and $sans("rep") thick e$
by $e^eta$. In the T-Mk case the premise types $e$ at $Theta\(C\)= R$\;
since $Theta$ is well formed, $R$ is concept-free, so
$R^eta = R = eta\(C\)= C^eta$, and the erased term $e^eta$ has the
erased type. The T-Rep case is symmetric. T-Ref uses the erased type
view $Delta^eta$, and no rule needs the grant after erasure, so any $G'$
serves. All remaining rules commute with erasure syntactically.]

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
$\(lambda x . thin x\)thick italic("tilt")$ has the same flow with no
direct wire (`bweak_evaded_by_eta`); a compositional role judgment
strong enough to close that gap has the rule shapes of typing over the
concept types and duplicates it.

== Dimensions: coherent arithmetic on representations
<dimensions-coherent-arithmetic-on-representations>
Dimensions play a narrower role than concept identity. Once a concept is
observed through $sans("rep")$, the arithmetic on its representation
must remain physically coherent, and that is all dimensions do. A
physical quantity has type $sans(Q)_d$. There is no dimension-specific
typing rule:
$sans("add")_d : sans(Q)_d arrow.r sans(Q)_d arrow.r sans(Q)_d$,
$sans("mul")_(d_1 d_2) : sans(Q)_(d_1) arrow.r sans(Q)_(d_2) arrow.r sans(Q)_(d_1 + d_2)$
and $sans("div")_(d_1 d_2)$ with $d_1 - d_2$ are registered operators,
and an application is checked by T-App. `length + time` is ill typed
(`dimension_mismatch_rejected`); erasing every dimension to the zero
vector is a sound translation that accepts it
(`counterexampleB_baseline_accepts_length_plus_time`), so the untyped
numeric baseline is the erasure of dimensional typing in the same sense
that it is the erasure of nominal typing.

Dimension and identity are orthogonal, and the orthogonality is what the
relationship-first reading needs: `Tilt` and `MotorAngle` both bound to
$sans(Q)_(sans("Angle"))$ remain distinct types
(`same_dimension_does_not_imply_same_semantic_identity`); a relationship
realized by the dimensioned formula
$lambda x . thick sans("mk") thick sans("Brightness") thick\(sans("rep") thick x dot.op italic("gain")\)$
with $italic("gain") : sans(Q)_(0 - sans("Angle"))$ is typed, a
dimension error inside it is caught by the same typing, and the formula
cannot manufacture a `MotorAngle` despite the shared dimension
(`explicit_semantic_mapping_uses_dimensioned_formula`). The association
between a concept and its dimension lives in $Theta$, not in the
identity and not in the type constructor: the designer says #emph[tilt
to brightness] first and #emph[tilt is an angle] separately.

Units are not in the calculus at all. A literal `90 deg` elaborates to
$sans("lit")_(sans("Angle"))$ of a scaled magnitude; a coordinate
$sans("inUnit")\(q\,u\)$ is $q$ divided by a scale constant and has
dimension zero; $sans("withUnit")\(x\,u\)$ is the converse; a
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
Values are booleans, naturals (which also carry every $sans(Q)_d$\; the
executable kernel's magnitudes are naturals), tagged concept values
$sans("mk")_C thin v$, $sans("none")$, $sans("some") thick v$, lists,
pairs, closures $sans("clo") thick rho thick e$ over a value
environment, and partially applied operators
$sans("prim") thick p thick arrow(v)$. An operator is computed when
saturated: $sans("applyPrim") thick p thick arrow(v)$ is
$sans("compute") thick p thick arrow(v)$ if $\|arrow(v)\|$ equals
$p$'s arity and $sans("prim") thick p thick arrow(v)$ otherwise.

The judgment $rho scripts(tack.r)_t e arrow.b.double v$ --- the value of $e$ at
tick $t$ under local environment $rho$, with the design $Delta$ and the
input $I$ ambient --- is defined in Figure 4 (`Ev`).

$ frac(rho\(x\)= v, rho scripts(tack.r)_t x arrow.b.double v) #h(2em) frac(, rho scripts(tack.r)_t lambda x : tau . thin e arrow.b.double sans("clo") thick rho thick e) #h(2em) frac(, rho scripts(tack.r)_t p arrow.b.double sans("applyPrim") thick p thick\[thin\]) $

$ frac(rho scripts(tack.r)_t f arrow.b.double sans("clo") thick rho' thick b quad rho scripts(tack.r)_t a arrow.b.double w quad w thin upright("::") thin rho' scripts(tack.r)_t b arrow.b.double v, rho scripts(tack.r)_t f thick a arrow.b.double v) #h(2em) frac(rho scripts(tack.r)_t f arrow.b.double sans("prim") thick p thick arrow(u) quad rho scripts(tack.r)_t a arrow.b.double w, rho scripts(tack.r)_t f thick a arrow.b.double sans("applyPrim") thick p thick\(arrow(u) + #h(-0.167em) #h(-0.167em) +\[w\]\)) $

$ frac(Delta in.rev delta := b quad\[thin\]scripts(tack.r)_t b arrow.b.double v, rho scripts(tack.r)_t delta arrow.b.double v) med upright("(E-Real)") #h(2em) frac(delta in.not upright("def")\(Delta\), rho scripts(tack.r)_t delta arrow.b.double I thick delta thick t) med upright("(E-Input)") $

$ frac(rho scripts(tack.r)_t e arrow.b.double sans("mk")_C thin w, rho scripts(tack.r)_t sans("rep") thick e arrow.b.double w) #h(2em) frac(rho scripts(tack.r)_t e arrow.b.double w, rho scripts(tack.r)_t sans("mk")_C thick e arrow.b.double sans("mk")_C thin w) $

$ frac(rho scripts(tack.r)_0 i arrow.b.double v, rho scripts(tack.r)_0 sans("delay") thick i thick e arrow.b.double v) med upright("(E-Delay0)") #h(2em) frac(rho scripts(tack.r)_t e arrow.b.double v, rho scripts(tack.r)_(t + 1) sans("delay") thick i thick e arrow.b.double v) med upright("(E-DelayS)") $

$ frac(rho scripts(tack.r)_t f arrow.b.double v_f quad rho scripts(tack.r)_t z arrow.b.double v_z quad rho scripts(tack.r)_t l arrow.b.double sans("list") thin\[thin\], rho scripts(tack.r)_t sans("fold") thick f thick z thick l arrow.b.double v_z) med upright("(E-FoldNil)") $

$ frac(rho scripts(tack.r)_t f arrow.b.double v_f quad rho scripts(tack.r)_t z arrow.b.double v_z quad rho scripts(tack.r)_t l arrow.b.double sans("list") thin\(x thin upright("::") thin italic("xs")\)\
 \[sans("list") thin italic("xs")\,thin v_z\,thin v_f\]scripts(tack.r)_t sans("fold") thick\#2 thick\#1 thick\#0 arrow.b.double r #h(2em)\[r\,thin x\,thin v_f\]scripts(tack.r)_t\#2 thick\#1 thick\#0 arrow.b.double v, rho scripts(tack.r)_t sans("fold") thick f thick z thick l arrow.b.double v) med upright("(E-FoldCons)") $

#figcaption[Figure 4. Single-domain evaluation (`Ev`), with $Delta$ and $I$
ambient. In one domain $sans("sync")_kappa$ evaluates exactly as
$sans("delay")$ (rules `syncZero`, `syncSucc`), which §6.7 justifies.
Literals evaluate to themselves. The variable $\#i$ is de Bruijn index
$i$.]

Three points of Figure 4 deserve comment. An unrealized declaration is
an #emph[input]: E-Input reads $I thick delta thick t$, the
environment's realization of the relationship. A realized declaration is
evaluated from its realization at the current tick in the #emph[empty]
environment (E-Real): a reference's value never depends on the local
environment of the reader, which is what makes a relationship a stream
the design observes rather than a function of its call site
(`Ev.declRef_env_irrelevant`). And $sans("delay")$ shifts the tick:
read at $t + 1$, it evaluates its operand at $t$\; at $0$ it evaluates
the initial value.

The recursor's rule unrolls syntactically. Rather than a recursive
definition of a fold on values, the rule evaluates the syntactic term
$sans("fold") thick\#2 thick\#1 thick\#0$ in an environment holding the
tail, the seed and the function, and then the term
$\#2 thick\#1 thick\#0$ in an environment holding the result, the head
and the function. This keeps $sans("Ev")$ an ordinary inductive relation
with no mutual recursion, so every proof by induction on $sans("Ev")$
that predated the recursor extends by one case, and totality is a
separate lemma by induction on the list (§7.1).

#thm("Theorem", "9")[Determinism; `Ev.det`][If
$rho scripts(tack.r)_t e arrow.b.double v_1$ and
$rho scripts(tack.r)_t e arrow.b.double v_2$ then $v_1 = v_2$.]

#proof[By induction on the first derivation, inverting the
second: each syntactic form has at most one applicable rule per tick
(for $sans("delay")$ and $sans("sync")$ the tick decides between the
initial and the successor rule, and for a constant the presence of a
definiens decides between E-Real and E-Input), the environment lookup,
the input and the definiens are functions, and the induction hypotheses
identify the values of the premises.]

Evaluation is a partial function with no hidden evaluation order ---
there are no effects to order --- and this holds unconditionally.

An executable interpreter $sans("evalF")$ with a fuel parameter is
proved sound for the relation (`evalF_sound`, `Ev.of_evalF`). Every
trace in the development and in this paper was computed by it inside the
proof checker.

== Cycles and causality
<cycles-and-causality>
Let $e . sans("instRefs")$ be the declarations $e$ refers to
#emph[instantaneously]: those not under the delayed operand of a
$sans("delay")$ or $sans("sync")$ (the initial value is read at tick
$0$ and counts as instantaneous). The relation
$sans("InstDependsOn") thick Delta thick a thick b$ holds when
$b$ is among the instantaneous references of $a$'s definiens.

#thm("Definition", "")[Causal][A design $Delta$ is #strong[causal] when
there are a rank $italic("rank")$ on constant names and a bound $R$
with $italic("rank") thick delta < R$ for every $delta$, such that
every instantaneous dependency strictly decreases the rank:
$sans("InstDependsOn") thick Delta thick a thick b$ implies
$italic("rank") thick b < italic("rank") thick a$. We write
$sans("Causal") thick Delta$, and say that $italic("rank")\,R$
witness it.]

On the delay-free fragment $sans("InstDependsOn")$ is
$sans("DependsOn")$, so causality is exactly bounded acyclicity
(`Causal_iff_acyclic_of_delayFree`): the earlier condition is the
timeless special case rather than a replaced requirement. A structural
cycle every path of which passes through a delayed operand ---
`A := delay 0 B; B := A`, or a self-delayed accumulator --- is causal. A
cycle that is partly delayed is not.

#thm("Proposition", "10")[Strict cycles have no value;
`Ev.not_of_strictCyclic`][If a constant $delta$ lies on a cycle of
references passing through neither a delayed operand nor a lambda, then
for every tick $t$ and environment $rho$ there is no $v$ with
$rho scripts(tack.r)_t delta arrow.b.double v$.]

#proof[Every derivation of $rho scripts(tack.r)_t e arrow.b.double v$
carries the invariant that no #emph[strict] reference of $e$ --- a
reference not under a delayed operand or a lambda --- lies on a strict
cycle: E-Real passes from $delta$ to the strict references of its
definiens, so a strict path from $delta$ back to $delta$ would yield a
strictly smaller derivation of the same conclusion, which is impossible
by induction; the delay rules read their operand at an earlier tick and
do not count as strict; a lambda's body is not evaluated. A constant on
a strict cycle violates the invariant at the root.]

Not "some default", not "one of several": no derivation exists. A gap
should be recorded. A cycle guarded by a lambda, `A := λx. A x`, is
rejected by $sans("Causal")$ yet `declRef A` does evaluate --- to a
closure; only applying it diverges. The judgment $sans("Causal")$ is
conservative for lambda-guarded cycles, and Proposition 10 covers strict
cycles only.

== The logical relation and totality
<the-logical-relation-and-totality>
Totality is proved by a logical relation indexed by the tick. The
relation is stated generically in an #emph[application relation]
$A : sans("Value") arrow.r sans("Value") arrow.r sans("Value") arrow.r sans("Prop")$
--- how a function value applied to an argument yields a result --- so
that the single-domain and multi-domain semantics share one relation. At
a fixed tick, $A$ is $sans("Apply") thick Delta thick I thick t$:
$v_f$ applied to $w$ yields $v$ when $v_f$ is a closure whose body
evaluates to $v$ at $t$ under $w$, or a partial operator whose
saturation is $v$.

$ cal(R)_Theta^A\[sans("Bool")\]thick v arrow.l.r.double & exists b . thick v = sans("Bool") thick b\
cal(R)_Theta^A\[sans("Nat")\]thick v thick = thick cal(R)_Theta^A\[sans(Q)_d\]thick v arrow.l.r.double & exists n . thick v = sans("Nat") thick n\
cal(R)_Theta^A\[sans("Option") thick tau\]thick v arrow.l.r.double & v = sans("none") thick or thick exists w . thick v = sans("some") thick w and cal(R)_Theta^A\[tau\]thick w\
cal(R)_Theta^A\[sans("List") thick tau\]thick v arrow.l.r.double & exists arrow(w) . thick v = sans("List") thick arrow(w) and forall w in arrow(w) . thick cal(R)_Theta^A\[tau\]thick w\
cal(R)_Theta^A\[tau times sigma\]thick v arrow.l.r.double & exists x thin y . thick v = sans("pair") thick x thick y and cal(R)_Theta^A\[tau\]thick x and cal(R)_Theta^A\[sigma\]thick y\
cal(R)_Theta^A\[tau arrow.r sigma\]thick v arrow.l.r.double & forall w . thick cal(R)_Theta^A\[tau\]thick w arrow.r exists v' . thick A thick v thick w thick v' and cal(R)_Theta^A\[sigma\]thick v'\
cal(R)_Theta^A\[C\]thick v arrow.l.r.double & exists w . thick v = sans("mk")_C thin w and forall R . thick Theta\(C\)= R arrow.r cal(R)^A\[R\]thick w $

The concept clause says that a concept value is a tagged representation
value. Its inner use of the relation at the representation $R$ is the
concept-free relation $sans("RedSF")$\; because $Theta . sans("WF")$
makes $R$ concept-free, the definition is well founded on the type
without appeal to $Theta$ (`Red_semFree`). At data types the relation is
independent of $A$ (`Red_data`), which is what allows a delayed value to
be transported between ticks. Registered operators are related at their
types for any $A$ that saturates them (`Red_prim`).

Well-typed inputs are inputs related to the type view:
$Delta in.rev delta : tau and delta in.not upright("def")\(Delta\)arrow.r.double cal(R)_Theta^(sans("Apply") thick Delta thick I thick t)\[tau\]thick\(I thick delta thick t\)$
for every $t$.

#thm("Theorem", "11")[Totality under causality; `fundamental`,
`reactive_total`, `Ev.red`][Let $Theta . sans("WF")$, let
$italic("rank")\,R$ witness $sans("Causal") thick Delta$, let
$sans("GlobalWF") thick italic("ev") thick Theta thick Delta$ and
let $I$ be well typed. Then for every tick $t$, bound $r$, grant $G$,
and $Theta\;Delta\;Gamma scripts(tack.r)_G e : tau$, and every $rho$ related to
$Gamma$ such that every instantaneous reference of $e$ has rank below
$r$, there is $v$ with $rho scripts(tack.r)_t e arrow.b.double v$ and
$cal(R)_Theta^(sans("Apply") thick Delta thick I thick t)\[tau\]thick v$.]

#emph[Proof.] Let $cal(R)_Theta\[tau\]thick v$ be the logical relation
of §6.3 at the application relation of the single-domain semantics:
booleans and numbers are related at $sans("Bool")$, $sans("Nat")$ and
$sans(Q)_d$\; optionals, lists and pairs componentwise; a value at
$tau arrow.r sigma$ is related when applying it to any value related at
$tau$ yields a value related at $sigma$\; a value at a concept $C$ is
$sans("mk")_C thin w$ with $w$ related at the representation $Theta\(C\)$
through the concept-free relation. Prove the stronger statement:
#emph[for every tick $t$ and bound $r$, every well-typed $e$ whose
instantaneous references have rank below $r$ evaluates, in every
environment related to its context, to a value related to its type.] The
proof is a triple induction --- strong induction on $t$, inside it
strong induction on $r$, inside that induction on the typing derivation
--- and the two outer inductions are what the two temporal constructs
need.

#emph[Constant] (T-Ref). If $delta$ has no definiens, its value is the
input $I thick delta thick t$, related by the hypothesis on inputs.
Otherwise its definiens $b$ is typed under $upright("grant")\(tau\)$
at top level by global well-formedness; causality gives
$italic("rank")\(delta'\)< italic("rank")\(delta\)< r$ for every
instantaneous reference $delta'$ of $b$, so the inner induction
hypothesis at bound $italic("rank")\(delta\)$ evaluates $b$ in the
empty environment, and E-Real lifts the result to $delta$.

#emph[Delay] (T-Delay). At tick $0$ the initial value's derivation gives
the result. At tick $t' + 1$ the operand is evaluated at tick $t'$ by
the #emph[outer] induction hypothesis, with the full bound $R$ --- a
delayed operand may reference anything, since its reference is not
instantaneous --- and the value is related at $tau$ because $tau$ is a
data type, at which the relation does not depend on the application
relation (`Red_data`), so relatedness transports across ticks.

#emph[Application] (T-App). The function's value is related at
$tau arrow.r sigma$ and the argument's at $tau$\; the definition of the
relation at arrow type yields a result value and its relatedness at
$sigma$. #emph[Abstraction] produces a closure, related at the arrow
type by the induction hypothesis applied to any related argument.
#emph[Rep] and #emph[Mk] move between a concept and its representation
using the concept clause of the relation; #emph[primitives] are related
at their types because each registered operator is total on related
arguments (`Red_prim`); #emph[fold] is an inner induction on the list
value.

`reactive_total` instantiates this at $e = delta$, bound $R$, empty
environment; `Ev.red` combines it with determinism to say that
#emph[the] value of a well-typed term is related. $square.stroked.tiny$

Consequently, in a causal, globally well formed design with well-typed
inputs, every declared relationship has a value at every tick, and that
value --- unique by Theorem 9 --- is related to its expected type.

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
$cal(R)^(sans("Apply") thick Delta thick I thick t)$ that must be
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

Initialization is semantic, not validation. Every $sans("delay")$
carries an explicit initial value. Two toy relations without one show
why: the first tick is either undefined
(`first_tick_undefined_without_init`) or nondeterministic
(`first_tick_nondeterministic_without_init`).

== Provenance through time
<provenance-through-time>
State carries semantic tags; it never creates them. Let
$v . sans("Taints") thick C$ hold when the tag $C$ occurs anywhere
inside $v$ --- including inside closures' environments and bodies.

#thm("Theorem", "12")[Semantic integrity over time; `Ev.tag_provenance`,
`temporal_state_preserves_semantic_identity`][If no realization in
$Delta$ constructs $C$, no input value is tainted by $C$, $e$ does not
construct $C$ and $rho$ is clean, then every value
$rho scripts(tack.r)_t e arrow.b.double v$ is clean. In particular a delayed
value carries exactly the tag of the value delayed.]

#proof[Say a value is #emph[tainted] by $C$ when a $sans("mk")_C$
tag occurs inside it --- including inside a closure's environment, and
counting a closure whose body could construct $C$. Prove by induction on
the evaluation derivation that if $e$ does not construct $C$ and the
environment is clean, the result is clean. The literal, variable and
primitive cases are immediate (a registered operator builds no tag). A
closure is clean because its body does not construct $C$ and its
environment is clean. Application evaluates a clean closure's body in a
clean environment. A constant with a definiens is evaluated from that
definiens, clean by hypothesis on $Delta$\; a constant without one
yields an input, clean by hypothesis on $I$. The forms $sans("delay")$
and $sans("sync")$ evaluate either the initial value or the operand at
an earlier tick, both covered by the induction. Observation
$sans("rep")$ strips a tag, and $sans("mk")_(C')$ with $C' eq.not C$ adds
a foreign one; neither introduces $C$. The statement about a delayed
value carrying exactly the tag of the value delayed is the successor
case read directly.]

Combined with Theorem 7 this is the runtime half of semantic integrity:
a concept appears in a value only if some signature announces it or some
input carries it, at every tick. The typing rule
$sans("delay") : tau arrow.r tau arrow.r tau$ at data $tau$ gives the
static half --- a delayed tilt is a tilt, and a backward difference over
a time step has dimension $sans("Length") - sans("Time")$ with no
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
$S : sans("ClockId") arrow.r bb(N) arrow.r sans("Bool")$ saying at
which global ticks each domain activates. A period $n$ induces the
schedule $t med mod med n = 0$ (`Sched.periodic`); the schedule lives
outside the design. Domain-local time is not a separate counter but the
sequence of a domain's activations. The last activation of $kappa$
strictly before $t$ is
$ sans("prevAct") thick S thick kappa thick 0 = sans("none")\,#h(2em) sans("prevAct") thick S thick kappa thick\(t + 1\)= sans("if") thick S thick kappa thick t thick sans("then") thick sans("some") thick t thick sans("else") thick sans("prevAct") thick S thick kappa thick t\, $
with
$sans("prevAct") thick S thick kappa thick t = sans("some") thick t' arrow.r.double t' < t and S thick kappa thick t'$.

Each declaration is assigned a domain by the clock environment
$upright(K)$, or none if it is a domain-agnostic relationship usable
anywhere. The clock is interface data in every sense that matters ---
clients' validity depends on it, it is frozen under refinement, and
changing it is an edit (Table 2) --- and it is stored as a projection
beside the interface, as a concept's representation is stored in $Theta$
rather than in the type.

The #strong[domain judgment]
$sans("Clocked") thick upright(K) thick kappa thick e$, for
$kappa : sans("Option") thick sans("ClockId")$, says that $e$ may
be evaluated in domain $kappa$:
$ sans("Clocked") thick upright(K) thick kappa thick\(delta\)arrow.l.r.double & upright(K) thick delta = sans("none") thick or thick upright(K) thick delta = kappa\
sans("Clocked") thick upright(K) thick\(sans("some") thick kappa\)thick\(sans("delay") thick i thick e\)arrow.l.r.double & sans("Clocked") thick upright(K) thick\(sans("some") thick kappa\)thick i and sans("Clocked") thick upright(K) thick\(sans("some") thick kappa\)thick e\
sans("Clocked") thick upright(K) thick\(sans("some") thick kappa\)thick\(sans("sync")_(kappa') thick i thick e\)arrow.l.r.double & sans("Clocked") thick upright(K) thick\(sans("some") thick kappa\)thick i and sans("Clocked") thick upright(K) thick\(sans("some") thick kappa'\)thick e\
sans("Clocked") thick upright(K) thick sans("none") thick\(sans("delay") thick i thick e\)arrow.l.r.double & sans("False") #h(2em) #h(2em) sans("Clocked") thick upright(K) thick sans("none") thick\(sans("sync")_(kappa') thick i thick e\)arrow.l.r.double sans("False") $
and homomorphically elsewhere. A reference stays in its domain or is
agnostic; a delay needs a domain; $sans("sync")_(kappa')$ switches the
domain of its operand. A design is well clocked when every realization
is clocked in its own declaration's domain. Typing is unchanged and
blind to domains: the direct wire between two domains at the same value
type is well typed and rejected only by $sans("Clocked")$. Placing
the domain in the type instead was tried and set aside: every
domain-agnostic relationship would then need clock polymorphism
(`clocked_type_forces_polymorphism`), and nothing the type rejects is
missed by the judgment.

== Multi-domain evaluation
<multi-domain-evaluation>
The judgment $rho scripts(tack.r)_t^kappa e arrow.b.double v$ --- in domain
$kappa$ at global tick $t$, with $S$, $Delta$, $I$ ambient --- is
$sans("Ev")$ with the two temporal rules replaced by four (`MEv`):
$ frac(sans("prevAct") thick S thick kappa thick t = sans("none") quad rho scripts(tack.r)_t^kappa i arrow.b.double v, rho scripts(tack.r)_t^kappa sans("delay") thick i thick e arrow.b.double v) #h(2em) frac(sans("prevAct") thick S thick kappa thick t = sans("some") thick t' quad rho scripts(tack.r)_(t')^kappa e arrow.b.double v, rho scripts(tack.r)_t^kappa sans("delay") thick i thick e arrow.b.double v) $
$ frac(sans("prevAct") thick S thick kappa' thick t = sans("none") quad rho scripts(tack.r)_t^kappa i arrow.b.double v, rho scripts(tack.r)_t^kappa sans("sync")_(kappa') thick i thick e arrow.b.double v) #h(2em) frac(sans("prevAct") thick S thick kappa' thick t = sans("some") thick t' quad rho scripts(tack.r)_(t')^(kappa') e arrow.b.double v, rho scripts(tack.r)_t^kappa sans("sync")_(kappa') thick i thick e arrow.b.double v) $
The form $sans("delay")$ reads the previous activation of the current
domain; $sans("sync")_(kappa')$ reads the previous activation of
$kappa'$ and evaluates its operand #emph[there], in $kappa'$. All other
rules carry $kappa$ unchanged.

#thm("Proposition", "13")[One temporal primitive; `delay_is_sync_own`,
`clocked_delay_iff_sync_own`, `single_domain_embedding`][$rho scripts(tack.r)_t^kappa sans("delay") thick i thick e arrow.b.double v$
iff
$rho scripts(tack.r)_t^kappa sans("sync")_kappa thick i thick e arrow.b.double v$,
and $sans("delay") thick i thick e$ is clocked in $kappa$ iff
$sans("sync")_kappa thick i thick e$ is. Under the always-active
schedule, $rho scripts(tack.r)_t^kappa e arrow.b.double v$ iff
$rho scripts(tack.r)_t e arrow.b.double v$, for every $kappa$.]

#proof[The two multi-domain rules for $sans("delay")$ read the
operand at the previous activation of the current domain $kappa$ (or the
initial value if there is none), and the two rules for
$sans("sync")_kappa$ read the operand at the previous activation of
$kappa$\; with the source domain equal to the current one the premises
coincide, so each derivation converts into the other by renaming the
rule. The clock judgment agrees for the same reason. The single-domain
semantics of §6 is the multi-domain one under the schedule that
activates one domain at every tick, since then the previous activation
of that domain is always the previous tick.]

The kernel therefore has one temporal primitive --- read a domain at its
previous activation --- and $sans("delay")$ is notation for its
diagonal; a $sans("delay")$ in a slow domain reads three global ticks
back where a $sans("delay")$ in a fast one reads one, with the same
syntax. The single-domain semantics of §6.1 is the one-domain special
case of this one rather than a replaced machine.

#thm("Theorem", "14")[Determinism and totality in every domain; `MEv.det`,
`mfundamental`, `multi_domain_total`][Multi-domain evaluation is a
partial function, for every schedule. In a causal, globally well formed
design with inputs well typed in every domain, every declared
relationship has a value in every domain at every tick, related to its
expected type.]

#proof[Determinism is the argument of Theorem 9 with the
multi-domain rules: the previous activation of a domain at a tick is a
function of the schedule, so the two temporal forms are deterministic
given determinism at the earlier tick. Totality is the argument of
Theorem 11 with the application relation of the multi-domain semantics
and one change in the temporal cases: a $sans("sync")_(kappa')$ reads
its operand at the last activation of $kappa'$ strictly before $t$, a
tick $t' < t$, so the outer strong induction on the global tick still
applies, and the initial value covers a domain that has not activated
yet. The value at the first activation of a domain is therefore the
explicit initial value of every transport into it.]

The proof reuses the logical relation of §6.3 with the application
relation
$sans("MApply") thick S thick Delta thick I thick kappa thick t$, and
the same lexicographic induction: a transport at $t$ evaluates its
operand at $t' < t$ under any rank. Causality is the #emph[same]
$sans("Causal") thick Delta$: a transport's operand is never
instantaneous, so no cross-domain cycle can be. An interpreter
$sans("mevalF")$ is proved sound (`mevalF_sound`). Tag provenance
holds across domains (`MEv.tag_provenance`): transport changes timing,
not identity, and a crossing from `Tilt@fast` to `Tilt@slow` authorizes
neither `Tilt -> MotorAngle` nor
$sans(Q)_(sans("Length")) arrow.r sans(Q)_(sans("Time"))$, by the
typing rule.

== Strictly before: preserving the authored temporal structure
<strictly-before-preserving-the-authored-temporal-structure>
#emph[Why not expose scheduler order?] A transport sees only source
activations strictly before the destination tick. The rule exists to
preserve the designer's declared temporal relationship --- "`heat` reads
the light as it stood before this tick" --- without adding a fact the
designer never authored, namely which of two simultaneously active
domains the implementation happens to run first. That is a choice with
an observable alternative, and the alternative was built.

#thm("Theorem", "15")[Same-tick visibility exposes the scheduler;
`scheduling_order_observable`][Let $sans("MEv")_lt.eq$ be the
semantics in which a transport may also see a simultaneously active
source, resolved by a priority between domains. There is a two-domain
design, a schedule and an input such that two priorities give two
different values to the same declaration at the same tick.]

#proof[Take two domains, `fast` and `other`, both active at tick
$1$ and `other` for the first time; an input $x$ in `other` with
$x thick 1 = 1$\; and
$a := sans("sync")_(upright("other")) thick 0 thick x$ in `fast`.
Under $sans("MEv")_lt.eq$ with `other` ordered first the transport sees
the simultaneous activation and $a$ evaluates to $1$\; with `fast`
ordered first there is no earlier activation of `other` and $a$
evaluates to the initial value $0$. Both are derivations of the same
judgment form, differing only in the order parameter; so the semantics
depends on the order --- which the design never authored. Under
strict-before there is no simultaneous case, and $a$ is $0$ regardless
of order.]

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
The recursor $sans("fold") thick f thick z thick l$ is a #emph[term
former], not a registered operator. The kernel has no recursion,
deliberately; a total language needs an eliminator for its inductive
data, and $sans("fold")$ is the one construct that applies a function
value in the course of evaluation. Registered operators never apply
closures. The alternative of one primitive per collection operation was
rejected because a primitive cannot apply a closure and each would need
its own evaluation rule; the alternative of bounded unrolling was
rejected because lists --- the cross-domain window --- are unbounded.

The recursor is total on related values (`fold_total`, `mfold_total`),
by an induction on the list separate from Theorem 11, which invokes it
in its $sans("fold")$ case. Every collection operation --- `map`,
`filter`, `any`, `all`, `contains`, `append`, `sum`, `zip`, and through
$sans("toList")$ the option eliminators --- is a definition over
$sans("fold")$, and each is proved to compute the mathematical function
it names through one general lemma: the recursor computes
$sans(L i s t . f o l d r) thick g$ whenever the step closure implements
$g$ on the reachable accumulators (`fold_spec`\; then `any_spec`,
`all_spec`, `map_spec`, `filter_spec`, `min_spec`, `clamp_spec`, …).
Finite quantification is a fold ---
$forall x in italic("xs") . thin P thin x$ iff `all xs P` evaluates to
true (`forall_in_list`, `exists_in_list`) --- and a finite-set literal
means membership with duplicates irrelevant (`oneOf_mem`,
`oneOf_dup_irrelevant`), so there is no `Set` type and no uniqueness
convention.

Products $tau times sigma$ with $sans("pair")$, $sans("fst")$,
$sans("snd")$ entered the kernel after the Church encoding was tried and
refuted twice. A Church pair is an arrow, and arrows are not data:
nothing of function type can be delayed or transported
(`arrow_not_delayable`), so paired #emph[state] --- a delayed reading
with its timestamp --- needs a data product. And a Church pair used as a
first-class value needs rank-2 types: in a toy System F with a rank
measure, the type of $sans("fst")$ on Church pairs has rank 2
(`church_fst_rank`), and in the prenex fragment a pair instantiated at
one result type serves only one projection
(`church_pair_prenex_one_projection`). Products are value composition
only; they are never a component interface or an output bundle (§9 shows
what a tuple-returning declaration does to the dependency graph).

Equality $sans("eq")_tau^(italic("pf"))$ is structural equality at every
data type --- booleans, numbers, $sans("none")$/$sans("some")$, pairs
and lists componentwise, concept values by tag and representation ---
with the proof $h : tau . sans("Data")$ carried #emph[in the syntax].
This is the kernel's only capability evidence: an equality on a function
type is unwritable rather than ill typed, which keeps T-Prim
unconditional. On first-order values structural equality is equality
(`Value.beq_iff`, by a mutual induction over the nested value type).

Order is deliberately not generalized. A first formulation gave `<` a
structural meaning at every data type --- booleans, options, pairs and
lists lexicographically --- and it was formally consistent. An audit
rejected it on the grounds that no such order has a design meaning:
`mode1 < mode2` would order modes by a constructor tag, `None < Some x`
is an artifact. The structural order was deleted and $sans("lt")_d$
restored to quantities only. So $sans("Data") arrow.r.double sans("Eq")$
holds (`Cap.eq_iff_data`) but $sans("Eq") ⇏ sans("Ord")$\; order on a
#emph[concept] is a surface capability --- a concept the designer
declared ordered and represented by a quantity compares as $sans("lt")_d$
on $sans("rep")$, a term the kernel already admits
(`lt_only_on_quantities`, `lt_rejected`, `min_mode_rejected`).
Enumerations follow the same rule: equality is natural, declaration
order is never silently behavioral order.

== Polymorphism by families, and the library as combinators
<polymorphism-by-families-and-the-library-as-combinators>
Five models of polymorphism were compared: a monomorphic kernel;
per-type duplication; rank-1 parametric polymorphism; System F; higher
rank. The one adopted is rank-1 #emph[as definitional families]: every
library entry is a function $sans("Ty") arrow.r sans("Expr")$ (or
$sans("Dim") arrow.r sans("Expr")$) in the metalanguage, and a scheme
is a pattern over type and dimension variables with capability
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
consulted (`generic_preserves_identity`); the same for $sans(Q)_d$
versus $sans(Q)'_d$ (`generic_preserves_dimension`). This is Reynolds's
abstraction @reynolds1983types and Wadler's free theorems
@wadler1989free at the level of syntax: a family cannot inspect what it
is instantiated at, because it is instantiated by substitution into a
closed term.

Every library entry is a #strong[combinator]: variables, literals,
lambdas, applications, registered operators, the recursor and
$sans("rep")$ --- no reference, no state, no transport, no $sans("mk")$.
For combinators four facts are proved once and combine into an inlining
statement (`lib_expansion`): typing is independent of the design and the
grant and reads $Theta$ only through write-once bindings
(`HasType.comb_irrelevant`); the value is the same in every design at
every tick under every input (`lib_eval_context_free`, from `Ev.pure`);
the term is clocked in every domain (`lib_clocked`); nothing is
constructed (`Comb.noConstruct`). This is what lets an implementation
inline an equation at each use without creating a declaration --- a
library entry as a declaration would be monomorphic and would enter the
dependency graph.

The expressiveness ceiling, stated once: total first-order-data
computation over booleans, quantities, concepts, options, lists and
pairs, with higher-order functions and one list recursor; generic
definitions instantiated at closed types; no general recursion, no type
abstraction in terms, no sums (an enumeration with a payload is encoded
as a tag paired with an optional payload, and a kernel sum would cost
one more eliminator term former exactly like $sans("fold")$), no
unbounded quantification. This is a design conclusion backed by executed
cases and the proved library; it is not a minimality theorem.

== The window: a negative design result
<the-window-a-negative-design-result>
Within one domain an occurrence is a stream of optional type (§7.4).
Across domains this fails: $sans("sync")$ is a zero-order hold, so a
slow consumer of a fast event source sees the last value only. Two fast
events at ticks 1 and 2 and one event at tick 2 are indistinguishable at
the slow activation at tick 3, and a single event at tick 1 followed by
a quiet fast tick is dropped outright
(`opt_loses_multiplicity_under_sync`). The counterexample is against
$sans("sync")$ as an #emph[event transport], not against optional
types; it says that multiplicity and order are observable across domains
and that keeping them requires buffering.

What the destination should see is the source's activations since the
destination's own previous activation --- the #emph[window],
$sans("windowTicks") thick S thick italic("src") thick italic("dst") thick t$,
the source ticks in
$\[sans("prevAct") thick S thick italic("dst") thick t\,med t\)$.
The window equals the source's accumulated log read at the current tick
minus its length at the previous destination activation
(`buffer_from_log_and_cursor`): two single-instant reads, a
$sans("sync")$ of a source-side accumulator and a $sans("delay")$ of
a cursor. With list data this is five ordinary declarations:

```
log     @src :  cons src (delay nil log)             -- source-side accumulator
logD    @dst :  sync src nil log                     -- the log, transported
seen    @dst :  length logD                          -- log length now
cursor  @dst :  delay 0 seen                         -- log length at the previous activation
window  @dst :  reverse (take (seen - cursor) logD)  -- the new entries, oldest first
```

#thm("Theorem", "16")[The window is derivable;
`buffer_window_correspondence`][For every schedule, input, destination
domain and tick, if the five declarations are realized as above and
$italic("src")$ is an input, then
$\[thin\]scripts(tack.r)_t^(italic("dst")) sans("window") arrow.b.double sans("list") thin\(sans("map") thin\(I thin italic("src")\)thin\(sans("windowTicks") thick S thick italic("src") thick italic("dst") thick t\)\)$.]

#proof[The five declarations are: a log of every source
activation (a list in the source domain, extended by one element at each
activation), a count of source activations, the count as seen at the
destination's previous activation, the difference of the two, and the
window, which takes that many elements from the reversed log. Prove
three equations by induction on the tick, each in its domain: the log at
tick $t$ is the list of the source's values at the source activations up
to $t$\; the count is its length; and the count transported into the
destination domain is the length at the destination's previous
activation. The window's definiens then evaluates, by the list
operators' equations, to the reversal of the first (length now minus
length then) elements of the reversed log --- that is, the source values
at exactly the source activations since the destination's previous
activation, in order and with multiplicity, which is the definition of
$sans("windowTicks")$. No hypothesis on the schedules is used;
at a non-activation tick the equations hold with the previous values.]

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
$sans("delay")$ and registered operators. Table 2 lists the
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
    [`previous x`], [$sans("delay") thick italic("init") thick x$],
    [`previous x` without an initial
    value], [$sans("delay") thick sans("none") thick\(sans("some") thick x\)$\;
    the absence is pushed to consumers],
    [`hold init e`], [$sans("getD") thick e thick\(sans("delay") thick italic("init") thick italic("self")\)$],
    [`count e`], [$sans("ite") thick\(sans("isSome") thick e\)thick\(1 + sans("delay") thick 0 thick italic("self")\)thick\(sans("delay") thick 0 thick italic("self")\)$],
    [`since e`], [$sans("ite") thick\(sans("isSome") thick e\)thick 0 thick\(1 + sans("delay") thick 0 thick italic("self")\)$],
    [`once e`], [$sans("delay") thick sans("false") thick italic("self") or sans("isSome") thick e$],
    [`every n`], [a modulo-$n$ counter over $sans("delay")$],
    [`rise b`], [$b and not thin sans("delay") thick sans("false") thick b$,
    as an optional Boolean],
  )]
  , kind: table
  )

#emph[Table 3. Derived temporal operators
(`Experiments/ReactiveAlternatives.lean`).]

There is no signal type in $sans("Ty")$: under this semantics a signal
type would be inhabited by exactly the terms of the underlying type and
would reject nothing. There is no event type: within one domain an input
delivers at most one value per tick by construction, so an occurrence is
a stream of optional type, and the streams of type
$sans("Option") thick tau$ are exactly the streams of multiplicity at
most one. What separates an occurrence from an optional value can only
be seen when a source ticks faster than its observer, which is the
cross-domain question of §7.3. State has no identity of its own: a cell
is a $sans("delay")$ in a declaration body, consumers refer to the
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

- $Omega : sans("OutputId") arrow.r sans("Option") thick chevron.l italic("accepts")\,italic("clock") chevron.r$
  --- each output's accepted type and domain;
- $beta : sans("DeclId") arrow.r sans("Option") thick sans("OutputId")$
  --- the drive edges, a write-once per-declaration projection of the
  same shape as $upright(K)$\;
- $sans("DriveWF") thick Omega thick upright(K) thick Delta thick beta := forall delta thin o . thick beta thick delta = sans("some") thick o arrow.r exists italic("spec") . thick Omega thick o = sans("some") thick italic("spec") and Delta in.rev delta : italic("spec") . italic("accepts") and upright(K) thick delta = sans("some") thick italic("spec") . italic("clock")$\;
- $sans("SingleDriver") thick beta := forall delta_1 thin delta_2 thin o . thick beta thick delta_1 = sans("some") thick o arrow.r beta thick delta_2 = sans("some") thick o arrow.r delta_1 = delta_2$\;
- $sans("CompleteOutputs") thick beta thick italic("req")$
  --- every required output is driven.

Nothing was added to types, typing, the domain judgment, evaluation or
the grant. The edge neither coerces nor converts nor synchronizes: the
driver's type #emph[equals] the accepted type and its domain #emph[is]
the output's. A declaration typed `Tilt` cannot drive a `MotorAngle`
output; an output that accepts a representation type needs an explicit
$sans("rep")$-typed declaration in front of it; a slow driver reading a
fast value must $sans("sync")$ it upstream. A driver of a
concept-accepting output is necessarily a value, not a function
(`driver_is_unit_domain`).

#strong[Definition.]
$sans("PhysicalOutput") thick S thick Delta thick I thick Omega thick beta thick o thick t thick v := exists delta thin italic("spec") . thick beta thick delta = sans("some") thick o and Omega thick o = sans("some") thick italic("spec") and\[thin\]scripts(tack.r)_t^(italic("spec") . italic("clock")) delta arrow.b.double v$.

#thm("Theorem", "17")[One driver, one output;
`single_driver_output_deterministic`,
`multiple_direct_drivers_rejected`][Under
$sans("SingleDriver") thick beta$,
$sans("PhysicalOutput")$ is a partial function of $o$ and
$t$. Two declarations driving one output --- each well typed, well
clocked, causal and individually well formed --- violate
$sans("SingleDriver")$ and nothing else, and there is a tick at
which the output receives two values.]

#proof[A physical output value at $o$ and $t$ is the value of
some driver $delta$ with $beta thick delta = o$, evaluated in the domain
the output specifies. Given two such values from drivers $delta_1$ and
$delta_2$, $sans("SingleDriver") thick beta$ gives
$delta_1 = delta_2$, the specification of $o$ is unique, and Theorem 14
identifies the two values. The rejection of two direct drivers is a
finite check on the design of Counterexample A: both edges pass typing,
clocks, causality and the per-edge condition, and only the global count
fails.]

#emph[Why not hide output arbitration?] The principle is #emph[many
contributors, one explicit final driver]. Contributors are dependencies:
`base + corr -> final -> motor` passes every check; priority is a
conditional in the single driver; blend, maximum and clamp are ordinary
declarations of the target type. Why arbitration must be explicit is
shown rather than argued: first-wins, last-wins and maximum over the
same value graph give three different physical outputs
(`hidden_arbitration_observable`). Binding an unbound declaration to an
undriven output is a refinement and preserves
$sans("SingleDriver")$ (`first_output_binding_is_monotone`);
binding to a driven output is invalid; retargeting, renaming or
detaching an edge invalidates an unchanged design.

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
A renaming $r$ bundles four maps --- on declaration, concept, clock and
output identities. Renaming acts on types (through the concepts $C$ they
mention), on terms, on interfaces, on declarations and pointwise on
environments; $Delta . sans("RenamedBy") thick r thick Delta'$
says $Delta'$ stores the renamed declaration of $Delta$ at the renamed
identity.

#thm("Proposition", "18")[Equivariance; `HasType.rename`,
`Satisfies.rename`, `Clocked.rename`][If
$Theta\;Delta\;Gamma scripts(tack.r)_G e : tau$ and $Theta'\,Delta'\,G'$ are the
images of $Theta\,Delta\,G$ under $r$ (agreement on the image, with no
injectivity required), then
$Theta'\;Delta'\;Gamma^r scripts(tack.r)_(G') e^r : tau^r$\; likewise for
satisfaction, and for the domain judgment under a clock environment that
agrees on the declared identities.]

#proof[By induction on the derivation. Renaming acts
homomorphically on types, terms, contexts and environments; each rule of
Figure 2 is closed under it provided the environments agree on the image
--- T-Ref because $Delta'$ holds the renamed declaration at the renamed
name, T-Rep and T-Mk because $Theta'$ binds the renamed concept to the
renamed representation and the grant is transported, and the remaining
rules syntactically. No injectivity is used: two names sent to one are
consistent with every rule. Satisfaction and the clock judgment follow
by the same induction, with equivariance of evidence as the hypothesis
for the commitment half.]

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
The judgment $sans("Realizes") thick italic("ev") thick cal(C)$ is a
predicate over the existing judgments: the template is a well-formed
design (`Design.WF`: $sans("GlobalWF")$, $Theta . sans("WF")$, well
clocked, causal, $sans("DriveWF")$,
$sans("SingleDriver")$), every required port is an unrealized
declaration of the stated interface, every provided port is declared
with it, parameters are unrealized, data-typed and clock-free.

Instance $k$ of a component maps local identity $n$ to
$sans("fresh") thick W thick k thick n = W dot.op\(k + 1\)+ n$, with
$sans("decode")$ its inverse; distinct instances never share an
identity (`inst_decl_disjoint`). The encoding is a device --- any
injective allocator would do. A #strong[binding] realizes a destination
port of one instance from a source --- a port of another instance or a
closed constant --- with an optional transport: none for a direct
reference in the same or an agnostic domain,
$sans("some") thick italic("init")$ for $sans("sync")$ from the
source's domain. A #strong[system] is a width, a list of instances, a
list of bindings, the shared concept environment and the external
outputs. #strong[Flattening] is the union of the renamed instances
followed by the bindings applied as §4 realization steps: the
destination port is realized as $italic("src")$ or
$sans("sync")_kappa thick italic("init") thick\(italic("src")\)$. The
result is a design, consumed by every existing judgment unchanged.

#thm("Theorem", "19")[Composition adds no machinery; `binding_satisfies`,
`flatten_WF`, `flatten_causal`, `flatten_wellClocked`,
`flatten_singleDriver`, `open_port_stays_open`][Under
$sans("ComposeWF")$ --- every instance realizes its interface;
every binding is well formed (types agree; a direct binding's source is
in the destination's domain or agnostic; a transported binding's source
has a domain); external outputs are driven by at most one instance ---
and with evidence that is monotone, equivariant and port-sound (a
discharged commitment survives when a port copy is realized by a
reference to a declaration of the same interface), the flattening is
globally well formed, well clocked, single-driver, causal when the
inter-instance graph is acyclic, and its open ports remain open.]

#proof[Flattening first takes the disjoint union of the
instances, each template renamed by a fresh injective renaming, and then
realizes every bound port with a binding body --- a constant name, a
transport of one, or a closed constant. Establish an invariant along the
sequence of bindings: the current environment refines the union, is
globally well formed, and holds every port already bound at its binding
body. The base case is the union, globally well formed by Proposition 18
applied to each template. For a step, the binding body satisfies the
destination port's interface in any environment refining the union
(`binding_satisfies`): a port binding reads a provided port whose
interface refines the required one, with the transport's initial value
typed under the empty grant; a constant binding is closed and typed at
the port's type; the commitments transfer by port-soundness of the
evidence. Realizing an unrealized port with a satisfying body is a
$sans("realize")$ step, so Theorem 4 preserves global
well-formedness and the invariant. Causality of the result: order
instances by the acyclic inter-instance graph and, within an instance,
by the template's own rank; a direct binding creates an instantaneous
edge only from a destination to a source in a lower instance, and a
transport creates none. Clocks: bindings connect ports of equal domain
or through a transport whose source domain is the provided port's.
Single driver: each instance's drive edges are renamed injectively and
external sinks have at most one driving instance. An unbound port keeps
no definiens, since only bindings realize ports.]

#thm("Theorem", "20")[Modular semantics, restricted; `eval_flat_to_inst`,
`eval_inst_to_flat`, `modular_iff_flat`][For wiring designs with
closure-free inputs and direct bindings, in one domain, the value of a
declaration in an instance evaluated alone with a consistent modular
input equals its value in the flattened system.]

#proof[In the modular semantics an instance evaluates its own
declarations with an input that supplies, for each of its bound ports,
the value the binding delivers; #emph[consistent] means that input
equals the flattened value of the port's source. Forward direction, by
induction on the flattened derivation over wiring terms (constants,
applications of primitives, no lambdas): a reference the instance owns
evaluates identically, since its definiens is the same renamed body; a
reference to a bound port is, in the flattened design, a reference to
the source, and its value is by consistency the modular input for that
port. The backward direction is the same induction from the modular
side, using totality of the flattened semantics to obtain the source's
value and consistency to identify it. Closure-freeness of inputs keeps
every value first-order, so no environment of a closure can differ
between the two sides; direct bindings keep every reference within one
tick. The equivalence for a declaration $delta$ owned by instance $k$ is
both directions at $e = delta$.]

The restriction is exact and recorded: transported bindings under
$sans("MEv")$ need a domain-indexed input for the transported port, and
higher-order bodies are not covered --- the same obstacle in both
directions. Substitutability follows the usual contravariance: $B$ may
replace $A$ when every port $A$ provides, $B$ provides at the same type
and clock, and every port $B$ requires, $A$ required; replacing an
instance by a refining component preserves $sans("ComposeWF")$
(`substitute_composeWF`).

The counterexamples that fixed the design
(`Experiments/BehaviorAlternatives.lean`): a name-based identity
collides on double instantiation; a shared clock captured inside a
template cannot be re-bound; a binding across domains without transport
is rejected by $sans("Clocked")$\; two instances driving one
external output violate $sans("SingleDriver")$.

== Groups are the identity, and extraction is a system
<groups-are-the-identity-and-extraction-is-a-system>
A #emph[group] --- a designer's selection of several declarations --- is
authoring metadata: a group identity and a member list beside the
design. Every group operation acts on the list and leaves the design
untouched, so every kernel judgment of the design is the #emph[same
proposition] before and after, each proved by reflexivity
(`group_is_identity_on_design`). A group's boundary is a projection over
a finite enumeration: the non-members some member depends on
($sans("crossIn")$), the members some non-member depends on
($sans("crossOut")$); the aggregate socket a collapsed group shows
is these lists, none of which is a declaration, and
$a in sans("crossIn")$ says #emph[some] member depends on $a$ and
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

Three proof-engineering choices carried the metatheory. The relations
$sans("Ev")$ and $sans("MEv")$ are ordinary inductive relations with no
mutual recursion, because the recursor's rule unrolls through the
environment (§6.1); every induction on evaluation extends by one case
when a construct is added, and the transport primitive and the recursor
entered this way with every earlier theorem re-established without a
change of statement. The logical relation is parameterized by an
application relation so that the single- and multi-domain semantics
share it, and is independent of that parameter at data types
(`Red_data`), which is the fact that lets a value cross a tick. Every
rejected alternative is a theorem whose content is a rejection, stated
on a concrete design and discharged by `decide` or by running the
interpreters $sans("evalF")$/$sans("mevalF")$ --- proved sound for
the relations --- inside the checker; there is no test suite beside the
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
@leroy1994manifest@harper1994modules. The calculus does not claim that
such systems cannot express an unrealized relationship. The difference
is one of organization: here an unrealized declaration is an ordinary
inhabitant of the #emph[design environment] rather than a separate
compilation unit; its clients are typed against it in the same
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
$lambda_(upright("BDL"))$ the authored unit is a declared relationship,
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
$lambda_(upright("BDL"))$ adds is a small mechanized calculus for the
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
design in $lambda_(upright("BDL"))$ may contain decisions at different
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
  `A := λx. A x` is rejected by $sans("Causal")$ although `declRef A`
  evaluates to a closure; Proposition 10 covers strict cycles only.
- #emph[Modular semantics is proved for a fragment.] Theorem 20 holds
  for single-domain wiring designs with direct or constant bindings;
  transported bindings under $sans("MEv")$ and higher-order realizations
  are open.
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
The calculus is not interesting because it makes every implementation
detail first-class. It is interesting because a typed semantic
relationship can be declared, connected to concepts, depended upon by
other parts of a product, placed in time and bound to a physical output
while its computation is still undecided --- and can then acquire that
computation without disturbing anything built on it. The intermediate
state is a design state, not a broken program state, and the calculus
gives it a semantics in which it is typable, referenceable, composable,
refinable, stable for clients and eventually realizable.

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
