#heading(level: 1, numbering: none)[Abstract]
<abstract>
Interactive physical products are designed by people who state
#emph[relationships] before they can define them: a lamp's brightness
follows its tilt; the room's temperature is read once a second while the
tilt is read fifty times a second; the light is the product's only
physical effect. We present $lambda_(upright(B D L))$, the core calculus
of the Behavior Design Language, in which such a design is a finite
environment of #emph[persistent declarations] --- each a stable
identity, a frozen expected type with a growable set of public
commitments, and an optional realization --- over a simply typed term
language extended with nominal #emph[concept] types bound write-once to
data representations, a #emph[construction grant] derived from the
declaration's own signature, physical #emph[dimensions] carried by
operator types, ordinary data (options, lists, products) with one list
recursor, and exactly one temporal primitive: read a #emph[clock domain]
at its last activation strictly before now. We give the calculus a
tick-indexed big-step semantics and prove it deterministic and total on
#emph[causal] designs by a tick-indexed logical relation with a
lexicographic induction on (tick, instantaneous rank, derivation); the
single-domain semantics is the diagonal of the multi-domain one, memory
is transport at the own domain, and no scheduler order is observable. We
prove that refining a declaration --- adding a commitment, supplying a
body, strengthening a realized interface with re-verification ---
preserves every client's typing unconditionally and every client's
discharged commitment provided the validation layer's evidence is
monotone in the environment, and we show by a mechanized counterexample
that the monotonicity condition is necessary. Semantic identity has no
runtime residue (erasure is sound), cannot be manufactured except where
a signature announces it (construction is granted, and provenance is
preserved through memory and transport), and is orthogonal to dimension.
Physical effect passes through explicit drive edges with a single driver
per output, which makes the physical output a function of the tick.
Behavior components are derived from renaming and realization alone, and
flattening a composition yields an ordinary design checked by the
unchanged judgments. Every definition and theorem is mechanized in Lean
4 with no `sorry` and no classical choice; every rejected alternative is
a mechanized counterexample; every trace is computed by an interpreter
proved sound for the relation.

#strong[Keywords:] reactive semantics, clock domains, nominal types,
refinement, logical relations, mechanized metatheory, Lean 4,
synchronous languages, units of measure

= Introduction
<introduction>
A behavior designer working on an interactive physical product does
something that a programmer's language makes awkward: they #emph[declare
a relationship they cannot yet define]. "Brightness follows tilt" is a
complete design statement long before anyone knows the formula; it has a
type --- the concept `Tilt` to the concept `Brightness` --- and other
parts of the design depend on it at that type. Later the relationship
acquires a formula, a promise ("monotone"), a timing domain, a physical
output; none of these later steps should disturb what already depended
on it. The formula must be unable to produce anything but a
`Brightness`, even though a brightness and an opacity are both
represented by a dimensionless number and a tilt and a motor angle are
both angles. Values must be remembered across time with an explicit
first value, and read across timing domains without making the scheduler
visible. Physical effect must happen exactly once per output,
explicitly.

This paper presents the core calculus that gives these requirements a
semantics and proves that they compose: $lambda_(upright(B D L))$, the
kernel of the Behavior Design Language (BDL). The calculus is
deliberately small. Its term language is a simply typed λ-calculus with
registered first-order operators; what makes it a #emph[design] calculus
is not its terms but the environments they are typed and evaluated
against, and the two disciplines those environments impose --- a
#emph[refinement order] on declarations, and a #emph[grant] on the
construction of nominal values.

== What the calculus adds to the simply typed λ-calculus
<what-the-calculus-adds-to-the-simply-typed-λ-calculus>
- #strong[Persistent declarations] (§4). A design is an environment
  $Delta$ of declarations
  $chevron.l italic(i d)\,chevron.l tau\,C chevron.r\,italic(r e a l i z a t i o n) chevron.r$
  with a stable identity, a frozen expected type, a growable list of
  public commitments, and an optional body. Terms refer to declarations
  by identity, and the typing judgment reads $Delta$ through exactly one
  projection, the #emph[type view]. A refinement order on declarations
  and environments captures the operations that a client may survive;
  everything else is an #emph[edit] about which nothing is promised. We
  prove that refinement preserves every client's typing with no
  hypothesis, and every client's discharged commitment under a
  Kripke-style monotonicity condition on the validation layer's evidence
  --- a condition we show necessary (Theorems 4--5, Proposition 6).
- #strong[Nominal concepts with granted construction] (§5). A concept is
  a nominal type $upright("sem") thick s$\; a concept environment
  $Theta$ binds it, write-once, to a representation type that is data
  and mentions no concept. Observing a representation ($upright("rep")$)
  is always permitted; constructing a value ($upright("mk") thick s$)
  requires a grant, and a declaration's body is granted exactly the
  concepts in result position of its own signature. Under that
  discipline a hidden crossing between concepts is untypable, erasure to
  the representation is sound, and no tag is created by evaluation,
  memory, or transport (Theorems 8, 9 and 14).
- #strong[Dimensions in operator types] (§5.3). A physical quantity has
  type $upright("q") thick d$ for an exponent vector $d$\; the algebra
  lives entirely in the registered operators' types and no typing rule
  mentions it. The dimensionless baseline is the erasure of this typing,
  exactly as the numeric baseline is the erasure of nominal typing.
- #strong[One temporal primitive] (§6--7).
  $upright("sync") thick c thick italic(i n i t) thick e$ reads $e$ in
  clock domain $c$ at $c$'s last activation strictly before the current
  tick, or $italic(i n i t)$ if there is none; $upright("delay")$ is
  $upright("sync")$ at the own domain. The semantics is tick-indexed
  big-step evaluation against an input stream and a schedule. It is
  deterministic unconditionally and total on #emph[causal] designs ---
  those whose instantaneous dependency graph is acyclic --- by a logical
  relation indexed by the tick with a lexicographic induction on tick,
  rank and derivation (Theorems 10--13, 18--19). The delayed type must
  be data and $upright("delay")$ may appear only at top level; both
  restrictions are forced by the totality proof rather than chosen.
  Clock domains are nominal identities, not rates; the #emph[strictly
  before] rule makes the semantics independent of any order between
  simultaneously active domains, and the alternative is mechanically
  shown to expose the scheduler (Theorem 20).
- #strong[Data with one recursor] (§8). Options, lists and products are
  ordinary data; $upright("fold")$ is the one term former that applies a
  function value during evaluation. Its evaluation rule unrolls
  syntactically through the environment so that the evaluation relation
  remains an ordinary inductive relation. Polymorphism is rank-1 by
  definitional families instantiated by one-way matching against closed
  types; no type variable enters the kernel. The lossless cross-domain
  window buffer --- the one construction a designer would expect to be
  primitive --- is five declarations over $upright("delay")$,
  $upright("sync")$ and list operators, with a correctness theorem for
  every schedule (Theorem 21).
- #strong[Explicit outputs] (§9). A declaration computes a value;
  hardware moves only through a drive edge to a nominally identified
  output with a single driver. With one driver the physical output is a
  partial function of the tick; with a hidden arbitration policy three
  different outputs arise from one design (Theorem 23).
- #strong[Composition by renaming] (§10). Behavior components, fresh
  instantiation, bindings and flattening are derived from realization
  steps and an equivariance theorem for every judgment; the flattened
  system is an ordinary design accepted by the unchanged checkers
  (Theorems 24--26).

== Mechanization and claims
<mechanization-and-claims>
Every definition, theorem and counterexample in this paper is a Lean 4
declaration in the development `KCN-judu/BDL_FV` @moura2021lean. The
development builds with no `sorry`\; the axioms used are propositional
extensionality and quotient soundness (the latter only through function
extensionality), and classical choice is absent. Negative results are
theorems whose content is a rejection; every trace is computed by an
interpreter proved sound for the evaluation relation, inside the proof
checker. The paper cites the Lean name of each result at the point it is
stated, and Appendix A indexes them by section.

Two conventions bound the claims. #emph[Minimal] always means minimal
among the alternatives that were formalized and refuted, never a
minimality theorem. Where a theorem is proved for a fragment --- the
modular-semantics result holds for single-domain wiring designs with
direct bindings --- the restriction is part of the statement.

== What this paper is not
<what-this-paper-is-not>
It is not a paper about the surface language, the authoring environment
or the production toolchain that implements the calculus; those are
described in the BDL monograph, of which this paper is the formal core.
It is not a paper about hardware validation or deployment, which live
above the kernel as decidable relations that never enter typing or
evaluation. And it is not a new type-theoretic mechanism: each
ingredient is a known shape --- the interface/implementation separation
of module signatures @leroy1994manifest@harper1994modules, an abstract
type with a private constructor @mitchell1988abstract, a Kripke-style
stability condition, the `pre` of Lustre @halbwachs1991lustre confined
to nodes, a step-indexed logical relation
@appel2001indexed@ahmed2006stepindexed. What is specific is where the
ingredients come from --- the grant from the signature the designer
already wrote, the domain from an authored identity rather than an
inferred clock, the buffer from two reads of a log --- and that their
combination has been proved to compose.

= Overview: a lamp in $lambda_(upright(B D L))$
<overview-a-lamp-in-lambda_mathrmbdl>
We fix a small product to make the calculus concrete: a lamp whose
brightness follows its tilt, dims smoothly, and warms its base according
to the room temperature. The design begins with concepts and signatures
and nothing else.

#strong[Concepts.] `Tilt`, `Brightness`, `RoomTemp` and `MotorAngle` are
semantic identities $s in upright("SemanticId")$. Each is a nominal type
$upright("sem") thick s$. The concept environment $Theta$ binds `Tilt`
and `MotorAngle` to $upright("q") thick upright("Angle")$ and
`Brightness` to $upright("q") thick 0$\; the two angles remain distinct
types.

#strong[Declarations before definitions.] The relationship
`dimByTilt : Tilt -> Brightness` is a declaration
$chevron.l d_1\,chevron.l upright("sem") thick upright("Tilt") arrow.r upright("sem") thick upright("Brightness")\,\[thin\]chevron.r\,upright("none") chevron.r$:
an identity, an interface, and no body. `tilt : Tilt` is a declaration
with no body that will never receive one --- an #emph[input], whose
value the environment supplies at every tick. `light : Brightness` is
realized as
$upright("app") thick\(upright("declRef") thick d_1\)thick\(upright("declRef") thick italic(t i l t)\)$
and is well typed now, against $d_1$'s interface, whether or not $d_1$
ever acquires a formula.

#strong[Refinement.] Giving `dimByTilt` the body
$lambda x : upright("sem") thick upright("Tilt") . thick upright("mk") thick upright("Brightness") thick\(upright("clamp") thick\(upright("rep") thick x thin\/thin 90^compose\)thick 0 thick 1\)$
--- where `90 deg` is surface notation for a dimensioned literal
$upright("lit")_(upright("Angle"))$ and `clamp` for a library term over
$upright("lt")$ and $upright("ite")$ --- is a refinement step. The body
is typed under the grant ${ upright("Brightness") }$ --- the concepts in
result position of `Tilt -> Brightness` --- so
$upright("mk") thick upright("Brightness")$ is permitted and
$upright("mk") thick upright("MotorAngle")$ would not be. `light`'s
typing is untouched (Theorem 4). Adding the commitment `monotone` to
`dimByTilt` later is a refinement; changing its expected type is an
edit.

#strong[Memory.] A smooth dimmer remembers its previous output:
`smooth : Brightness` realized as a mix of `light` and
$upright("delay") thick italic(i n i t) thick\(upright("declRef") thick italic(s m o o t h)\)$.
The self-reference is a structural cycle every path of which passes
through a delayed operand; the design is #emph[causal] and has a value
at every tick (Theorem 13). The initial value is part of the syntax:
without it the first tick is undefined or nondeterministic, and both
failure modes are mechanized.

#strong[Clock domains.] `tilt` and `light` live in a domain `fast`\;
`roomTemp` and `heat` in a domain `slow`. Domains are nominal: a clone
of `fast` with the same schedule is a different domain, and a direct
wire between them is rejected by the domain judgment. `heat` may read
the tilt only through
$upright("sync") thick upright("fast") thick italic(i n i t) thick\(upright("declRef") thick italic(l i g h t)\)$,
whose value is `light` at the last `fast` activation strictly before the
current `slow` tick. Typing is blind to domains and unchanged.

#strong[Output.] The physical light is an output identity $o$ accepting
$upright("sem") thick upright("Brightness")$ in domain `fast`\; the
drive edge $beta thick italic(s m o o t h) = upright("some") thick o$ is
well formed because the types are equal and the domains agree, and it is
the only driver of $o$. Nothing else in the design has a physical
effect.

Sections 3--10 give each of these steps its rules and theorems.

= The calculus
<the-calculus>
== Syntax
<syntax>
Figure 1 gives the syntax. Types are those of a simply typed calculus
with booleans, counts and arrows, extended by nominal concept types
$upright("sem") thick s$ over an identity $s$, physical quantities
$upright("q") thick d$ over a dimension $d$, and the data formers
$upright("opt")$, $upright("list")$ and $times$. A dimension is an
exponent vector over a fixed finite set of base dimensions (length,
time, angle, mass, temperature in the development); dimensions form an
abelian group under pointwise addition, which is the only structure the
calculus uses.

$  & s in upright("SemanticId") #h(2em) d in upright("Dim") #h(2em) c in upright("ClockId") #h(2em) delta in upright("DeclId") #h(2em) o in upright("OutputId")\
tau\,sigma thick upright("::=") thick & upright("bool") divides upright("nat") divides tau arrow.r sigma divides upright("sem") thick s divides upright("q") thick d divides upright("opt") thick tau divides upright("list") thick tau divides tau times sigma\
e thick upright("::=") thick & x divides upright("true") divides upright("false") divides n divides lambda x : tau . thin e divides e thick e divides upright("declRef") thick delta divides upright("rep") thick e divides upright("mk") thick s thick e divides p\
divides thick & upright("delay") thick e thick e divides upright("sync") thick c thick e thick e divides upright("fold") thick e thick e thick e\
p thick upright("::=") thick & upright("lit")_d thin n divides upright("add")_d divides upright("sub")_d divides upright("mul")_(d_1 d_2) divides upright("div")_(d_1 d_2) divides upright("lt")_d divides upright("eq")_tau^h divides not divides and divides or divides upright("ite")_tau\
divides thick & upright("none")_tau divides upright("some")_tau divides upright("isSome")_tau divides upright("getD")_tau divides upright("nil")_tau divides upright("cons")_tau divides upright("length")_tau divides upright("take")_tau divides upright("drop")_tau divides upright("reverse")_tau divides upright("head")_tau\
divides thick & upright("toList")_tau divides upright("pair")_(tau sigma) divides upright("fst")_(tau sigma) divides upright("snd")_(tau sigma) $

#emph[Figure 1. Syntax of $lambda_(upright(B D L))$. Variables are de
Bruijn indices in the development; the paper writes names. $h$ in
$upright("eq")_tau^h$ is a proof that $tau$ is a data type.]

Terms are those of the λ-calculus plus five design-specific forms.
$upright("declRef") thick delta$ refers to a declaration by identity;
nothing about the declaration's interface or body is in the syntax.
$upright("rep") thick e$ observes the representation of a concept value
and $upright("mk") thick s thick e$ constructs one.
$upright("delay") thick i thick e$ is the value of $e$ at the previous
activation of the current domain, $i$ before any;
$upright("sync") thick c thick i thick e$ is the value of $e$ in domain
$c$ at $c$'s last activation strictly before now, $i$ if none.
$upright("fold") thick f thick z thick l$ is the list recursor,
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
#emph[which environment a judgment may see] --- is what the metatheory
rests on, and each theorem's hypotheses name the environments it depends
on.

- A #strong[declaration] is a triple
  $ upright("DesignDecl") = chevron.l thin italic(i d) : upright("DeclId")\,med italic(i n t e r f a c e) : chevron.l italic(e x p e c t e d T y p e) : upright("Ty")\,med italic(c o m m i t m e n t s) : upright("PropertyId")^(*) chevron.r\,med italic(r e a l i z a t i o n) : upright("Option") thick upright("Expr") thin chevron.r . $
  A #strong[design] is a declaration environment
  $Delta : upright("DeclId") arrow.r upright("Option") thick upright("DesignDecl")$.
  Its #emph[type view]
  $Delta^(upright(t y))\(delta\)=\(Delta thick delta\). upright("map")\(dot.op . italic(i n t e r f a c e) . italic(e x p e c t e d T y p e)\)$
  is all that typing sees; its #emph[realization view]
  $Delta^(upright(r e a l))\(delta\)=\(Delta thick delta\). upright("bind")\(dot.op . italic(r e a l i z a t i o n)\)$
  is all that evaluation sees. An #strong[unresolved] declaration is one
  whose realization is $upright("none")$\; nothing else distinguishes
  it.
- A #strong[concept environment]
  $Theta : upright("SemanticId") arrow.r upright("Option") thick upright("Ty")$
  binds each concept to a representation. It is well formed,
  $Theta . upright("WF")$, when every bound representation is
  concept-free and data:
  $Theta thick s = upright("some") thick R arrow.r.double R . upright("SemFree") and R . upright("Data")$.
- A #strong[grant] $G : upright("SemanticId") arrow.r upright("Prop")$
  says which concepts a term may construct. $upright("Grant.none")$
  permits nothing; $upright("Grant.of") thick tau$ permits the concepts
  in result position of $tau$,
  $upright("grant")\(upright("sem") thick s\)=\[s\]$,
  $upright("grant")\(tau arrow.r sigma\)= upright("grant")\(sigma\)$,
  $upright("grant")\(\_\)=\[thin\]$.
- A #strong[clock environment]
  $upright(K) : upright("DeclId") arrow.r upright("Option") thick upright("ClockId")$
  assigns each declaration a domain; $upright("none")$ is a
  domain-agnostic pure mapping. A #strong[schedule]
  $S : upright("ClockId") arrow.r bb(N) arrow.r upright("Bool")$ says at
  which global ticks each domain activates. An #strong[input]
  $I : upright("DeclId") arrow.r bb(N) arrow.r upright("Value")$
  supplies a value for every unresolved declaration at every tick.
- An #strong[output environment]
  $Omega : upright("OutputId") arrow.r upright("Option") thick chevron.l italic(a c c e p t s) : upright("Ty")\,italic(c l o c k) : upright("ClockId") chevron.r$
  and the #strong[drive edges]
  $beta : upright("DeclId") arrow.r upright("Option") thick upright("OutputId")$
  are introduced in §9.

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
$Theta thick s = upright("some") thick R$\; T-Mk additionally requires
the grant. T-Prim assigns each registered operator its type; the
dimension algebra is entirely in that table (Figure 3), so an
application of $upright("mul")_(d_1 d_2)$ is checked by T-App like any
other. T-Delay and T-Sync require the type to be data and the context to
be empty; T-Fold types the recursor.

$ frac(Gamma\(x\)= tau, Theta\;Delta\;G\;Gamma tack.r x : tau) med upright("(T-Var)") #h(2em) frac(, Theta\;Delta\;G\;Gamma tack.r b : upright("bool")) med upright("(T-Bool)") #h(2em) frac(, Theta\;Delta\;G\;Gamma tack.r n : upright("nat")) med upright("(T-Nat)") $

$ frac(Theta\;Delta\;G\;Gamma\,x : tau tack.r e : sigma, Theta\;Delta\;G\;Gamma tack.r lambda x : tau . thin e : tau arrow.r sigma) med upright("(T-Lam)") #h(2em) frac(Theta\;Delta\;G\;Gamma tack.r f : tau arrow.r sigma quad Theta\;Delta\;G\;Gamma tack.r a : tau, Theta\;Delta\;G\;Gamma tack.r f thick a : sigma) med upright("(T-App)") $

$ frac(Delta^(upright(t y))\(delta\)= upright("some") thick tau, Theta\;Delta\;G\;Gamma tack.r upright("declRef") thick delta : tau) med upright("(T-Ref)") #h(2em) frac(, Theta\;Delta\;G\;Gamma tack.r p : upright("ty")\(p\)) med upright("(T-Prim)") $

$ frac(Theta thick s = upright("some") thick R quad Theta\;Delta\;G\;Gamma tack.r e : upright("sem") thick s, Theta\;Delta\;G\;Gamma tack.r upright("rep") thick e : R) med upright("(T-Rep)") #h(2em) frac(G thick s quad Theta thick s = upright("some") thick R quad Theta\;Delta\;G\;Gamma tack.r e : R, Theta\;Delta\;G\;Gamma tack.r upright("mk") thick s thick e : upright("sem") thick s) med upright("(T-Mk)") $

$ frac(tau . upright("Data") quad Theta\;Delta\;G\;\[thin\]tack.r i : tau quad Theta\;Delta\;G\;\[thin\]tack.r e : tau, Theta\;Delta\;G\;\[thin\]tack.r upright("delay") thick i thick e : tau) med upright("(T-Delay)") $

$ frac(tau . upright("Data") quad Theta\;Delta\;G\;\[thin\]tack.r i : tau quad Theta\;Delta\;G\;\[thin\]tack.r e : tau, Theta\;Delta\;G\;\[thin\]tack.r upright("sync") thick c thick i thick e : tau) med upright("(T-Sync)") $

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
    [$upright("lit")_d thin n$], [$upright("q") thick d$], [$upright("eq")_tau^h$], [$tau arrow.r tau arrow.r upright("bool")$],
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
The client-stability theorem of §4 is a one-line consequence, and its
necessity is a one-line counterexample.

#emph[The construction boundary.] Client code is typed under
$upright("Grant.none")$\; a declaration's realization is typed under
$upright("Grant.of")$ its own expected type (§4.1). A value of
$upright("sem") thick s$ is therefore constructed only inside a
declaration whose signature announces $upright("sem") thick s$. This is
the whole of the semantic-isolation mechanism, and §5 shows what each
weaker alternative admits.

#emph[The temporal boundary.] $upright("delay")$ and $upright("sync")$
are typed only in the empty context and only at data types. Both
restrictions were forced by the totality proof of §6, not chosen: a
delayed closure would have to be transported across ticks, and a delay
under a binder would re-evaluate its operand at the previous tick in an
environment created at the current one. Temporal state therefore belongs
to declarations, and mappings are pointwise --- the arrangement of `pre`
in Lustre, where it lives in nodes rather than in functions
@halbwachs1991lustre.

== Inference, uniqueness and monotonicity
<inference-uniqueness-and-monotonicity>
Inference is syntax-directed. A function
$upright("infer") thick Theta thick Delta thick G thick Gamma thick e : upright("Option") thick upright("Ty")$
follows the rules of Figure 2 and needs only decidability of $G$, of
type equality and of $tau . upright("Data")$.

#strong[Theorem 1 (Inference; `infer_sound`, `infer_complete`,
`HasType.unique`).]
$upright("infer") thick Theta thick Delta thick G thick Gamma thick e = upright("some") thick tau$
iff $Theta\;Delta\;G\;Gamma tack.r e : tau$\; hence typing is decidable
and every term has at most one type.

Uniqueness matters beyond decidability: it is why the surface language's
polymorphism can be #emph[matching] rather than unification (§8.4), and
why a nominal mismatch is reported as "Brightness and Opacity are
different concepts" and never as a unification residue.

#strong[Theorem 2 (Monotonicity; `HasType.mono_env`,
`HasType.mono_concept`, `HasType.mono_grant`).] Typing is monotone in
each of its three environments: if
$Theta\;Delta\;G\;Gamma tack.r e : tau$, then the same holds in any
$Delta'$ with $upright("EnvRefines") thick Delta thick Delta'$ (§4.2),
any $Theta'$ that binds at least what $Theta$ binds, and any
$G' supset.eq G$.

Weakening holds for the delay-free fragment by appending to the context
(`HasType.weaken_append`); a stateful term cannot be moved under a
binder at all, so no stronger weakening is needed.

= Declarations, interfaces and refinement
<declarations-interfaces-and-refinement>
The foundational object is the declaration, and the foundational
question is which changes to a declaration its clients survive. This
section fixes the answer: a #emph[refinement order], the three steps
that generate it, and two preservation theorems with deliberately
different hypotheses.

== Interfaces, evidence and satisfaction
<interfaces-evidence-and-satisfaction>
An interface $S = chevron.l tau\,C chevron.r$ is an expected type and a
list of commitments --- atomic labels such as `total`, `monotone`,
`bounded` that a client may rely on. Interfaces are ordered by monotone
refinement:
$ S subset.eq.sq S' thick := thick S . tau = S' . tau thick and thick S . C subset.eq S' . C\, $
a decidable preorder, frozen on the type and growing on commitments
(`InterfaceRefines`). Nothing else is an interface refinement.

What discharges a commitment is not the kernel's business; it is the
validation layer's. The kernel abstracts it as an #strong[evidence]
relation
$italic(e v) : upright("DeclEnv") arrow.r upright("Expr") arrow.r upright("PropertyId") arrow.r upright("Prop")$.
Evidence takes the environment because compositional discharge needs it
--- "$A$ is monotone because $B$ is committed to be monotone" consults
$B$'s interface. A body $e$ #strong[satisfies] $S$ in
$Theta\,Delta\,Gamma$ when it has the expected type under the grant of
that type and every commitment is discharged:
$ upright("Satisfies") thick italic(e v) thick Theta thick Delta thick Gamma thick e thick S thick := thick Theta\;Delta\;upright("Grant.of")\(S . tau\)\;Gamma tack.r e : S . tau thick and thick forall p in S . C . thick italic(e v) thick Delta thick e thick p . $
A declaration is well formed when its body, if any, satisfies its
interface; a design is #strong[globally well formed],
$upright("GlobalWF") thick italic(e v) thick Theta thick Delta$, when
every stored declaration sits under its own identity and is well formed
in $Delta$ at top level. An unresolved declaration is always well
formed.

The refinement order is complete for abstract evidence:
$S subset.eq.sq S'$ iff every realization of $S'$ in every environment
under every evidence relation realizes $S$
(`InterfaceRefines_iff_semantic`). The proof of the converse
instantiates evidence at "the property is in $S'$'s list" and the body
at a reference to a single declaration.

== The refinement order and the lifecycle
<the-refinement-order-and-the-lifecycle>
A declaration takes a refinement step in one of three ways
(`DeclRefines`), each preserving the identity by construction and each
checked against the current environment $Delta$:
$ frac(S subset.eq.sq S', chevron.l delta\,S\,upright("none") chevron.r arrow.r.squiggly chevron.l delta\,S'\,upright("none") chevron.r) #h(2em) frac(upright("Satisfies") thick italic(e v) thick Theta thick Delta thick Gamma thick e thick S, chevron.l delta\,S\,upright("none") chevron.r arrow.r.squiggly chevron.l delta\,S\,upright("some") thick e chevron.r) #h(2em) frac(S subset.eq.sq S' quad upright("Satisfies") thick italic(e v) thick Theta thick Delta thick Gamma thick e thick S', chevron.l delta\,S\,upright("some") thick e chevron.r arrow.r.squiggly chevron.l delta\,S'\,upright("some") thick e chevron.r) $
An unresolved declaration may have its interface refined; an unresolved
declaration may be realized by a satisfying body; a realized declaration
may have its interface strengthened provided the body is
#emph[re-verified] against the new interface. Strengthening without
re-verification breaks well-formedness, and the counterexample is
mechanized (`naive_breaks_wellformedness`).

Separately from the steps there is a purely structural order with no
satisfaction condition: $upright("DeclLeq") thick h thick h'$ requires
the same identity, $h . S subset.eq.sq h' . S$, and a write-once
realization
($h . italic(r e a l i z a t i o n) = upright("some") thick e arrow.r.double h' . italic(r e a l i z a t i o n) = upright("some") thick e$);
$upright("EnvRefines") thick Delta thick Delta'$ lifts it pointwise and
permits new declarations. Storing a refined declaration back under its
identity is an environment refinement ---
$Delta thick h . italic(i d) = upright("some") thick h and upright("DeclLeq") thick h thick h' arrow.r.double upright("EnvRefines") thick Delta thick\(Delta\[h'\]\)$
(`EnvRefines_update`) --- and this is the one place identity does any
work: it makes the update land on the slot every reference resolves to,
which is what a name does in any environment semantics.

#strong[Theorem 3 (The lifecycle is the structural order;
`DeclRefinesStar_iff`).] The reflexive--transitive closure of the three
steps, all side conditions checked in $Delta$, relates $h$ to $h'$ iff
$upright("DeclLeq") thick h thick h'$ and $h'$ is well formed in
$Delta$.

== Client stability
<client-stability>
Can a declaration be refined or realized without editing its clients,
and without invalidating what was established about them? The answer has
two halves.

#strong[Theorem 4 (Client stability, typing;
`local_refinement_preserves_global_typing`).] If
$Delta thick B . italic(i d) = upright("some") thick B$ and
$upright("DeclLeq") thick B thick B'$, then every judgment
$Theta\;Delta\;G\;Gamma tack.r e : tau$ holds in $Delta\[B'\]$.

The proof is one line: typing reads $Delta$ through the type view, and
the type view is invariant under $upright("DeclLeq")$. The theorem
should be read as such --- its content is that letting clients see
interfaces and never bodies is #emph[sufficient] for client stability.
It is also necessary: change $B$'s expected type while keeping its
identity and every client breaks; that is why the type is frozen in
$subset.eq.sq$.

The commitment half needs more.

#strong[Definition (Monotone evidence).] $italic(e v)$ is
#strong[monotone] when
$upright("EnvRefines") thick Delta_1 thick Delta_2 and italic(e v) thick Delta_1 thick e thick p arrow.r.double italic(e v) thick Delta_2 thick e thick p$.
Evidence that ignores the environment is monotone; evidence that
consults only the #emph[presence] of commitments and realizations is
monotone; evidence that consults their #emph[absence] is not.

#strong[Theorem 5 (Client stability, commitments;
`local_refinement_preserves_global_wf`,
`local_lifecycle_preserves_global_wf`).] If $italic(e v)$ is monotone,
$upright("GlobalWF") thick italic(e v) thick Theta thick Delta$,
$Delta thick B . italic(i d) = upright("some") thick B$ and
$B arrow.r.squiggly B'$ with side conditions checked in $Delta$, then
$upright("GlobalWF") thick italic(e v) thick Theta thick\(Delta\[B'\]\)$.
The same holds for a whole lifecycle $B arrow.r.squiggly^(*) B'$ checked
against the original $Delta$.

#strong[Proposition 6 (Monotonicity is necessary; `badEv_not_mono`).]
There is an evidence relation $italic(e v)_(upright(b a d))$, a globally
well formed two-declaration design, and a valid realization step of one
declaration after which the design is not globally well formed;
consequently $italic(e v)_(upright(b a d))$ is not monotone.

The relation $italic(e v)_(upright(b a d))$ discharges "$A$ is total"
whenever the declaration $A$ reads is still unresolved --- evidence from
absence. Realizing that declaration is a perfectly valid step, and it
destroys the discharge. The monotonicity hypothesis was not part of the
original design; it appeared when Theorem 5 was attacked, and it is a
Kripke-style stability condition on the validation layer: any discharge
mechanism meant to survive refinement must be positive in the
environment.

Binding a representation to a previously unbound concept is likewise a
refinement: typing, satisfaction and global well-formedness are monotone
in $Theta$ (`GlobalWF.of_conceptRefines`). Rebinding a concept to a
different representation is an edit that breaks existing realizations
(`representation_change_is_edit_not_refinement`).

== Refinement versus edit
<refinement-versus-edit>
Theorems 4--5 cover refinement only. Table 1 classifies the operations a
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
    [assign or change a clock domain (§7)], [edit], [domain judgment on
    clients broken],
    [retarget an output binding (§9)], [edit], [completeness or
    single-driver may break],
  )]
  , kind: table
  )

#emph[Table 1. Refinement versus edit.]

Two rows are instructive. Dropping a commitment changes no type, so the
type checker is silent, yet $A$'s own commitment was discharged through
$B$'s and is now unsupported: commitments are part of the interface in
the same load-bearing sense as the expected type. Detaching a
realization is an edit for the same reason. The kernel does not forbid
edits; it declines to promise anything about them.

== Unfolding
<unfolding>
Before time enters, the semantics of a design is #emph[unfolding]:
replace each reference to a realized declaration by its body,
recursively, stopping at unresolved declarations
($upright("Unfolds") thick Delta thick e thick e'$). Let
$upright("DependsOn") thick Delta thick a thick b$ hold when the body of
$a$ refers to $b$.

#strong[Theorem 7 (Unfolding; `Unfolds.det`,
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
agrees with tick evaluation on the first-order fragment (Theorem 15).

= Nominal concepts, representation and dimensions
<nominal-concepts-representation-and-dimensions>
Section 4 typed declarations without saying what a type means. This
section adds the two things a product concept carries that a number does
not --- an identity that survives representation, and a physical
dimension --- and states the theorems that make the identity
trustworthy.

== Nominal identity and the grant
<nominal-identity-and-the-grant>
Suppose concepts were represented only by their representation types, so
that `Tilt` and `MotorAngle` are both
$upright("q") thick upright("Angle")$. Then the wire
`motorTarget := tiltSensor` is well typed and the design is globally
well formed, because nothing in the model records the distinction.
Nominal types $upright("sem") thick s$ over an internal identity record
it: two distinct identities are distinct types regardless of
representation, so the invalid wire is rejected by T-App with no
additional judgment. An explicit relationship
`tiltToMotor : Tilt -> MotorAngle` is an ordinary declaration of arrow
type --- signature-first, possibly unresolved --- and it appears in the
term wherever a crossing occurs. The kernel has no cast, coercion or
conversion.

Nominal identity alone leaves concept values opaque: under T-Ref and
T-App only, a value of $upright("sem") thick s$ can originate only in a
declaration of semantic type (`no_semantic_value_without_declaration`).
To let a formula realize a mapping, representation must be observable
and constructible, and the obvious way to add it destroys what identity
just bought. With global
$upright("rep")_s : upright("sem") thick s arrow.r R$ and
$upright("mk")_s : R arrow.r upright("sem") thick s$ available
everywhere,
$lambda x . thick upright("mk")_(upright(M o t o r))\(upright("rep")_(upright(T i l t)) thick x\)$
is a well-typed `Tilt -> MotorAngle` in the empty environment with no
declaration and no mapping
(`unrestricted_representation_binding_bypasses_semantic_identity`), and
the crossing can hide inside a body whose signature mentions no motor
(`hidden_crossing_inside_unrelated_body`). Observation alone is safe but
cannot realize a mapping.

The grant separates the two. $upright("rep")$ is typed everywhere
(T-Rep); $upright("mk") thick s$ is typed only where $G thick s$ (T-Mk);
client code is typed under $upright("Grant.none")$ and a body under
$upright("Grant.of")$ of its own signature (the definition of
$upright("Satisfies")$). Let $e . upright("constructs") thick s$ hold
when $upright("mk") thick s$ occurs in $e$.

#strong[Theorem 8 (Construction is granted;
`HasType.constructs_granted`).] If
$Theta\;Delta\;G\;Gamma tack.r e : tau$ and
$e . upright("constructs") thick s$, then $G thick s$. Under
$upright("Grant.of") thick tau$: a value of $upright("sem") thick s$ is
built only inside a realization whose signature announces
$upright("sem") thick s$.

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
inlining as provenance (Theorem 14), not as a type property of the
executable.

== Erasure
<erasure>
Let $rho : upright("SemanticId") arrow.r upright("Ty")$ map each concept
to a data type, agreeing with $Theta$ on bound concepts. Erasure
$tau^rho$ replaces $upright("sem") thick s$ by $rho thick s$ throughout
a type; on terms, $upright("rep") thick e$ and
$upright("mk") thick s thick e$ erase to $e^rho$, and the type indices
of operators are erased.

#strong[Theorem 9 (Erasure is sound; `HasType.erase`).] If
$Theta . upright("WF")$, $rho$ agrees with $Theta$, and
$Theta\;Delta\;G\;Gamma tack.r e : tau$, then
$Theta\;Delta^rho\;G'\;Gamma^rho tack.r e^rho : tau^rho$ for every grant
$G'$.

Erasure is not injective --- `Tilt` and `MotorAngle` erase to the same
type (`erase_not_injective`) --- and the untyped baseline is exactly
what erasure leaves: the design the nominal calculus rejects is accepted
after erasure (`baseline_is_erased_modelA`). Generated code is therefore
ordinary code; the semantic layer has no runtime residue.

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

== Dimensions
<dimensions>
A physical quantity has type $upright("q") thick d$. There is no
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

Dimension and identity are orthogonal. `Tilt` and `MotorAngle` both
bound to $upright("q") thick upright("Angle")$ remain distinct types
(`same_dimension_does_not_imply_same_semantic_identity`); a mapping
realized by the dimensioned formula
$lambda x . thick upright("mk") thick upright("Brightness") thick\(upright("rep") thick x dot.op italic(g a i n)\)$
with $italic(g a i n) : upright("q") thick\(0 - upright("Angle")\)$ is
typed, a dimension error inside it is caught by the same typing, and the
formula cannot manufacture a `MotorAngle` despite the shared dimension
(`explicit_semantic_mapping_uses_dimensioned_formula`). The association
between a concept and its dimension lives in $Theta$, not in the
identity and not in the type constructor.

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
surface's definitional families (§8.4), where matching against closed
dimensions instantiates them.

= Reactive semantics in one domain
<reactive-semantics-in-one-domain>
Every declaration denotes a stream over a tick domain. This section
gives the single-domain semantics --- one primitive, $upright("delay")$
--- and proves it deterministic and total on causal designs. Section 7
generalizes it to many domains and shows that this section is the
diagonal of that one.

== Values and evaluation
<values-and-evaluation>
Values are booleans, naturals (which also carry every
$upright("q") thick d$\; the executable kernel's magnitudes are
naturals), tagged concept values $upright("sem") thick s thick v$,
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

$ frac(rho scripts(tack.r)_t e arrow.b.double upright("sem") thick s thick w, rho scripts(tack.r)_t upright("rep") thick e arrow.b.double w) #h(2em) frac(rho scripts(tack.r)_t e arrow.b.double w, rho scripts(tack.r)_t upright("mk") thick s thick e arrow.b.double upright("sem") thick s thick w) $

$ frac(rho scripts(tack.r)_0 i arrow.b.double v, rho scripts(tack.r)_0 upright("delay") thick i thick e arrow.b.double v) med upright("(E-Delay0)") #h(2em) frac(rho scripts(tack.r)_t e arrow.b.double v, rho scripts(tack.r)_(t + 1) upright("delay") thick i thick e arrow.b.double v) med upright("(E-DelayS)") $

$ frac(rho scripts(tack.r)_t f arrow.b.double v_f quad rho scripts(tack.r)_t z arrow.b.double v_z quad rho scripts(tack.r)_t l arrow.b.double upright("list") thin\[thin\], rho scripts(tack.r)_t upright("fold") thick f thick z thick l arrow.b.double v_z) med upright("(E-FoldNil)") $

$ frac(rho scripts(tack.r)_t f arrow.b.double v_f quad rho scripts(tack.r)_t z arrow.b.double v_z quad rho scripts(tack.r)_t l arrow.b.double upright("list") thin\(x thin upright("::") thin italic(x s)\)\
 \[upright("list") thin italic(x s)\,thin v_z\,thin v_f\]scripts(tack.r)_t upright("fold") thick\#2 thick\#1 thick\#0 arrow.b.double r #h(2em)\[r\,thin x\,thin v_f\]scripts(tack.r)_t\#2 thick\#1 thick\#0 arrow.b.double v, rho scripts(tack.r)_t upright("fold") thick f thick z thick l arrow.b.double v) med upright("(E-FoldCons)") $

#emph[Figure 4. Single-domain evaluation (`Ev`), with $Delta$ and $I$
ambient. In one domain $upright("sync") thick c$ evaluates exactly as
$upright("delay")$ (rules `syncZero`, `syncSucc`), which §7 justifies.
Literals evaluate to themselves. $\#i$ is de Bruijn index $i$.]

Three points of Figure 4 deserve comment. An unresolved declaration is
an #emph[input]: E-Input reads $I thick delta thick t$. A realized
declaration is evaluated from its body at the current tick in the
#emph[empty] environment (E-Real): a reference's value never depends on
the local environment of the reader, which is what makes a declaration a
stream rather than a function of its call site
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
totality is a separate lemma by induction on the list (§8.1).

#strong[Theorem 10 (Determinism; `Ev.det`).] If
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

#strong[Theorem 11 (Strict cycles have no value;
`Ev.not_of_strictCyclic`).] If $a$ lies on a cycle of references passing
through neither a delayed operand nor a lambda, then for every tick and
environment there is no $v$ with
$rho scripts(tack.r)_t upright("declRef") thick a arrow.b.double v$.

Not "some default", not "one of several": no derivation exists. A gap
should be recorded. A cycle guarded by a lambda, `A := λx. A x`, is
rejected by $upright("Causal")$ yet `declRef A` does evaluate --- to a
closure; only applying it diverges. $upright("Causal")$ is conservative
for lambda-guarded cycles and Theorem 11 covers strict cycles only.

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
cal(R)_Theta^A\[upright("sem") thick s\]thick v arrow.l.r.double & exists w . thick v = upright("sem") thick s thick w and forall R . thick Theta thick s = upright("some") thick R arrow.r cal(R)^A\[R\]thick w $

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

#strong[Theorem 12 (Fundamental theorem; `fundamental`).] Let
$Theta . upright("WF")$, let $italic(r a n k)\,R$ witness
$upright("Causal") thick Delta$, let
$upright("GlobalWF") thick italic(e v) thick Theta thick Delta$ and let
$I$ be well typed. Then for every tick $t$, bound $r$, grant $G$, and
$Theta\;Delta\;G\;Gamma tack.r e : tau$, and every $rho$ related to
$Gamma$ such that every instantaneous reference of $e$ has rank below
$r$, there is $v$ with $rho scripts(tack.r)_t e arrow.b.double v$ and
$cal(R)_Theta^(upright("Apply") thick Delta thick I thick t)\[tau\]thick v$.

#emph[Proof sketch.] Lexicographic induction on
$\(t\,r\,upright("derivation")\)$. A delayed operand at tick $t + 1$ is
evaluated at tick $t$ under #emph[any] rank (the first component
decreases); an instantaneous reference to a realized declaration $delta$
is evaluated at the same tick under the smaller bound
$italic(r a n k) thick delta$ (the second decreases), and its body is
well typed under the grant of its own signature by
$upright("GlobalWF")$\; every other case is the induction on the
derivation. The $upright("fold")$ case uses `fold_total` (§8.1).
$square.stroked.tiny$

#strong[Theorem 13 (Totality; `reactive_total`, `Ev.red`).] In a causal,
globally well formed design with well-typed inputs, every declared
identity has a value at every tick, and that value --- unique by Theorem
10 --- is related to its expected type.

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
induction of Theorem 12 needs. A delayed closure would be a value at
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
therefore belongs to declarations, and a reusable stateful component is
instantiated into fresh declarations (§10) rather than abstracted over.

Initialization is semantic, not validation. Every $upright("delay")$
carries an explicit initial value. Two toy relations without one show
why: the first tick is either undefined
(`first_tick_undefined_without_init`) or nondeterministic
(`first_tick_nondeterministic_without_init`).

== Provenance through time
<provenance-through-time>
State carries semantic tags; it never creates them. Let
$v . upright("Taints") thick s$ hold when the tag $s$ occurs anywhere
inside $v$ --- including inside closures' environments and bodies.

#strong[Theorem 14 (Tag provenance; `Ev.tag_provenance`,
`temporal_state_preserves_semantic_identity`).] If no realization in
$Delta$ constructs $s$, no input value is tainted by $s$, $e$ does not
construct $s$ and $rho$ is clean, then every value
$rho scripts(tack.r)_t e arrow.b.double v$ is clean. In particular a delayed
value carries exactly the tag of the value delayed.

Combined with Theorem 8 this is the runtime half of semantic isolation:
a concept appears in a value only if some signature announces it or some
input carries it, at every tick. The typing rule
$upright("delay") : tau arrow.r tau arrow.r tau$ at data $tau$ gives the
static half --- a delayed tilt is a tilt, and a backward difference over
a time step has dimension $upright("Length") - upright("Time")$ with no
derivative primitive.

== Wiring designs and unfolding
<wiring-designs-and-unfolding>
The first-order fragment of interest to a compiler consists of
#emph[wiring] terms --- references, literals, operators, applications,
$upright("rep")$, $upright("mk")$, $upright("delay")$ and
$upright("sync")$, with no lambda --- and designs all of whose bodies
are wiring terms. On this fragment closures never arise (`Ev.noClo`) and
evaluation is independent of the local environment
(`Ev.env_irrelevant`).

#strong[Theorem 15 (Unfolding preserves stepping;
`unfolds_preserves_eval`).] On a wiring design with closure-free inputs,
if $upright("Unfolds") thick Delta thick e thick e'$ then
$rho scripts(tack.r)_t e arrow.b.double v$ iff
$rho scripts(tack.r)_t e' arrow.b.double v$.

This licenses inlining: the value of the unfolded program at a tick is
the value of the referencing program. A more general statement is
available for #emph[pure] terms --- closed terms with no reference,
state or transport --- whose value is the same in every design, at every
tick, under every input (`Ev.pure`); §8.4 uses it for the definitional
library.

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

#emph[Table 2. Derived temporal operators
(`Experiments/ReactiveAlternatives.lean`).]

There is no signal type in $upright("Ty")$: under this semantics a
signal type would be inhabited by exactly the terms of the underlying
type and would reject nothing. There is no event type: within one domain
an input delivers at most one value per tick by construction, so an
occurrence is a stream of optional type, and the streams of type
$upright("opt") thick tau$ are exactly the streams of multiplicity at
most one. What separates an occurrence from an optional value can only
be seen when a source ticks faster than its observer, which is a
cross-domain question (§7.5). State has no identity of its own: a cell
is a $upright("delay")$ in a declaration body, consumers refer to the
declaration, and there is consequently no notion of two writers to one
cell.

= Clock domains
<clock-domains>
"Contact and orientation move with the interaction; temperature moves
with the environment." A designer can say this before any rate is known,
and it is a statement about which quantities update together, not about
how often. The calculus records it as a nominal #strong[clock domain]
and treats rate as data outside the kernel.

== Schedules and the domain judgment
<schedules-and-the-domain-judgment>
The time model is one global base tick and a schedule
$S : upright("ClockId") arrow.r bb(N) arrow.r upright("Bool")$ saying at
which global ticks each domain activates. A period $n$ induces the
schedule $t med mod med n = 0$ (`Sched.periodic`); the schedule lives
outside the design. Domain-local time is not a separate counter but the
sequence of a domain's activations. The last activation of $c$ strictly
before $t$ is
$ upright("prevAct") thick S thick c thick 0 = upright("none")\,#h(2em) upright("prevAct") thick S thick c thick\(t + 1\)= upright("if") thick S thick c thick t thick upright("then") thick upright("some") thick t thick upright("else") thick upright("prevAct") thick S thick c thick t\, $
with
$upright("prevAct") thick S thick c thick t = upright("some") thick t' arrow.r.double t' < t and S thick c thick t'$.

Each declaration is assigned a domain by the clock environment
$upright(K)$, or none if it is a pure mapping usable anywhere. The clock
is interface data in every sense that matters --- clients' validity
depends on it, it is frozen under refinement, and changing it is an edit
(Table 1) --- and it is stored as a projection beside the interface, as
a concept's representation is stored in $Theta$ rather than in the type.

The #strong[domain judgment]
$upright("Clocked") thick upright(K) thick c thick e$, for
$c : upright("Option") thick upright("ClockId")$, says that $e$ may be
evaluated in domain $c$:
$ upright("Clocked") thick upright(K) thick c thick\(upright("declRef") thick delta\)arrow.l.r.double & upright(K) thick delta = upright("none") thick or thick upright(K) thick delta = c\
upright("Clocked") thick upright(K) thick\(upright("some") thick c\)thick\(upright("delay") thick i thick e\)arrow.l.r.double & upright("Clocked") thick upright(K) thick\(upright("some") thick c\)thick i and upright("Clocked") thick upright(K) thick\(upright("some") thick c\)thick e\
upright("Clocked") thick upright(K) thick\(upright("some") thick c\)thick\(upright("sync") thick c' thick i thick e\)arrow.l.r.double & upright("Clocked") thick upright(K) thick\(upright("some") thick c\)thick i and upright("Clocked") thick upright(K) thick\(upright("some") thick c'\)thick e\
upright("Clocked") thick upright(K) thick upright("none") thick\(upright("delay") thick i thick e\)arrow.l.r.double & upright("False") #h(2em) #h(2em) upright("Clocked") thick upright(K) thick upright("none") thick\(upright("sync") thick c' thick i thick e\)arrow.l.r.double upright("False") $
and homomorphically elsewhere. A reference stays in its domain or is
agnostic; a delay needs a domain; $upright("sync") thick c'$ switches
the domain of its operand. A design is well clocked when every body is
clocked in its own declaration's domain. Typing is unchanged and blind
to domains: the direct wire between two domains at the same value type
is well typed and rejected only by $upright("Clocked")$. Placing the
domain in the type instead was tried and set aside: every pure mapping
would then need clock polymorphism (`clocked_type_forces_polymorphism`),
and nothing the type rejects is missed by the judgment.

== Multi-domain evaluation
<multi-domain-evaluation>
The judgment $rho scripts(tack.r)_t^c e arrow.b.double v$ --- in domain $c$ at
global tick $t$, with $S$, $Delta$, $I$ ambient --- is $upright("Ev")$
with the two temporal rules replaced by four (`MEv`):
$ frac(upright("prevAct") thick S thick c thick t = upright("none") quad rho scripts(tack.r)_t^c i arrow.b.double v, rho scripts(tack.r)_t^c upright("delay") thick i thick e arrow.b.double v) #h(2em) frac(upright("prevAct") thick S thick c thick t = upright("some") thick t' quad rho scripts(tack.r)_(t')^c e arrow.b.double v, rho scripts(tack.r)_t^c upright("delay") thick i thick e arrow.b.double v) $
$ frac(upright("prevAct") thick S thick c' thick t = upright("none") quad rho scripts(tack.r)_t^c i arrow.b.double v, rho scripts(tack.r)_t^c upright("sync") thick c' thick i thick e arrow.b.double v) #h(2em) frac(upright("prevAct") thick S thick c' thick t = upright("some") thick t' quad rho scripts(tack.r)_(t')^(c') e arrow.b.double v, rho scripts(tack.r)_t^c upright("sync") thick c' thick i thick e arrow.b.double v) $
$upright("delay")$ reads the previous activation of the current domain;
$upright("sync") thick c'$ reads the previous activation of $c'$ and
evaluates its operand #emph[there], in $c'$. All other rules carry $c$
unchanged.

#strong[Theorem 16 (Memory is transport at the own domain;
`delay_is_sync_own`, `clocked_delay_iff_sync_own`).]
$rho scripts(tack.r)_t^c upright("delay") thick i thick e arrow.b.double v$ iff
$rho scripts(tack.r)_t^c upright("sync") thick c thick i thick e arrow.b.double v$,
and $upright("delay") thick i thick e$ is clocked in $c$ iff
$upright("sync") thick c thick i thick e$ is.

The kernel therefore has one temporal primitive --- read a domain at its
previous activation --- and $upright("delay")$ is notation for its
diagonal. A $upright("delay")$ in a slow domain reads three global ticks
back where a $upright("delay")$ in a fast one reads one, with the same
syntax.

#strong[Theorem 17 (Single-domain embedding;
`single_domain_embedding`).] Under the always-active schedule,
$rho scripts(tack.r)_t^c e arrow.b.double v$ iff
$rho scripts(tack.r)_t e arrow.b.double v$, for every $c$.

The results of §6 are thus the one-domain special case of this section
rather than a replaced machine.

#strong[Theorem 18 (Determinism; `MEv.det`).] Multi-domain evaluation is
a partial function, for every schedule.

#strong[Theorem 19 (Totality in every domain; `mfundamental`,
`multi_domain_total`).] In a causal, globally well formed design with
inputs well typed in every domain, every declared identity has a value
in every domain at every tick, related to its expected type.

The proof reuses the logical relation of §6.3 with the application
relation
$upright("MApply") thick S thick Delta thick I thick c thick t$, and the
same lexicographic induction: a transport at $t$ evaluates its operand
at $t' < t$ under any rank. Causality is the #emph[same]
$upright("Causal") thick Delta$: a transport's operand is never
instantaneous, so no cross-domain cycle can be. An interpreter
$upright("mevalF")$ is proved sound (`mevalF_sound`). Tag provenance
holds across domains (`MEv.tag_provenance`): transport changes timing,
not identity, and a crossing from `Tilt@fast` to `Tilt@slow` authorizes
neither `Tilt -> MotorAngle` nor
$upright("q") thick upright("Length") arrow.r upright("q") thick upright("Time")$,
by the typing rule.

== Strictly before, and what the alternative exposes
<strictly-before-and-what-the-alternative-exposes>
A transport sees only source activations strictly before the destination
tick. That is a choice with an observable alternative, and the
alternative was built.

#strong[Theorem 20 (Same-tick visibility exposes the scheduler;
`scheduling_order_observable`).] Let $upright("MEv")_lt.eq$ be the
semantics in which a transport may also see a simultaneously active
source, resolved by a priority between domains. There is a two-domain
design, a schedule and an input such that two priorities give two
different values to the same declaration at the same tick.

At tick 1 both domains are active for the first time; with the source
first the transport delivers the source's current value, with the
destination first it delivers the initial value. The strictly-before
rule has no such parameter, and Theorem 18 has no order between
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

== Occurrences across domains: the window buffer
<occurrences-across-domains-the-window-buffer>
Within one domain an occurrence is a stream of optional type. Across
domains this fails: $upright("sync")$ is a zero-order hold, so a slow
consumer of a fast event source sees the last value only. Two fast
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

#strong[Theorem 21 (The window is computed;
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

The point for the calculus is what was #emph[not] added: no event type,
no buffer primitive, no scheduler order, no same-tick visibility, no
implicit overflow rule. An event stream is a data-typed declaration in a
domain; an occurrence is its value at an activation; a lossless view of
it across domains is the five declarations; `latest`, `count`,
`coalesce` are ordinary computations over `window`.

= Data, the recursor and polymorphism
<data-the-recursor-and-polymorphism>
The kernel of §3--7 computes with booleans, counts, quantities, concepts
and optional values and abstracts with lambdas over them. A product
needs more: a mode tested against a finite set of modes, every reading
below a threshold, a pair of readings, a calibration mapped over a
collection. This section records the smallest typed data basis that
supports them, what could not be derived and why, and how polymorphism
is provided without a type variable in the kernel.

== The list recursor
<the-list-recursor>
$upright("fold") thick f thick z thick l$ is a #emph[term former], not a
registered operator. The kernel has no recursion, deliberately; a total
language needs an eliminator for its inductive data, and
$upright("fold")$ is the one construct that applies a function value in
the course of evaluation. Registered operators never apply closures. The
alternative of one primitive per collection operation was rejected
because a primitive cannot apply a closure and each would need its own
evaluation rule; the alternative of bounded unrolling was rejected
because lists --- the cross-domain window --- are unbounded.

#strong[Theorem 22 (The recursor is total; `fold_total`,
`mfold_total`).] If $v_f$ is related at
$tau arrow.r sigma arrow.r sigma$, $v_z$ at $sigma$ and every element of
$arrow(w)$ at $tau$, then
$\[upright("list") thin arrow(w)\,v_z\,v_f\]scripts(tack.r)_t upright("fold") thick\#2 thick\#1 thick\#0 arrow.b.double r$
for some $r$ related at $sigma$.

The proof is an induction on the list, separate from the fundamental
theorem, which invokes it in its $upright("fold")$ case. Every
collection operation --- `map`, `filter`, `any`, `all`, `contains`,
`append`, `sum`, `zip`, and through $upright("toList")$ the option
eliminators --- is a definition over $upright("fold")$, and each is
proved to compute the mathematical function it names through one general
lemma: the recursor computes $upright("List.foldr") thick g$ whenever
the step closure implements $g$ on the reachable accumulators
(`fold_spec`\; then `any_spec`, `all_spec`, `map_spec`, `filter_spec`,
`min_spec`, `clamp_spec`, …). Finite quantification is a fold ---
$forall x in italic(x s) . thin P thin x$ iff `all xs P` evaluates to
true (`forall_in_list`, `exists_in_list`) --- and a finite-set literal
means membership with duplicates irrelevant (`oneOf_mem`,
`oneOf_dup_irrelevant`), so there is no `Set` type and no uniqueness
convention.

== Products, and why not Church pairs
<products-and-why-not-church-pairs>
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
only; they are never a component interface or an output bundle (§10
shows what a tuple-returning declaration does to the dependency graph).

== Equality with its evidence in the syntax
<equality-with-its-evidence-in-the-syntax>
$upright("eq")_tau^h$ is structural equality at every data type ---
booleans, numbers, $upright("none")$/$upright("some")$, pairs and lists
componentwise, concept values by tag and representation --- with the
proof $h : tau . upright("Data")$ carried #emph[in the syntax]. This is
the kernel's only capability evidence: an equality on a function type is
unwritable rather than ill typed, which keeps T-Prim unconditional. On
first-order values structural equality is equality (`Value.beq_iff`, by
a mutual induction over the nested value type).

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

== Rank-1 polymorphism by families
<rank-1-polymorphism-by-families>
Five models of polymorphism were compared: a monomorphic kernel;
per-type duplication; rank-1 parametric polymorphism; System F; higher
rank. The one adopted is rank-1 #emph[as definitional families]: every
library entry is a function $upright("Ty") arrow.r upright("Expr")$ (or
$upright("Dim") arrow.r upright("Expr")$) in the metalanguage, and a
scheme is a pattern over type and dimension variables with capability
constraints. The kernel sees only the instances
(`instances_are_monomorphic`: three uses of `min` are three kernel
terms), and T-Prim, T-App and Theorem 1 are unchanged.

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
$alpha arrow.r alpha arrow.r alpha$, instantiated at concept $s$,
rejects an argument of concept $s' eq.not s$, the representations never
consulted (`generic_preserves_identity`); the same for
$upright("q") thick d$ versus $upright("q") thick d'$
(`generic_preserves_dimension`). This is Reynolds's abstraction
@reynolds1983types and Wadler's free theorems @wadler1989free at the
level of syntax: a family cannot inspect what it is instantiated at,
because it is instantiated by substitution into a closed term.

== The library as combinators, and inlining
<the-library-as-combinators-and-inlining>
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

= Physical outputs
<physical-outputs>
A declaration computes a value; it does not move hardware. Physical
effect happens only through an explicit #strong[drive edge] from a
declaration to a nominally identified #strong[output] --- a logical
actuator channel, a resource in a different sort from both concepts and
declarations: "the desired steering angle" is a value, "the steering
motor" is a resource.

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

#strong[Theorem 23 (One driver, one output;
`single_driver_output_deterministic`,
`multiple_direct_drivers_rejected`).] Under
$upright("SingleDriver") thick beta$, $upright("PhysicalOutput")$ is a
partial function of $o$ and $t$. Two declarations driving one output ---
each well typed, well clocked, causal and individually well formed ---
violate $upright("SingleDriver")$ and nothing else, and there is a tick
at which the output receives two values.

The principle is #emph[many contributors, one explicit final driver].
Contributors are dependencies: `base + corr -> final -> motor` passes
every check; priority is a conditional in the single driver; blend,
maximum and clamp are ordinary declarations of the target type. Why
arbitration must be explicit is shown rather than argued: first-wins,
last-wins and maximum over the same value graph give three different
physical outputs (`hidden_arbitration_observable`). Binding an unbound
declaration to an undriven output is a refinement and preserves
$upright("SingleDriver")$ (`first_output_binding_is_monotone`); binding
to a driven output is invalid; retargeting, renaming or detaching an
edge invalidates an unchanged design.

Two alternatives were formalized in toy form. Direct effect rows --- the
set of outputs a declaration drives --- are exactly the drive edges, and
single-driver is exactly their pairwise disjointness; propagated rows
flag a valid design in which a display reads the driver; action values
move the conflict into the collector that consumes them, which must then
be a policy, which is the single driver by another name. None of this
bears on richer effect systems @plotkin2013handlers\; it says these
formulations add no rejection the single-driver rule lacks.

Finally, the dual form. Once zero-input relationships have the canonical
interface type `() -> A` (normalized above the kernel to `A`, with the
unit eliminated before any term is typed --- the kernel has no unit
type, and `delay` inside a zero-input declaration is why: a unit binder
would forbid memory there, `delay_not_under_binder`), the form `A -> ()`
suggests itself as a consumer. It cannot name one: in a pure total
language every function into the one-point type is the same function
(`unit_codomain_collapse`, by function extensionality), so two
"consumers" are indistinguishable (`consumers_indistinguishable`), and
the evaluation relation has no effect component
(`eval_independent_of_drives`). Naming a receiver needs an output
semantics, and the calculus already has exactly one.

= Composition by renaming
<composition-by-renaming>
A second lamp should reuse the first's behavior without copying it. This
needs a component with a promised interface, instantiated with fresh
identity and bound to other behaviors. The section's result is that all
of it is derivable from what §4 provides --- realization plus renaming
--- and that the flattened system is checked by the unchanged judgments.

== Equivariance
<equivariance>
A renaming $r$ bundles four maps --- on declaration, semantic, clock and
output identities. Renaming acts on types (through $upright("sem")$), on
terms, on interfaces, on declarations and pointwise on environments;
$Delta . upright("RenamedBy") thick r thick Delta'$ says $Delta'$ stores
the renamed declaration of $Delta$ at the renamed identity.

#strong[Theorem 24 (Equivariance; `HasType.rename`, `Satisfies.rename`,
`Clocked.rename`).] If $Theta\;Delta\;G\;Gamma tack.r e : tau$ and
$Theta'\,Delta'\,G'$ are the images of $Theta\,Delta\,G$ under $r$
(agreement on the image, with no injectivity required), then
$Theta'\;Delta'\;G'\;Gamma^r tack.r e^r : tau^r$\; likewise for
satisfaction, and for the domain judgment under a clock environment that
agrees on the declared identities.

Evidence must be equivariant as well (`Evidence.Equivariant`), an
abstract condition beside monotonicity. Nothing else is new in the
composition theory; the rest is definitions over Theorem 24 and §4.

== Components, instances and flattening
<components-instances-and-flattening>
A #strong[port] is a template declaration by local identity with the
public part of its interface and its parameter clock. A #strong[behavior
interface] has required ports (unresolved declarations a composer
binds), provided ports, elaboration-time parameters (unresolved
data-typed declarations bound to closed constants at instantiation) and
clock parameters. A #strong[component] is an interface, a template
design over local identities below a width $W$, and a partition of its
concepts and outputs into private (freshened per instance) and shared.
$upright("Realizes") thick italic(e v) thick C$ is a predicate over the
existing judgments: the template is a well-formed design (`Design.WF`:
$upright("GlobalWF")$, $Theta . upright("WF")$, well clocked, causal,
$upright("DriveWF")$, $upright("SingleDriver")$), every required port is
an unresolved declaration of the stated interface, every provided port
is declared with it, parameters are unresolved, data-typed and
clock-free.

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
$upright("sync") thick c thick italic(i n i t) thick\(upright("declRef") thick italic(s r c)\)$.
The result is a design, consumed by every existing judgment unchanged.

#strong[Theorem 25 (Flattening is well formed; `binding_satisfies`,
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

#strong[Theorem 26 (Modular semantics, restricted; `eval_flat_to_inst`,
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
#emph[restrictions] of the design, the component with an unresolved copy
of each crossing-in declaration as a required port and the residual with
an unresolved copy of each crossing-out member, and forms a two-instance
system with one direct binding per crossing. No body is translated or
copied across the boundary. Both templates realize their inferred
interfaces (`restrict_realizes`, needing evidence that depends only on
the interfaces of the referenced declarations,
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
beyond core): 11 in `Core` (the calculus of §3--7 and §9), 12 in
`Behavior` (§10), 19 in `Surface` (the definitional library,
polymorphism, units, buffering and the boundary constructions above the
kernel), 2 in `Validation` (hardware and capacity, outside this paper),
and 24 experiment modules holding alternatives, counterexamples and
executed examples; about 26 500 lines and 1 545 theorem declarations. It
builds with no `sorry`. The axioms are propositional extensionality and
quotient soundness, the latter only through function extensionality and
the choice-free rational quotient used by the unit laws; classical
choice is absent, and the whole development was re-audited for it at
every phase.

Three proof-engineering choices carried the metatheory.

#emph[One inductive relation.] $upright("Ev")$ and $upright("MEv")$ are
ordinary inductive relations with no mutual recursion and no fixpoint,
because the recursor's rule unrolls through the environment (§6.1).
Every induction on evaluation --- determinism, provenance,
closure-freeness, environment irrelevance, unfolding --- extends by one
case when a construct is added; the transport primitive and the recursor
entered this way, and every earlier theorem was re-established without a
change of statement.

#emph[One logical relation, generic in application.] $cal(R)$ is
parameterized by an application relation so that the single- and
multi-domain semantics share it; at data types it is independent of that
parameter (`Red_data`), which is the fact that lets a value cross a
tick. The lexicographic induction on (tick, rank, derivation) is written
once, in `fundamental`, and once more in `mfundamental` with
$upright("prevAct")$ in place of the predecessor.

#emph[Counterexamples as theorems, traces by a proved interpreter.]
Every rejected alternative is a theorem whose content is a rejection,
stated on a concrete design and discharged by `decide` or by running
$upright("evalF")$/$upright("mevalF")$ (proved sound for the relations)
inside the checker. There is no test suite beside the proofs; the
executed examples are part of the same `lake build`. Several results are
recorded as trivial by definition --- the typing half of client
stability, the well-formedness of a refinement target --- and are
reported as such rather than presented as content.

Extraction to an implementation is not part of the development. The
production toolchain implements the calculus in Rust and is tested
differentially against the traces the interpreter computes; that
correspondence is a tested claim, not a theorem, and is recorded as such
in the monograph.

= Related work
<related-work>
#emph[Synchronous languages.] $lambda_(upright(B D L))$'s time model is
that of Lustre @halbwachs1991lustre and Esterel @berry1992esterel: a
global logical tick, streams as the meaning of declarations, memory as
`pre` with an explicit initial value, causality as acyclicity of
instantaneous dependencies. Two departures are deliberate. Clocks are
nominal and authored, not inferred
@colaco2003clocks@biernacki2008clock@caspi1996kahn, because the
information that would let a clock be inferred arrives at realization
binding, after the design has been reasoned about; and a cross-clock
read is a single primitive with a strictly-before rule and an explicit
initial value, so that no simultaneously active domains ever see each
other and no `when`/`merge` calculus of sub-sampling is needed ---
sub-domains evaluated in one instant are the same domain here. The
window buffer of §7.5 plays the role that sampling operators play in
Lucid Synchrone. Vélus @bourke2017velus verifies a Lustre compiler; the
present development verifies a calculus and its metatheory, and leaves
the compiler to differential testing. Zélus @bourke2013zelus and
state-machine extensions @colaco2005state address continuous time and
modes, neither of which the calculus has.

#emph[Functional reactive programming.] FRP
@elliott1997fran@nilsson2002frp@cooper2006frtime makes signals
first-class values. The calculus has no signal type: every declaration
is a stream by interpretation, and a signal type would reject nothing
(§6.7). Typed FRP with modal or temporal types
@krishnaswami2013frp@jeffrey2012ltl@cave2014fair uses the type to
control what may be remembered; here that control is the data
restriction on $upright("delay")$ and the empty-context restriction,
both forced by the totality proof, and the guarantee is totality rather
than the absence of space leaks.

#emph[Logical relations.] The totality proof is a step-indexed logical
relation @appel2001indexed@ahmed2006stepindexed in which the index is
the tick and a rank on declarations is a second index; the arrow clause
is tick-indexed and the data clauses are not, which is what makes memory
sound. Kripke-style monotonicity conditions on a world are standard in
such proofs; the evidence-monotonicity condition of §4.3 is the same
shape imposed on a #emph[validation layer] rather than on a store.

#emph[Modules, abstract types and nominal types.] Persistent
declarations are the interface/implementation separation of module
signatures @leroy1994manifest@harper1994modules with a growable
commitment set whose growth is a first-class operation on a
declared-but-undefined name. The grant is the private constructor of an
abstract type @mitchell1988abstract@reynolds1983types with the
capability derived from the signature. Nominal type identity is the
ordinary mechanism of a nominal type system @pierce2002tapl\; the
contribution is the pair of erasure and provenance theorems and the
refuted alternatives, not the mechanism.

#emph[Units of measure.] Kennedy's dimension types
@kennedy1997units@kennedy2010units put dimension polymorphism in the
type system. The calculus keeps dimensions monomorphic in operator types
and provides dimension polymorphism only in surface families
instantiated by matching (§8.4), with units entirely outside the kernel.

#emph[Typed holes and live programming.] Hazelnut
@omar2017hazelnut@omar2019live gives a semantics to programs with holes
and edits. An unresolved declaration is not a hole position in a term
but a declaration whose realization is absent, referred to by identity
and typed by its interface; the refinement order plays the role of the
edit action calculus, restricted to the operations under which clients
are stable.

#emph[Effects.] The single-driver discipline is not an effect system
@plotkin2013handlers\; §9 records that effect rows and action values, in
the toy forms tried, add no rejection the drive edge lacks. Statecharts
@harel1987statecharts and model-based design tools supply modes and
hierarchy that the calculus encodes as ordinary declarations.

#emph[Expressiveness.] The negative results of §7.5 and §8 are
statements about what a construct can and cannot express relative to the
kernel --- in Felleisen's sense @felleisen1990expressive of whether a
construct is definable by a local translation --- with the difference
that each is a mechanized theorem about a specific candidate rather than
a general expressiveness result.

= Limitations and open problems
<limitations-and-open-problems>
The paper's claims are bounded by the following, each recorded in the
development.

- #emph[Causality is conservative for lambda-guarded cycles.]
  `A := λx. A x` is rejected by $upright("Causal")$ although `declRef A`
  evaluates to a closure; Theorem 11 covers strict cycles only. A finer
  criterion that admits productive higher-order cycles has not been
  formulated.
- #emph[Modular semantics is proved for a fragment.] Theorem 26 holds
  for single-domain wiring designs with direct or constant bindings.
  Transported bindings under $upright("MEv")$ need a domain-indexed
  modular input; higher-order bodies need a relation between closures
  across the two evaluations. Both are open.
- #emph[Evidence is abstract.] The kernel imposes monotonicity,
  equivariance and port-soundness on the validation layer's evidence and
  proves nothing about a concrete discharge mechanism; a compositional
  evidence model that discharges these once is future work.
- #emph[No sums.] Enumerations with payloads are encoded; a kernel sum
  would be one eliminator term former, and its absence is a decision to
  stop where the executed cases stopped.
- #emph[Magnitudes are naturals.] The executable kernel's quantities are
  natural numbers, so its unit registry is exact only for integer
  scales; the unit laws are proved over an abstract scalar domain
  instantiated symbolically, and floating-point implementations are held
  to toleranced versions above the kernel.
- #emph[No minimality theorem.] "Minimal" means minimal among the
  formalized candidates; several alternatives (flow-sensitive semantic
  analyses, structural typing with a separate role judgment) were argued
  against rather than refuted.
- #emph[Nothing about designers.] The calculus was shaped by
  requirements from a design workflow; whether it serves designers is an
  empirical question no theorem addresses.

= Conclusion
<conclusion>
$lambda_(upright(B D L))$ is a small calculus whose content is in its
environments and the disciplines they impose rather than in its terms: a
declaration environment read by typing through the type view and by
evaluation through the realization view, with a refinement order under
which clients are stable; a concept environment read through write-once
bindings, with a grant derived from the signature under which
construction is authorized; a clock environment read by a judgment that
typing never sees; and an output environment read by a drive discipline
with a single driver. One temporal primitive gives memory and transport,
and a tick-indexed logical relation gives totality on causal designs in
one domain and in many. The negative results --- a scheduler made
observable by same-tick visibility, an evidence relation destroyed by a
valid realization, a hidden concept crossing admitted by unrestricted
construction, three physical outputs from one design under hidden
arbitration, a lossy summary for every bounded buffer --- are mechanized
alongside the positive ones and are, we think, as much a part of the
calculus's specification as the rules.

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
