// BDL paper - ACM-inspired Typst layout.
// Primary editable source: paper.md -> body.typ (generated with Pandoc).
// This file supplies the paper chrome and two-column layout.

#set page(
  paper: "us-letter",
  margin: (top: 0.58in, bottom: 0.62in, left: 0.68in, right: 0.68in),
  numbering: "1",
  number-align: center,
)
#set text(font: "Libertinus Serif", size: 9pt, lang: "en")
#set par(justify: true, leading: 0.52em)
#set heading(numbering: "1.1")
#set enum(indent: 1.15em, body-indent: 0.45em)
#set list(indent: 1.05em, body-indent: 0.45em)
#show raw: set text(font: "DejaVu Sans Mono", size: 0.9em)

#show heading.where(level: 1): set text(font: "Libertinus Serif", size: 10.2pt, weight: "bold")
#show heading.where(level: 2): set text(font: "Libertinus Serif", size: 9.2pt, weight: "bold")
#show heading.where(level: 3): set text(font: "Libertinus Serif", size: 9pt, weight: "bold", style: "italic")

#let smallcaps(body) = text(font: "Libertinus Serif", weight: "bold", size: 8.2pt, body)

#align(center)[
  #text(font: "Libertinus Serif", size: 17pt, weight: "bold")[
    Executable Behavioral Design for Industrial Designers
  ]
  #v(3pt)
  #text(size: 11.2pt, weight: "bold")[
    Signature-First Relationships, Progressive Refinement, and a Mechanically Derived Kernel
  ]
  #v(7pt)
  #text(size: 9.2pt)[ZHU ZHEHAO]
  #linebreak()
  #text(size: 8.3pt, style: "italic")[Research Design Draft]
]

#v(10pt)

#smallcaps[ABSTRACT]
#v(2pt)
#set text(size: 8.5pt)
Industrial products increasingly embed sensing, temporal logic, software, and control, yet industrial designers still lack a behavioral design medium with the immediacy that CAD provides for geometry. Existing prototyping and visual-programming tools reduce implementation cost but preserve engineering-oriented representations such as state transitions, execution steps, callbacks, or node-level computation. This paper proposes BDL, a Behavior Design Language whose primary artifacts are typed product relationships. A Mapping Block is created from a semantic signature, for example $?f: upright("Tilt") arrow.r upright("Brightness")$, and may remain unresolved while the surrounding design is authored and checked; the claim is not that designers think signature-first but that an unresolved relationship is a legal, statically meaningful state, so that stopping between declaration and realization costs nothing. The kernel beneath the surface was derived by a mechanized design-space exploration in Lean 4: each construct of an earlier draft was formalized, attacked with counterexamples, and kept only when the tested alternatives failed for a stated reason. What survived is an environment of named declarations with frozen types, monotone public commitments, and write-once realizations, under which refining one declaration preserves every client; nominal semantic types with a representation binding that licenses construction only inside a declaration whose signature announces the concept; physical dimensions carried in primitive operator types; one temporal primitive that reads a clock domain at its previous activation, of which single-domain delay is a special case, with deterministic evaluation that is total exactly on causal designs; nominal clock domains checked by a judgment rather than a type; and nominal physical outputs with one explicit driver each. Signal and event types, effect rows, action requests, and runtime arbitration were removed. A separate validation layer decides, with a solver proved sound and complete for its finite fragment, whether a design fits a declared microcontroller, and its evidence is kept apart from the evidence that survives refinement. The paper states each result with its claim strength, presents the interaction model and acceptance levels the architecture implies, and gives an evaluation plan; no elaborator, editor, or user study has yet been built.

#v(6pt)
#smallcaps[CCS CONCEPTS]
#text(size: 8.3pt)[Human-centered computing $arrow.r$ User interface programming; Software and its engineering $arrow.r$ Domain specific languages; Theory of computation $arrow.r$ Type theory; Software and its engineering $arrow.r$ Formal language definitions; Applied computing $arrow.r$ Computer-aided design.]

#v(4pt)
#smallcaps[KEYWORDS]
#text(size: 8.3pt)[industrial design, product behavior, executable design intent, type systems, synchronous reactive semantics, clock domains, refinement, mechanized design-space exploration, hardware feasibility, design tools]

#v(8pt)
#line(length: 100%, stroke: 0.45pt)
#v(6pt)

#set text(size: 9pt)
#columns(2, gutter: 0.22in)[
  #include "body.typ"
  #bibliography("references.bib", style: "ieee", title: "References")
]
