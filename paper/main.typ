// BDL paper - ACM-inspired Typst layout.
// Primary editable source: paper.md -> body.typ (generated with Pandoc).
// This file supplies the paper chrome and two-column layout.

#set page(
  paper: "us-letter",
  margin: (top: 0.58in, bottom: 0.62in, left: 0.68in, right: 0.68in),
  numbering: "1",
  number-align: center,
)
#set text(font: "Linux Libertine O", size: 9pt, lang: "en")
#set par(justify: true, leading: 0.52em)
#set heading(numbering: "1.1")
#set enum(indent: 1.15em, body-indent: 0.45em)
#set list(indent: 1.05em, body-indent: 0.45em)
#set raw(font: "DejaVu Sans Mono", size: 7.8pt)

#show heading.where(level: 1): set text(font: "Linux Biolinum O", size: 10.2pt, weight: "bold")
#show heading.where(level: 2): set text(font: "Linux Biolinum O", size: 9.2pt, weight: "bold")
#show heading.where(level: 3): set text(font: "Linux Biolinum O", size: 9pt, weight: "bold", style: "italic")

#let smallcaps(body) = text(font: "Linux Biolinum O", weight: "bold", size: 8.2pt, body)

#align(center)[
  #text(font: "Linux Biolinum O", size: 17pt, weight: "bold")[
    Executable Behavioral Design for Industrial Designers
  ]
  #v(3pt)
  #text(size: 11.2pt, weight: "bold")[
    Signature-First Mappings, Progressive Formalization, and a Typed Kernel for Product Logic
  ]
  #v(7pt)
  #text(size: 9.2pt)[Anonymous Author]
  #linebreak()
  #text(size: 8.3pt, style: "italic")[Research Design Draft]
]

#v(10pt)

#smallcaps[ABSTRACT]
#v(2pt)
#set text(size: 8.5pt)
Industrial products increasingly embed sensing, temporal logic, software, and control, yet industrial designers still lack a behavioral design medium with the immediacy that CAD provides for geometry. Existing prototyping and visual-programming tools reduce implementation cost but often preserve engineering-oriented representations such as state transitions, execution steps, callbacks, or node-level computation. This paper proposes BDL, a Behavior Design Language whose primary artifacts are typed product relationships. A Mapping Block is created first by a semantic type signature, for example $?f: upright("Tilt") arrow.r upright("Brightness")$, and may remain intentionally unresolved while the surrounding design is authored and checked. Formulas, curves, examples, temporal modifiers, hardware bindings, and verification obligations progressively refine the same artifact. BDL separates a designer-facing surface language from a kernel calculus with semantic quantity types, physical dimensions, declared clock domains, signals and events, scoped StateHandlers, deterministic action policies, typed holes, causality analysis, and a synchronous tick semantics. Temporal identity is declared rather than inferred, so that questions about differing update rates are raised while they are still semantic questions rather than at hardware binding. Core type soundness is kept separate from range, timing, and device-feasibility obligations. The paper also derives an interaction model that moves from broad functional intent to mapping detail, temporal/state detail, realization binding, and verification without requiring designers to adopt procedural implementation concepts. The central research hypothesis is that product behavior can become a design material: intuitive at the surface, but precise enough underneath to support early execution and validation.

#v(6pt)
#smallcaps[CCS CONCEPTS]
#text(size: 8.3pt)[Human-centered computing $arrow.r$ User interface programming; Software and its engineering $arrow.r$ Domain specific languages; Theory of computation $arrow.r$ Type theory; Applied computing $arrow.r$ Computer-aided design.]

#v(4pt)
#smallcaps[KEYWORDS]
#text(size: 8.3pt)[industrial design, product behavior, executable design intent, type systems, reactive programming, typed holes, progressive formalization, clock domains, design tools]

#v(8pt)
#line(length: 100%, stroke: 0.45pt)
#v(6pt)

#set text(size: 9pt)
#columns(2, gutter: 0.22in)[
  #include "body.typ"
  #bibliography("references.bib", style: "ieee", title: "References")
]
