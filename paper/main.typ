// BDL Design and Formalization Monograph - Typst layout.
// Primary editable source: paper.md -> body.typ (generated with Pandoc via build.sh).
// This file supplies the document chrome and a single-column monograph layout.

#set page(
  paper: "us-letter",
  margin: (top: 0.9in, bottom: 0.9in, left: 1.0in, right: 1.0in),
  numbering: "1",
  number-align: center,
)
#set text(font: "Libertinus Serif", size: 10pt, lang: "en")
#set par(justify: true, leading: 0.6em)
#set heading(numbering: none)
#set enum(indent: 1.15em, body-indent: 0.5em)
#set list(indent: 1.05em, body-indent: 0.5em)
#show raw: set text(font: "DejaVu Sans Mono", size: 0.88em)
#show table: set text(size: 8.6pt)
#show table.cell: set align(left + top)
#show table.cell: set par(justify: false)
#show table.cell.where(y: 0): set text(weight: "bold")
#set table(inset: (x: 4pt, y: 3pt), stroke: (x: none, y: 0.3pt))

#show heading.where(level: 1): it => {
  pagebreak(weak: true)
  v(6pt)
  set text(font: "Libertinus Serif", size: 15pt, weight: "bold")
  it
  v(6pt)
}
#show heading.where(level: 2): set text(font: "Libertinus Serif", size: 11.5pt, weight: "bold")
#show heading.where(level: 3): set text(font: "Libertinus Serif", size: 10.2pt, weight: "bold", style: "italic")

// ---------------------------------------------------------------- title page
#align(center)[
  #v(2.2in)
  #text(font: "Libertinus Serif", size: 24pt, weight: "bold")[
    BDL Design and Formalization Monograph
  ]
  #v(10pt)
  #text(size: 13pt)[
    A Behavior Design Language for Industrial Designers: \
    Motivation, Mechanically Derived Kernel, Production Toolchain, \
    Correspondence, Rejected Alternatives and Open Agenda
  ]
  #v(24pt)
  #text(size: 11pt)[ZHU ZHEHAO]
  #v(6pt)
  #text(size: 9.5pt, style: "italic")[Living technical record — revision of 2026-09-18]
  #v(4pt)
  #text(size: 9pt)[
    Formal development `KCN-judu/BDL_FV` at `3b4f11b` · production `KCN-judu/BDL` at `f1ce82c`
  ]
  #v(1.6in)
  #block(width: 88%)[
    #set par(justify: true)
    #set text(size: 9.3pt)
    This document is the authoritative narrative record of BDL. It is not a paper and is not written to a page limit; it records what the language is, why each construct exists or was rejected, which theorem or executed example supports each claim, how production implements it, where production deviates from the formal model, and what remains open. Every claim carries a strength label (formally proved, executable example, informed by FV, production-tested, design recommendation). No usability claim in it has been tested with users.
  ]
]

#pagebreak()

// ---------------------------------------------------------------- contents
#outline(title: [Contents], indent: 1.2em, depth: 2)

#pagebreak()

#include "body.typ"
#bibliography("references.bib", style: "ieee", title: "References")
