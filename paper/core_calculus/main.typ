// A Core Calculus for Signature-First Reactive Design — Typst layout.
// Primary editable source: paper.md -> body.typ (generated with Pandoc via build.sh).
// This file supplies the document chrome: a single-column journal-paper layout
// in the style of the PACMPL / acmsmall format (title block, abstract inside
// the body, numbered sections, running heads, IEEE-style numeric references).

#set page(
  paper: "us-letter",
  margin: (top: 1.0in, bottom: 1.0in, left: 1.05in, right: 1.05in),
  numbering: "1",
  number-align: center,
  header: context {
    let p = counter(page).get().first()
    if p > 1 [
      #set text(size: 8pt, fill: luma(80))
      #if calc.even(p) [#h(1fr) ZHU Zhehao] else [A Core Calculus for Signature-First Reactive Design #h(1fr)]
    ]
  },
)
#set text(font: "Libertinus Serif", size: 10pt, lang: "en")
#set par(justify: true, leading: 0.58em, first-line-indent: 1.1em)
#set heading(numbering: "1.1")
#set enum(indent: 1.0em, body-indent: 0.5em)
#set list(indent: 0.9em, body-indent: 0.5em)
#set math.equation(numbering: none)
#show math.equation.where(block: true): set block(above: 0.9em, below: 0.9em)
#show raw: set text(font: "DejaVu Sans Mono", size: 0.86em)
#show raw.where(block: true): set block(inset: (x: 0.6em, y: 0.5em), fill: luma(248), width: 100%, radius: 2pt)
#show table: set text(size: 8.4pt)
#show table.cell: set align(left + top)
#show table.cell: set par(justify: false, first-line-indent: 0em)
#show table.cell.where(y: 0): set text(weight: "bold")
#set table(inset: (x: 4pt, y: 3pt), stroke: (x: none, y: 0.3pt))
#show figure.where(kind: table): set block(breakable: true)
#show figure.where(kind: table): set figure(placement: none)
#show table.cell: it => box(width: 100%, it)
#show raw.where(block: false): it => {
  show regex("[_./:]"): m => m.text + sym.zws
  it
}
#show link: set text(fill: rgb("#1a3d7c"))

// Headings: journal style, no page breaks, small caps-like weight.
#show heading.where(level: 1): it => {
  v(10pt)
  set text(size: 12pt, weight: "bold")
  block(it)
  v(3pt)
}
#show heading.where(level: 2): it => {
  v(6pt)
  set text(size: 10.5pt, weight: "bold")
  block(it)
  v(2pt)
}
#show heading.where(level: 3): it => {
  v(4pt)
  set text(size: 10pt, weight: "bold", style: "italic")
  block(it)
  v(1pt)
}
// Unnumbered front-matter and back-matter headings keep the same look.
#show heading.where(numbering: none): set text(weight: "bold")

// ---------------------------------------------------------------- title block
#align(left)[
  #v(0.2in)
  #text(size: 19pt, weight: "bold")[
    A Core Calculus for Signature-First Reactive Design
  ]
  #v(4pt)
  #text(size: 12.5pt)[
    Typed Semantic Relationships Before Their Realization
  ]
  #v(12pt)
  #text(size: 11pt)[ZHU ZHEHAO]
  #v(2pt)
  #text(size: 9.5pt, style: "italic")[
    Formal development `KCN-judu/BDL_FV` (Lean 4.33.1, through Phase 18); paper revision of 2026-09-20
  ]
  #v(10pt)
]

#include "body.typ"

#set par(first-line-indent: 0em)
#bibliography("references.bib", style: "ieee", title: "References")
