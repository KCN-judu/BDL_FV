# A Core Calculus for Signature-First Reactive Design

The core-calculus paper: the kernel of `BDL/Core/` and its metatheory,
written for a programming-languages audience. It presents the calculus
λ_BDL — persistent declarations with a refinement order, nominal concepts
with a construction grant, dimensions in operator types, one temporal
primitive over nominal clock domains, one list recursor, explicit outputs
with a single driver, and composition by renaming — with its typing,
tick-indexed semantics, logical relation, and the mechanized counterexamples
that fixed each choice. Every theorem is cited by its Lean name; Appendix A
indexes them by section.

The paper is derived from Part IV and Appendices A–B of the monograph in
`../monograph/`, which remains the record: where the two differ in wording
the monograph is authoritative, and where either differs from the Lean the
Lean is. The paper covers `Core/`, `Behavior/` and the parts of `Surface/`
that the metatheory needs (the definitional library, polymorphism by
matching, the window buffer); units, provision, realization, the adapter
boundary and hardware validation are named only as they bear on the kernel.

## Files

- `paper.md` — the canonical source. Everything is edited here.
- `main.typ` — the document chrome: a single-column journal-paper layout
  (title block, running heads, numbered sections, numeric references).
- `body.typ` — **generated** from `paper.md` by Pandoc; never edited by hand.
- `BDL_core_calculus.pdf` — **generated** by Typst from `main.typ`.
- `references.bib` — the bibliography.
- `build.sh` — the build.

## Build

```bash
./build.sh
```

The script regenerates `body.typ` from `paper.md` with Pandoc (verified with
3.11), patches the symbol names Pandoc emits for pre-0.13 Typst and sets the
tick index of a turnstile beside it, and compiles `main.typ` with Typst (0.13
or later; verified with 0.15) to the PDF. Without Pandoc the existing
`body.typ` is used; without Typst the script stops after regenerating it.

## Conventions

- Theorem names are Lean identifiers in `KCN-judu/BDL_FV` and never change
  to track the document; a paper theorem number is a presentation device and
  Appendix A maps it to the Lean names and files.
- A result proved for a fragment states the fragment in the theorem; "minimal"
  means minimal among the formalized candidates, never a minimality theorem.
- Math is written in LaTeX in `paper.md` and converted by Pandoc: `\text{}`
  for keywords and constructors, `\mathit{}` for multi-letter variables, one
  `&` per row in an `array` (Typst alternates alignment at each `&`), `{}`
  before a row that begins with `[`.
- The abstract is the first section of `paper.md` (`# Abstract {-}`); the
  title, author and revision line are in `main.typ`.
