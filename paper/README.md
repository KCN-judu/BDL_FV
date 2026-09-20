# The BDL papers

Two documents, each with its own canonical Markdown source and the same
build pipeline (Pandoc → `body.typ` → Typst → PDF; `build.sh` in each
directory). The Lean sources under `../BDL/` are the authority for every
formal claim in either; the records under `../docs/` are their record.

| Directory                          | Document                                                                                                                                                                                                                                                                                 |
| ---------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| [`monograph/`](monograph/README.md) | _The BDL Design and Formalization Monograph_ — the living technical record: the design problem, the architecture, one product through the lifecycle, the derived formal model, the toolchain, Studio, the evidence and the open agenda, with the reference apparatus in its appendices |
| [`core_calculus/`](core_calculus/README.md) | _A Core Calculus for Signature-First Reactive Design_ — the kernel of `BDL/Core/` and its metatheory written as a programming-languages paper: syntax, typing, the tick-indexed semantics, clock domains, outputs, composition, and the mechanization                                  |

Where the two differ in wording, the monograph is the record and the paper
is a presentation of its formal part; where either differs from the Lean, the
Lean is right and the document is to be corrected. Theorem names in both are
Lean identifiers and never change to track a document.

## Build

```bash
./monograph/build.sh
./core_calculus/build.sh
```

Each script regenerates `body.typ` from its `paper.md` with Pandoc (verified
with 3.11), patches the symbol names Pandoc emits for pre-0.13 Typst, and
compiles `main.typ` with Typst (0.13 or later; verified with 0.15) to the PDF.
`body.typ` is generated and never edited by hand.
