# BDL ACM-style Typst project

This project is an ACM-inspired two-column research-paper layout written for Typst.

## Files

- `main.typ` - paper layout, title block, abstract, CCS concepts, keywords, and bibliography.
- `body.typ` - generated Typst body used by `main.typ`.
- `paper.md` - canonical prose source used to regenerate both Typst and the PDF fallback build.
- `references.bib` - bibliography.
- `assets/` - paper figures.
- `build.sh` - regenerates `body.typ` from `paper.md`, then compiles with Typst if `typst` is installed.

## Build

```bash
./build.sh
```

The script runs:

```bash
pandoc paper.md -f markdown -t typst -o body.typ
typst compile main.typ BDL_behavior_design_language.pdf
```

`paper.md` is the single source for the body; never edit `body.typ` by hand — run `./build.sh` (needs pandoc, verified with 3.11) to regenerate it. Typst 0.13+ is required (verified with 0.15). The project does not depend on external Typst packages; fonts fall back to the bundled Libertinus family. `build.sh` patches the symbol names pandoc emits (`bracket.l.double`, `angle.l`, `gt.tri`, …) to their current Typst names after regenerating `body.typ`.

`BDL_behavior_design_language.pdf` in this directory is the Typst rendering. An earlier draft was distributed as an ACM `acmart` rendering of the same `paper.md`; that pipeline is not part of this repository.
