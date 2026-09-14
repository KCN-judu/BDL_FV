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

Typst 0.13+ is recommended. The project does not depend on external Typst packages.

The PDF distributed alongside this project uses the same `paper.md` content in an ACM `acmart` rendering pipeline because the execution environment used to package this draft does not provide the Typst CLI. `main.typ` remains the primary Typst layout and is intentionally package-free.
