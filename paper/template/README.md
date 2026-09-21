# The paper template

The layout conventions every paper under `paper/` is generated with, in the
style of PACMPL (`acmsmall`): single column, Libertinus Serif 10 pt, numbered
sections, running heads, theorem and proof environments, numeric references.

- `env.typ` — the environments: `#thm(kind, num)[name][body]` (small-caps
  head, italic body), `#proof[body]` (tombstone on the last line),
  `#figcaption[body]`.
- `postprocess.py` — turns Pandoc's `body.typ` into those environments and
  fixes letter-spaced math words (`sans(s o m e)` → `sans("some")`).

Each paper's `build.sh` copies both files beside its `main.typ` (so that a
mirror of one paper directory builds alone), runs Pandoc, then the
post-processor, then Typst. Edit the template here, never the copies.

## What the Markdown must look like

- A result: a paragraph starting `**Theorem 3 (Name; \`lean_name\`).**`
  followed by the statement — also `Proposition`, `Lemma`, `Corollary`, and
  `Definition (Name).`, `Remark (Name).` and `Example (Name).` without a number.
- Its proof: the next paragraph, `*Proof.* …` ending with `$\square$`.
- A figure caption: an italic paragraph `*Figure 1. …*` after the display.
- Math keywords in `\mathsf{…}` (constructors, named judgments), sets and
  functions in `\mathrm{…}`, metavariables bound once in a *Notation*
  paragraph after the syntax figure (`paper/core_calculus/paper.md` §3.1).

Writing follows Krantz, *A Primer of Mathematical Writing* (arXiv
1612.04888): every statement self-contained with its hypotheses, a proof that
names its method and its steps before carrying them out, notation introduced
once and never rebound, words for the logic of the prose and symbols for the
objects, and no sentence that begins with a symbol.
