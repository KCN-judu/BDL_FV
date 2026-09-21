# BDL_FV — formal-design experiment for a Behavior Design Language kernel

A Lean 4 project that treats the BDL proposal as a _candidate_ specification and
derives, by construction / counterexample / proof, what its kernel actually
needs. No dependencies beyond core Lean.

```bash
lake build
```

- `BDL/` — the development: `Core/` (the kernel), `Validation/` (hardware and
  capacity, outside the kernel), `Behavior/` (components, systems, groups),
  `Surface/` (elaborations proved to preserve the kernel's judgments),
  `Experiments/` (the alternatives tried and the executed cases)
- [`docs/`](docs/README.md) — the records: the kernel in one page, the file map
  and the minimality table; one report per phase; one record per design decision
  (FVD-0001 … FVD-0158); the design notes with production guidance; the open
  items; status and governance
- [`paper/`](paper/README.md) — the two documents. `paper/monograph/` is the BDL
  Design and Formalization Monograph, the living technical record that
  synthesizes the records by concept and pins production to one commit
  (`paper/monograph/paper.md` is canonical; `body.typ` and the PDF are generated
  by `paper/monograph/build.sh`; `paper/monograph/archive/` keeps the 2026-09
  conference manuscript as history). `paper/core_calculus/` is the core-calculus
  paper: the kernel of `BDL/Core/` and its metatheory written for a
  programming-languages audience, with the same pipeline

Status: Phases 0–7, 8a/8b, 9a–9c, 10, 10b, 11, 12, 13, 14, 15, 16, 17, 18, 19,
20, 21 and 22 complete; Phase 8c (surface elaboration of the remaining
designer-facing forms, executable semantics) and the final minimality audit not
started — [docs/project/status.md](docs/project/status.md).

Kernel in one line: `DeclEnv : DeclId → Option DesignDecl`, where a `DesignDecl`
is a stable id, a `DeclInterface` (expected type + monotone public commitments)
and an optional write-once realization; one temporal primitive `sync`, one
recursor `fold`, `rep`/`mk` under a grant, and a tick-indexed evaluation
relation — the rest is construction over designs. The full paragraph:
[docs/kernel/kernel.md](docs/kernel/kernel.md).

Records follow [docs/project/governance.md](docs/project/governance.md):
decisions are `FVD-NNNN`, open items `FVI-NNNN`, each linked to the production
record (`ADR`/`PRP`/`ISS`) it concerns; `just docs-check` validates them,
`just check` also builds.
