---
kind: report
phase: 0
area: core
date: 2026-09-14
status: current
---

# Phase 0 — a single persistent declaration

Conclusions carried forward unchanged (Phase-0 vocabulary translated):

1. A persistent design declaration is a stable name + a fixed expected type
   - a monotonically growing commitment set + a write-once realization. The
     lifecycle closure is exactly this preorder (`DeclRefinesStar_iff`).
2. Strengthening the interface of a realized declaration must re-verify the
   realization (`DeclRefines.strengthen` carries the premise;
   `naive_breaks_wellformedness`).
3. Identity alone contributes nothing beyond a declaration name to the
   single-declaration theorems.
4. Theorem 4 (`preserves_wellFormed`) has no independent content: its hypothesis
   is unused because the invariant was moved into the definition. This is
   reported, not hidden (`DeclRefines.wellFormed_target`).
