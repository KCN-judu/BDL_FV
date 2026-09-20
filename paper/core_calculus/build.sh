#!/usr/bin/env bash
# Regenerate body.typ from paper.md (pandoc), patch symbol names for Typst >= 0.13,
# and compile main.typ. Run from anywhere.
set -euo pipefail
cd "$(dirname "$0")"
if command -v pandoc >/dev/null 2>&1; then
  pandoc paper.md -f markdown -t typst -o body.typ
  # pandoc emits pre-0.13 symbol names; map them to current Typst names, and
  # keep the tick index of a turnstile beside it (Typst would set it below).
  sed -i '' \
    -e 's/bracket\.l\.double/bracket.l.stroked/g' \
    -e 's/bracket\.r\.double/bracket.r.stroked/g' \
    -e 's/angle\.l/chevron.l/g' \
    -e 's/angle\.r/chevron.r/g' \
    -e 's/gt\.tri/gt.closed/g' \
    -e 's/tack\.r\([_^]\)/scripts(tack.r)\1/g' \
    body.typ
else
  echo "pandoc not found; using existing body.typ" >&2
fi
if ! command -v typst >/dev/null 2>&1; then
  echo "typst CLI not found; install Typst 0.13+ to compile main.typ." >&2
  exit 2
fi
typst compile main.typ BDL_core_calculus.pdf
