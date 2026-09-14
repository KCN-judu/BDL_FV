#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
pandoc paper.md -f markdown -t typst -o body.typ
if ! command -v typst >/dev/null 2>&1; then
  echo "typst CLI not found. body.typ regenerated; install Typst 0.13+ to compile main.typ." >&2
  exit 2
fi
typst compile main.typ BDL_behavior_design_language.pdf
