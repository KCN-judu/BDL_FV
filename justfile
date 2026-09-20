# BDL_FV task runner.  `just` lists recipes.

set shell := ["zsh", "-cu"]

prettier     := "npx --yes prettier@3.9.7"
markdownlint := "npx --yes markdownlint-cli2@0.23.2"

default:
    @just --list

# ---- Lean -----------------------------------------------------------------

build:
    lake build

# ---- Records (docs/project/governance.md) ---------------------------------

# Format every tracked Markdown file: Prettier for layout, bare fences
# labelled `text`, then markdownlint's own fixes.  Never lay out by hand.
docs-fmt:
    git ls-files -z '*.md' | xargs -0 {{prettier}} --log-level warn --write
    git ls-files -z '*.md' ':!paper/**' | xargs -0 python3 scripts/md_normalize.py
    git ls-files -z '*.md' | xargs -0 {{markdownlint}} --fix

# Report Markdown that `just docs-fmt` would change or that breaks a rule.
docs-lint:
    git ls-files -z '*.md' | xargs -0 {{prettier}} --log-level warn --check
    git ls-files -z '*.md' | xargs -0 {{markdownlint}}

# Lint plus the record validator: ids, statuses, frontmatter, index
# coverage, supersession in both directions, resolved items, links.
docs-check: docs-lint
    python3 scripts/validate_docs.py

# Everything CI would run.
check: build docs-check
