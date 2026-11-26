#!/usr/bin/env bash
# Typeset the manuscript and its one-page introduction from the tracked sources.
set -euo pipefail
cd "$(dirname "$0")/.."
output=dist/paper-build
mkdir -p "$output"
# Use the manuscript date (2026-11-26 UTC) for reproducible PDF metadata.
export SOURCE_DATE_EPOCH=1795651200 FORCE_SOURCE_DATE=1 TZ=UTC
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir="$output" \
  paper/boolean-scott-spectral-gaps.tex
pandoc RESULT.md --from=markdown --pdf-engine=pdflatex \
  -V papersize=letter -V geometry:margin=0.92in -V fontsize=12pt \
  -V colorlinks=true -V urlcolor=blue!55!black \
  -M 'title-meta=How hard is it to describe one Boolean algebra?' \
  -M 'author-meta=GPT 6.2 Astra (Codex) with Serafim Batzoglou' \
  -o "$output/result-in-one-page.pdf"
