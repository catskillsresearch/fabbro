#!/usr/bin/env bash
# Regenerate arxiv.tex, compile arxiv.pdf, and dist/arxiv_submit.zip.
set -euo pipefail
cd "$(dirname "$0")/.."

TEX="arxiv.tex"
PDF="arxiv.pdf"

echo "==> Regenerating arxiv.tex + lean-listings/ + figures/"
bash scripts/build_arxiv_tex.sh

echo "==> Compiling PDF (pdfLaTeX via latexmk)"
latexmk -C "$TEX" >/dev/null 2>&1 || true
rm -f arxiv.aux arxiv.out arxiv.toc arxiv.lof
latexmk -pdf \
  -pdflatex="pdflatex -interaction=nonstopmode -halt-on-error" \
  -interaction=nonstopmode \
  -halt-on-error \
  "$TEX" || {
  echo "latexmk reported errors; tail of log:" >&2
  tail -n 60 arxiv.log >&2 || true
  exit 1
}

echo "wrote $PDF ($(du -h "$PDF" | cut -f1))"

echo "==> Packaging arXiv submission zip"
bash scripts/package_arxiv_submit.sh --skip-tex-build
