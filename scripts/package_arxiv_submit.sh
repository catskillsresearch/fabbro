#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

TEX="arxiv.tex"
CMU_STYLE="cmu-titlepage2.sty"
LISTINGS_DIR="lean-listings"
OUT_DIR="dist"
ZIP="${OUT_DIR}/arxiv_submit.zip"

if [[ "${1:-}" != "--skip-tex-build" ]]; then
  bash scripts/build_arxiv_tex.sh
fi

missing=0
for f in "$TEX" "$CMU_STYLE"; do
  if [[ ! -f "$f" ]]; then
    echo "error: missing $f" >&2
    missing=1
  fi
done
if [[ ! -d "$LISTINGS_DIR" ]] || [[ -z "$(find "$LISTINGS_DIR" -maxdepth 1 -type f 2>/dev/null)" ]]; then
  echo "error: missing listings in $LISTINGS_DIR" >&2
  missing=1
fi
if [[ "$missing" -ne 0 ]]; then
  exit 1
fi

mkdir -p "$OUT_DIR"
rm -f "$ZIP"

python3 - <<'PY'
import json
from pathlib import Path

sources = [
    {"filename": "arxiv.tex", "usage": "toplevel"},
    {"filename": "cmu-titlepage2.sty", "usage": "include"},
]
for path in sorted(p for p in Path("lean-listings").iterdir() if p.is_file()):
    sources.append({"filename": path.as_posix(), "usage": "include"})
Path("00README.json").write_text(json.dumps({"process": {"compiler": "pdflatex"}, "sources": sources}, indent=2) + "\n")
print(f"  {len(sources)} sources")
PY

zip -r "$ZIP" 00README.json "$TEX" "$CMU_STYLE" "$LISTINGS_DIR"
echo "wrote $ZIP ($(du -h "$ZIP" | cut -f1))"
