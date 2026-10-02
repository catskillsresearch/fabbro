#!/usr/bin/env bash
# Run Palomar preflight for ALL fabbro course surfaces under surfaces/Course*/.
# Preflight only — fabbro surfaces are NOT submitted to the Palomar registry.
#
# Usage:
#   bash scripts/palomar_preflight.sh --mechanical-only
#   bash scripts/palomar_preflight.sh            # full (needs CURSOR_API_KEY for editorial)
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
ONE="$ROOT/scripts/palomar_preflight_one.sh"

shopt -s nullglob
surfaces=("$ROOT"/surfaces/Course*)
if [[ ${#surfaces[@]} -eq 0 ]]; then
  echo "error: no surfaces/Course* directories found" >&2
  exit 1
fi

echo "Fabbro Palomar preflight: ${#surfaces[@]} surfaces (local/CI only; not a registry submission)"
fail=0
for d in "${surfaces[@]}"; do
  name="$(basename "$d")"
  echo "======== $name ========"
  if ! bash "$ONE" "$d" "$@"; then
    echo "FAILED: $name" >&2
    fail=1
  fi
done

if [[ "$fail" -ne 0 ]]; then
  echo "error: one or more surface preflights failed" >&2
  exit 1
fi
echo "All surface preflights completed."
