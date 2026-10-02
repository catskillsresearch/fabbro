#!/usr/bin/env bash
# Thin wrapper: run Palomar preflight for one fabbro surface directory.
# Usage: bash scripts/palomar_preflight_one.sh surfaces/CourseXXXXX [--mechanical-only ...]
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"

if [[ $# -lt 1 ]]; then
  echo "usage: $0 surfaces/CourseXXXXX [preflight-args...]" >&2
  exit 2
fi

SURFACE_ARG="$1"
shift
SURFACE="$(cd "$ROOT" && cd "$SURFACE_ARG" && pwd)"

find_toolkit() {
  local root="$1" d
  for d in \
    "${PALOMAR_PREFLIGHT_ROOT:-}" \
    "$(dirname "$root")/palomar-preflight" \
    "$root/palomar-preflight"; do
    [[ -n "$d" && -f "$d/palomar_preflight.sh" ]] && {
      cd "$d" && pwd
      return 0
    }
  done
  echo "error: palomar-preflight not found; set PALOMAR_PREFLIGHT_ROOT or checkout toolkit" >&2
  return 1
}

toolkit_supports_cli() {
  bash "$1/palomar_preflight.sh" --help 2>&1 | grep -q -- '--project-root'
}

# Longest-prefix-first: overlapping namespaces (Course21120 vs Course21120FTC)
# otherwise falsely match the shorter prefix and break pretty-print closure.
patch_compare_prefix_order() {
  local compare="$1/compare_challenge_solution_types.sh"
  [[ -f "$compare" ]] || return 0
  if grep -q 'sorted(prefixes))' "$compare" && ! grep -q 'key=len, reverse=True' "$compare"; then
    sed -i 's/sorted(prefixes)/sorted(prefixes, key=len, reverse=True)/g' "$compare"
    echo "note: patched $compare for longest-prefix namespace matching" >&2
  fi
}

TOOLKIT="$(find_toolkit "$ROOT")"
patch_compare_prefix_order "$TOOLKIT"

# Challenge.lean may contain deliberate sorry; Solution.lean must be sorry-free.
# Course proofs live in the path dependency (fabbro root) and are scanned separately
# by the root build; for the surface package scan Solution.lean only.
SORRY_PATHS="Solution.lean"

if toolkit_supports_cli "$TOOLKIT"; then
  exec bash "$TOOLKIT/palomar_preflight.sh" \
    --project-root "$SURFACE" \
    --sorry-paths "$SORRY_PATHS" \
    "$@"
fi

export PALOMAR_PROJECT_ROOT="$SURFACE"
export PALOMAR_SORRY_PATHS="$SORRY_PATHS"
exec bash "$TOOLKIT/palomar_preflight.sh" "$@"
