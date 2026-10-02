# Palomar surfaces (one per course)

Each subdirectory under `surfaces/` is a **Palomar-style Challenge / Solution
package** for one BS-in-Measurement-Theory course capstone.

```
surfaces/CourseXXXXX/
  Challenge.lean      # Mathlib-only holes (sorry on compared theorems only)
  Solution.lean       # imports BSinMeasurementTheory.CourseXXXXX
  comparator.json
  formalization.yaml
  PROVENANCE.md
  lakefile.toml
  lean-toolchain      # → ../../lean-toolchain
```

## Important: preflight only

These surfaces exist so you can run **local / CI mechanical Palomar preflight**
for fun and regression. They are **not** submitted to the Palomar registry.
The Scott 1964 paper surface [`scott1964`](https://github.com/catskillsresearch/scott1964)
is the registry submission; fabbro is the curriculum packaging.

## How to build one surface

```bash
# Share the root mathlib cache (avoids duplicating ~7GB per surface)
mkdir -p surfaces/Course21127/.lake
ln -sfn "$(pwd)/.lake/packages" surfaces/Course21127/.lake/packages

cd surfaces/Course21127
lake build Challenge Solution
```

Committed `lake-manifest.json` files pin the same mathlib rev as the fabbro root.
After a root `lake exe cache get` / `lake build`, symlink `.lake/packages` as above
before building surfaces.

## How to run mechanical preflight

From the fabbro root (requires sibling `../palomar-preflight` or
`PALOMAR_PREFLIGHT_ROOT`):

```bash
# all surfaces
bash scripts/palomar_preflight.sh --mechanical-only

# one surface
bash scripts/palomar_preflight_one.sh surfaces/Course21127 --mechanical-only
```

Equivalent loop:

```bash
for d in surfaces/Course*; do
  bash scripts/palomar_preflight_one.sh "$d" --mechanical-only
done
```

See `docs/PALOMAR_EDITORIAL_AUDIT.md` for full vs mechanical preflight notes.
