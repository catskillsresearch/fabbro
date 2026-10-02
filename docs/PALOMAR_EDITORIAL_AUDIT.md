# Palomar editorial audit (fabbro surfaces — local dry-run only)

Fabbro packages **one Palomar-style Challenge / Solution surface per course**
under `surfaces/CourseXXXXX/`. These surfaces exist so you can run the same
mechanical (and optionally editorial) Palomar preflight toolkit used by
[`scott1964`](https://github.com/catskillsresearch/scott1964) **locally and in
CI**.

## Not a registry submission

**Fabbro surfaces are not submitted to the Palomar registry.** They are
curriculum packaging for preflight-for-fun / regression. The Scott 1964 paper
surface (`scott1964`) is the standalone registry submission. Each surface
`PROVENANCE.md` and `formalization.yaml` state this explicitly.

Do not treat a green fabbro surface preflight as authorization to register
that course package with Palomar.

## Full preflight (optional, local)

```bash
# CURSOR_API_KEY in env, or in ../tokens_ssto.yaml (shared with sibling repos)
bash scripts/palomar_preflight.sh
```

Runs mechanical Comparator checks for **every** `surfaces/Course*/` directory,
then (unless `--mechanical-only`) policy sync and LLM editorial audit via the
shared toolkit in `../palomar-preflight`.

Toolkit pin: `vendor/PALOMAR_PREFLIGHT_PIN`
(`de7e8b926342c75358801c609efd1296af4ed412`).

## Mechanical-only (CI / day-to-day)

```bash
bash scripts/palomar_preflight.sh --mechanical-only

# or one surface
bash scripts/palomar_preflight_one.sh surfaces/Course21127 --mechanical-only
```

GitHub Actions uses mechanical-only after `lake build` of the root project.

## Packaging checklist (local only)

1. Compared theorems are the course headline results listed in each
   `comparator.json`.
2. Challenge definitions are sorry-free; only compared theorem *proofs* use
   `sorry`.
3. `formalization.yaml` `main_results` match `comparator.json` `theorem_names`.
4. `Solution.lean` only imports the course development (no new proofs).
5. Mechanical green: `bash scripts/palomar_preflight_one.sh surfaces/CourseXXXXX --mechanical-only`.

Again: green preflight here means the curriculum surface typechecks and
matches Challenge/Solution — **not** that the package should be registered.
