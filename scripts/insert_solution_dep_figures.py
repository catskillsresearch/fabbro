#!/usr/bin/env python3
"""Insert a Mermaid dependency figure under each course Solution heading.

Mathlib lives in an amber box; solution modules live in a blue box.
"""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

COURSE_LEANS: list[tuple[str, str, list[str]]] = [
    ("21-120-21-122.md", "21-120 / 21-122", [
        "BSinMeasurementTheory/Course21120FTC.lean",
        "BSinMeasurementTheory/Course21120.lean",
        "BSinMeasurementTheory/Course21120Taylor.lean",
    ]),
    ("21-127.md", "21-127", ["BSinMeasurementTheory/Course21127.lean"]),
    ("21-241.md", "21-241", ["BSinMeasurementTheory/Course21241.lean"]),
    ("21-228.md", "21-228", ["BSinMeasurementTheory/Course21228.lean"]),
    ("21-355.md", "21-355", ["BSinMeasurementTheory/Course21355.lean"]),
    ("21-373.md", "21-373", [
        "BSinMeasurementTheory/Course21373.lean",
        "BSinMeasurementTheory/Course21373Numerical.lean",
    ]),
    ("21-321.md", "21-321", ["BSinMeasurementTheory/Course21321.lean"]),
    ("21-292.md", "21-292", [
        "BSinMeasurementTheory/Course21292.lean",
        "BSinMeasurementTheory/Course21292Numerical.lean",
    ]),
    ("21-329.md", "21-329", ["BSinMeasurementTheory/Course21329.lean"]),
    ("21-651.md", "21-651", ["BSinMeasurementTheory/Course21651.lean"]),
    ("21-720.md", "21-720", ["BSinMeasurementTheory/Course21720.lean"]),
    ("21-640.md", "21-640", ["BSinMeasurementTheory/Course21640.lean"]),
    ("21-410-21-599.md", "21-410 / 21-599", ["BSinMeasurementTheory/Course21410.lean"]),
    ("21-322.md", "21-322", ["BSinMeasurementTheory/Course21322.lean"]),
]

IMPORT_RE = re.compile(r"^import\s+(\S+)\s*$", re.MULTILINE)
MARKER_RE = re.compile(
    r"\n?<!-- lean-dep-figure -->.*?<!-- /lean-dep-figure -->\n?",
    re.DOTALL,
)

MATHLIB_HINTS: list[tuple[re.Pattern[str], str]] = [
    (re.compile(r"\bHasDerivAt\b|\bDifferentiableAt\b|\bderiv\b"), "Analysis.Calculus.Deriv"),
    (re.compile(r"\bintegral\b|intervalIntegral|integral_inv"), "MeasureTheory.Integral.IntervalIntegral"),
    (re.compile(r"\barctan\b"), "Analysis.SpecialFunctions.Arctan"),
    (re.compile(r"\bsin\b|\bcos\b|continuous_sin|abs_sin"), "Analysis.SpecialFunctions.Trigonometric"),
    (re.compile(r"\bIsCompact\b|isCompact_Icc"), "Topology.Compactness.Compact"),
    (re.compile(r"\bTendsto\b|\batTop\b|\b𝓝\b|Filter\."), "Order.Filter.Basic"),
    (re.compile(r"\blimsup\b|\bliminf\b|ciSup|ciInf|tailSup|tailInf"), "Order.LiminfLimsup"),
    (re.compile(r"\bBooleanAlgebra\b"), "Order.BooleanAlgebra"),
    (re.compile(r"\bLattice\b|\bBoundedOrder\b"), "Order.BoundedOrder"),
    (re.compile(r"\bZorn\b|zorn"), "Order.Zorn"),
    (re.compile(r"\bCardinal\b"), "SetTheory.Cardinal.Basic"),
    (re.compile(r"\bLinearMap\b|→ₗ"), "Algebra.Module.LinearMap.Basic"),
    (re.compile(r"\bNormedSpace\b|\bNormedAddCommGroup\b|‖"), "Analysis.NormedSpace.Basic"),
    (re.compile(r"\bAddCommGroup\b|\bModule ℝ\b|SublinearFunctional"), "Algebra.Module.Basic"),
    (re.compile(r"\binner\b|\bInnerProductSpace\b"), "Analysis.InnerProductSpace.Basic"),
    (re.compile(r"\bBasis\b"), "LinearAlgebra.Basis.Basic"),
    (re.compile(r"\bPerm\b"), "Data.Fintype.Perm"),
    (re.compile(r"\bFintype\b"), "Data.Fintype.Basic"),
    (re.compile(r"\bFinset\b|∑ |BigOperators"), "Algebra.BigOperators.Group.Finset.Basic"),
    (re.compile(r"\bQuotient\b|\bSetoid\b|\bEquiv\b"), "Data.Setoid.Basic"),
    (re.compile(r"\bWellFounded\b|\bAcc\b|well.?order", re.I), "Order.WellFounded"),
    (re.compile(r"\bℚ\b|\bRat\b"), "Data.Rat.Defs"),
    (re.compile(r"\bℤ\b"), "Data.Int.Basic"),
    (re.compile(r"\bℝ\b"), "Data.Real.Basic"),
    (re.compile(r"\bContinuousMap\b|\bC\("), "Topology.ContinuousMap.Basic"),
    (re.compile(r"\bIsClosed\b|\bIsOpen\b|\bContinuous\b"), "Topology.Basic"),
    (re.compile(r"\bIsAtom\b|IsBooleanAtom"), "Order.Atoms"),
    (re.compile(r"linarith|nlinarith"), "Tactic.Linarith"),
    (re.compile(r"\bnorm_num\b"), "Tactic.NormNum"),
]


def is_import_only(code: str) -> bool:
    lines = [
        ln.strip()
        for ln in code.splitlines()
        if ln.strip() and not ln.strip().startswith("--")
    ]
    return bool(lines) and all(ln.startswith("import ") for ln in lines)


def course_files(seeds: list[str]) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()

    def add(rel: str) -> None:
        if rel not in seen and (ROOT / rel).is_file():
            seen.add(rel)
            out.append(rel)

    for rel in seeds:
        add(rel)
        path = ROOT / rel
        sibling = path.with_suffix("") if path.suffix == ".lean" else path
        if sibling.is_dir():
            for child in sorted(sibling.rglob("*.lean")):
                add(child.relative_to(ROOT).as_posix())
    return out


def parse_imports(code: str) -> list[str]:
    return IMPORT_RE.findall(code)


def infer_mathlib(code: str) -> list[str]:
    found: list[str] = []
    seen: set[str] = set()
    for pat, mod in MATHLIB_HINTS:
        if pat.search(code) and mod not in seen:
            seen.add(mod)
            found.append(mod)
    return found


def module_label(rel: str) -> str:
    name = Path(rel).stem
    if name.startswith("Course") and name[-3:].isdigit():
        return name
    for prefix in (
        "Course21120",
        "Course21127",
        "Course21228",
        "Course21241",
        "Course21292",
        "Course21321",
        "Course21322",
        "Course21329",
        "Course21355",
        "Course21373",
        "Course21410",
        "Course21640",
        "Course21651",
        "Course21720",
    ):
        if name.startswith(prefix):
            rest = name[len(prefix) :]
            return rest or name
    return name


def sid(prefix: str, name: str) -> str:
    return prefix + re.sub(r"[^A-Za-z0-9]", "", name)


def lean_path(imp: str) -> str | None:
    if not imp.startswith("BSinMeasurementTheory."):
        return None
    return imp.replace(".", "/") + ".lean"


def mathlib_names(code: str) -> list[str]:
    imports = [imp for imp in parse_imports(code) if imp.startswith("Mathlib")]
    if imports == ["Mathlib"]:
        return infer_mathlib(code)
    if not imports:
        return [] if is_import_only(code) else infer_mathlib(code)
    return [imp.removeprefix("Mathlib.") for imp in imports]


def ancestors(node: str, preds: dict[str, set[str]]) -> set[str]:
    seen: set[str] = set()
    stack = list(preds.get(node, ()))
    while stack:
        parent = stack.pop()
        if parent in seen:
            continue
        seen.add(parent)
        stack.extend(preds.get(parent, ()))
    return seen


def mermaid_for(rels: list[str]) -> str:
    files = {rel: (ROOT / rel).read_text(encoding="utf-8") for rel in rels}
    displayed = [rel for rel, code in files.items() if not is_import_only(code)]
    if not displayed:
        displayed = list(files)

    preds: dict[str, set[str]] = {rel: set() for rel in files}
    mathlib_of: dict[str, set[str]] = {}
    for rel, code in files.items():
        mathlib_of[rel] = set(mathlib_names(code))
        for imp in parse_imports(code):
            dest = lean_path(imp)
            if dest in files:
                preds[rel].add(dest)

    mathlib_ids = {
        ml: sid("L", ml)
        for rel in displayed
        for ml in mathlib_of[rel]
    }
    module_ids = {rel: sid("M", Path(rel).stem) for rel in displayed}

    edges: list[tuple[str, str]] = []
    for rel in displayed:
        mid = module_ids[rel]
        inherited = set()
        for anc in ancestors(rel, preds):
            inherited |= mathlib_of.get(anc, set())
        for ml in mathlib_of[rel]:
            if ml not in inherited:
                edges.append((mathlib_ids[ml], mid))
        for dest in preds[rel]:
            if dest in module_ids:
                edges.append((module_ids[dest], mid))

    lines = [
        "%%{init: {\"flowchart\": {\"htmlLabels\": false, \"nodeSpacing\": 16, \"rankSpacing\": 36}}}%%",
        "flowchart LR",
        "  classDef course fill:#dbeafe,stroke:#1d4ed8,color:#1e3a8a,stroke-width:1.2px",
        "  classDef mathlib fill:#ffedd5,stroke:#c2410c,color:#7c2d12,stroke-width:1.2px",
        "",
        "  subgraph ML[\"Mathlib\"]",
        "    direction TB",
        "    style ML fill:#fff7ed,stroke:#c2410c,stroke-width:2px",
    ]
    for ml, lid in sorted(mathlib_ids.items(), key=lambda kv: kv[0].lower()):
        lines.append(f"    {lid}[\"{ml}\"]:::mathlib")
    lines += [
        "  end",
        "",
        "  subgraph SOL[\"Solution modules\"]",
        "    direction TB",
        "    style SOL fill:#eff6ff,stroke:#1d4ed8,stroke-width:2px",
    ]
    for rel in displayed:
        lines.append(f"    {module_ids[rel]}[\"{module_label(rel)}\"]:::course")
    lines.append("  end")
    lines.append("")
    seen_e: set[tuple[str, str]] = set()
    known = set(mathlib_ids.values()) | set(module_ids.values())
    for src, dst in edges:
        if src == dst or (src, dst) in seen_e or src not in known or dst not in known:
            continue
        seen_e.add((src, dst))
        lines.append(f"  {src} --> {dst}")
    return "\n".join(lines) + "\n"


def figure_block(course: str, mermaid: str) -> str:
    caption = (
        f"Lean module dependencies for the {course} solution. "
        "Amber box: Mathlib imports. Blue box: solution modules."
    )
    return (
        "<!-- lean-dep-figure -->\n"
        f"<!-- figure-caption: {caption} -->\n"
        "```mermaid\n"
        f"{mermaid}"
        "```\n"
        "<!-- /lean-dep-figure -->\n"
    )


def insert_under_solution(text: str, block: str) -> str:
    text = MARKER_RE.sub("", text)
    m = re.search(r"^## Solution\s*$", text, re.MULTILINE)
    if not m:
        raise RuntimeError("missing ## Solution heading")
    insert_at = m.end()
    rest = text[insert_at:].lstrip("\n")
    return text[:insert_at] + "\n\n" + block + "\n" + rest


def main() -> None:
    for md, course, seeds in COURSE_LEANS:
        rels = course_files(seeds)
        block = figure_block(course, mermaid_for(rels))
        path = ROOT / "courses" / md
        path.write_text(insert_under_solution(path.read_text(encoding="utf-8"), block), encoding="utf-8")
        print(f"updated {md}")


if __name__ == "__main__":
    main()
