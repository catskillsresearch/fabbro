#!/usr/bin/env python3
"""Assemble arxiv.md + course notes + Lean sources → arxiv_with_code.md."""

from __future__ import annotations

import re
from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GITHUB = "https://github.com/catskillsresearch/fabbro"

PHASES: list[tuple[str, str, list[tuple[str, list[str]]]]] = [
    (
        "Phase 1: Language and linear structure",
        "Calculus, proof language, dual bases, and combinatorial cancellation.",
        [
            ("21-120-21-122.md", ["BSinMeasurementTheory/Course21120FTC.lean", "BSinMeasurementTheory/Course21120Taylor.lean"]),
            ("21-127.md", ["BSinMeasurementTheory/Course21127.lean"]),
            ("21-241.md", ["BSinMeasurementTheory/Course21241.lean", "BSinMeasurementTheory/Course21241Numerical.lean"]),
            ("21-228.md", ["BSinMeasurementTheory/Course21228.lean"]),
        ],
    ),
    (
        "Phase 2: Analysis, algebras, and formal proof",
        "Completeness, finite Boolean algebras, and Scott's Theorems 1.1--1.3 in Lean.",
        [
            ("21-355.md", [
                "BSinMeasurementTheory/Course21355.lean",
                "BSinMeasurementTheory/Course21355/BolzanoWeierstrass.lean",
                "BSinMeasurementTheory/Course21355/LimsupLiminf.lean",
                "BSinMeasurementTheory/Course21355/AltSeq.lean",
                "BSinMeasurementTheory/Course21355/CompactIcc.lean",
                "BSinMeasurementTheory/Course21355/Numerical.lean",
            ]),
            ("21-373.md", ["BSinMeasurementTheory/Course21373.lean", "BSinMeasurementTheory/Course21373Numerical.lean"]),
            ("21-321.md", [
                "BSinMeasurementTheory/Course21321.lean",
                "BSinMeasurementTheory/Course21321/ScottPair.lean",
                "BSinMeasurementTheory/Course21321/Theorem11.lean",
                "BSinMeasurementTheory/Course21321/Theorem12.lean",
                "BSinMeasurementTheory/Course21321/Theorem13.lean",
                "BSinMeasurementTheory/Course21321/Kraft.lean",
            ]),
        ],
    ),
    (
        "Phase 3: Duality and set theory",
        "Linear-programming duality and the ultrafilter engine of the infinite case.",
        [
            ("21-292.md", ["BSinMeasurementTheory/Course21292.lean", "BSinMeasurementTheory/Course21292Numerical.lean"]),
            ("21-329.md", ["BSinMeasurementTheory/Course21329.lean"]),
        ],
    ),
    (
        "Phase 4: Stone spaces and measures",
        "Stone representation and Riesz representation.",
        [
            ("21-651.md", ["BSinMeasurementTheory/Course21651.lean"]),
            ("21-720.md", ["BSinMeasurementTheory/Course21720.lean"]),
        ],
    ),
    (
        "Phase 5: The missing extension",
        "Hahn--Banach, the step Scott cites and leaves unproved.",
        [
            ("21-640.md", ["BSinMeasurementTheory/Course21640.lean"]),
        ],
    ),
    (
        "Phase 6: Assembly and consistency check",
        "The infinite extension of Theorem 4.1, and the finite/infinite agreement check.",
        [
            ("21-410-21-599.md", ["BSinMeasurementTheory/Course21410.lean"]),
            ("21-322.md", ["BSinMeasurementTheory/Course21322.lean"]),
        ],
    ),
]

def library_lean_files() -> list[str]:
    files = ["BSinMeasurementTheory.lean"]
    lib = ROOT / "BSinMeasurementTheory"
    files.extend(sorted(p.relative_to(ROOT).as_posix() for p in lib.rglob("*.lean")))
    return files


def course_lean_files(rels: list[str]) -> list[str]:
    """Barrel path plus every file in a matching CourseXXXX/ directory."""
    out: list[str] = []
    seen: set[str] = set()

    def add(rel: str) -> None:
        if rel not in seen and (ROOT / rel).is_file():
            seen.add(rel)
            out.append(rel)

    for rel in rels:
        add(rel)
        path = ROOT / rel
        sibling_dir = path.with_suffix("") if path.suffix == ".lean" else path
        if sibling_dir.is_dir():
            for child in sorted(sibling_dir.rglob("*.lean")):
                add(child.relative_to(ROOT).as_posix())
    return out


LEAN_FILES = library_lean_files()

MODULE_DOC = re.compile(r"/-!\s*(.*?)\s*-/", re.DOTALL)
DECL_DOC = re.compile(r"/--\s*(.*?)\s*-/", re.DOTALL)


_ASCII_FROM_UNICODE = (
    ("ℝ", "R"),
    ("ℚ", "Q"),
    ("ℤ", "Z"),
    ("ℕ", "N"),
    ("ℵ", "aleph"),
    ("∫", "integral "),
    ("≤", "<="),
    ("≥", ">="),
    ("≠", "!="),
    ("∈", " in "),
    ("⊆", " subset "),
    ("∅", "empty"),
    ("⊥", "bottom"),
    ("⊤", "top"),
    ("∧", " and "),
    ("∨", " or "),
    ("¬", "not "),
    ("→", " -> "),
    ("↔", " <-> "),
    ("∀", "for all "),
    ("∃", "exists "),
    ("∞", "infinity"),
    ("α", "alpha"),
    ("ε", "epsilon"),
    ("φ", "phi"),
    ("Λ", "Lambda"),
    ("₀", "0"),
    ("₁", "1"),
    ("₂", "2"),
    ("₃", "3"),
    ("ˣ", "x"),
    ("²", "^2"),
    ("³", "^3"),
    ("⁴", "^4"),
    ("⁵", "^5"),
    ("—", "--"),
    ("–", "-"),
    ("‘", "'"),
    ("’", "'"),
    ("“", '"'),
    ("”", '"'),
    ("×", "x"),
)


def _ascii(text: str) -> str:
    for src, dst in _ASCII_FROM_UNICODE:
        text = text.replace(src, dst)
    text = re.sub(r"[^\x00-\x7f]", "", text)
    text = re.sub(r"\s+", " ", text).strip()
    return text


def _clip(text: str) -> str:
    text = _ascii(re.sub(r"\s+", " ", text.replace("`", "")).strip())
    if not text:
        return ""
    cut = len(text)
    for sep in (". ", "; "):
        idx = text.find(sep)
        if 20 <= idx < cut:
            cut = idx
    sentence = text[:cut].rstrip(" .;:")
    if len(sentence) > 140:
        sentence = sentence[:137].rsplit(" ", 1)[0] + "..."
    return sentence


def _one_line(text: str) -> str:
    """Prefer the first heading or sentence, not the whole module comment."""
    for raw in text.splitlines():
        line = re.sub(r"^#+\s*", "", raw.strip())
        if line:
            return _clip(line)
    return _clip(text)


def _looks_like_identifier(text: str) -> bool:
    return bool(text) and " " not in text and text.isalnum()


# Path-keyed first, then basename. Used when module comments are headings or fragments.
FILE_BLURBS: dict[str, str] = {
    "BSinMeasurementTheory/Course21120FTC.lean":
        "Fundamental theorem of calculus for the Fresnel-type integrand.",
    "BSinMeasurementTheory/Course21120Taylor.lean":
        "Degree-9 Taylor estimate of f(0.5) with an explicit remainder bound.",
    "BSinMeasurementTheory/Course21127/NonzeroDenomInt.lean":
        "Integers with a nonzero denominator: the domain of the fraction relation.",
    "BSinMeasurementTheory/Course21127/ToRat.lean":
        "The explicit map from a pair (a, b) to the rationals, and the induced bijection.",
    "BSinMeasurementTheory/Course21127/WellOrder.lean":
        "Well-ordered subsets of Q, and a refutation of the claimed well-order of the positives.",
    "BSinMeasurementTheory/Course21228/Counting.lean":
        "Count of permutation pairs that make two sequences agree termwise.",
    "BSinMeasurementTheory/Course21228/SmallN.lean":
        "Exact pair counts for n = 2 and n = 3.",
    "BSinMeasurementTheory/Course21228/Symmetric.lean":
        "Symmetric conditions on length-n sequences and permutation invariance of sums.",
    "BSinMeasurementTheory/Course21241/Basis.lean":
        "Standard primal basis of three-space and the dual basis functionals.",
    "BSinMeasurementTheory/Course21241/DualCone.lean":
        "The dual cone of the non-negative orthant.",
    "BSinMeasurementTheory/Course21241/Numerical.lean":
        "Concrete separating functional for a point outside the orthant.",
    "BSinMeasurementTheory/Course21241/Separation.lean":
        "Euclidean inner product, Riesz identification, and a separating vector.",
    "BSinMeasurementTheory/Course21241/Space.lean":
        "The non-negative orthant cone in three-space.",
    "BSinMeasurementTheory/Course21292/Instance.lean":
        "A concrete 3x3 Scott-type linear program.",
    "BSinMeasurementTheory/Course21292/LinearProgram.lean":
        "Inequality-form linear programs over the rationals.",
    "BSinMeasurementTheory/Course21292/WeakDuality.lean":
        "Weak duality for a primal/dual linear program.",
    "BSinMeasurementTheory/Course21292Numerical.lean":
        "Numerical checks of the four calculations in the 21-292 example.",
    "BSinMeasurementTheory/Course21321/Kraft.lean":
        "Kraft difference vectors as a ScottPair with a cancellation witness.",
    "BSinMeasurementTheory/Course21321/ScottPair.lean":
        "Scott pairs, separating functionals, and the cancellation-witness class.",
    "BSinMeasurementTheory/Course21321/Theorem11.lean":
        "Scott's Theorem 1.1: a separable pair satisfies real non-cancellation.",
    "BSinMeasurementTheory/Course21321/Theorem12.lean":
        "Scott's Theorem 1.2: rational separability implies combinatorial non-cancellation.",
    "BSinMeasurementTheory/Course21321/Theorem13.lean":
        "Scott's Theorem 1.3 (one direction): rational non-cancellation implies real non-cancellation.",
    "BSinMeasurementTheory/Course21322/AtomIso.lean":
        "Canonical bijection between atoms and the Stone space of a finite algebra.",
    "BSinMeasurementTheory/Course21322/Hom.lean":
        "Boolean homomorphisms from a power set into Bool, and principal evaluations.",
    "BSinMeasurementTheory/Course21322/MeasureCollapse.lean":
        "Collapse of Stone-space measure evaluation to the discrete atomic measure.",
    "BSinMeasurementTheory/Course21322/Numerical.lean":
        "Direct calculation of the atomic measure on {0, 2}.",
    "BSinMeasurementTheory/Course21322/StoneClopen.lean":
        "The Stone clopen associated with an element and preservation of membership.",
    "BSinMeasurementTheory/Course21329/Cardinality.lean":
        "Cardinal-arithmetic argument that the Stone space is large.",
    "BSinMeasurementTheory/Course21329/Filter.lean":
        "Filters, proper filters, and ultrafilters on a bounded lattice.",
    "BSinMeasurementTheory/Course21329/StoneNonempty.lean":
        "The principal filter generated by top, and non-emptiness of the Stone space.",
    "BSinMeasurementTheory/Course21329/UltrafilterExtension.lean":
        "Ultrafilter extension: a chain of proper filters unions to a proper filter.",
    "BSinMeasurementTheory/Course21355/AltSeq.lean":
        "The alternating sequence of plus and minus one, and an epsilon-argument that it diverges.",
    "BSinMeasurementTheory/Course21355/BolzanoWeierstrass.lean":
        "Bolzano-Weierstrass: a bounded real sequence has a convergent subsequence.",
    "BSinMeasurementTheory/Course21355/CompactIcc.lean":
        "Closed bounded intervals in R are compact.",
    "BSinMeasurementTheory/Course21355/LimsupLiminf.lean":
        "Tail supremum and tail infimum of a real sequence.",
    "BSinMeasurementTheory/Course21355/Numerical.lean":
        "Computable alternating sequence used to inspect the example of (c).",
    "BSinMeasurementTheory/Course21373/AtomJoin.lean":
        "Join and disjointness properties of Boolean atoms.",
    "BSinMeasurementTheory/Course21373/BooleanAction.lean":
        "Boolean automorphisms and atoms of the fixed-point subalgebra.",
    "BSinMeasurementTheory/Course21373/IsBooleanAtom.lean":
        "Atoms in a Boolean algebra.",
    "BSinMeasurementTheory/Course21373/Representation.lean":
        "Canonical representation of an element as the join of the atoms below it.",
    "BSinMeasurementTheory/Course21373Numerical.lean":
        "Numerical example for the finite Boolean-algebra representation.",
    "BSinMeasurementTheory/Course21410/Glue.lean":
        "Glue lemmas: inclusion-exclusion, monotonicity, and preference preservation.",
    "BSinMeasurementTheory/Course21410/Measure.lean":
        "Finitely additive probability measures on a finite space.",
    "BSinMeasurementTheory/Course21640/Numerical.lean":
        "Sup-norm example of a sublinear functional and a dominated extension on the plane.",
    "BSinMeasurementTheory/Course21640/Sublinear.lean":
        "Sublinear functionals and dominated linear extensions.",
    "BSinMeasurementTheory/Course21651/BooleanHom.lean":
        "Boolean algebra homomorphisms from B to Bool.",
    "BSinMeasurementTheory/Course21651/ClosedEmbedding.lean":
        "The Stone space as an intersection of closed equalizer sets in B -> Bool.",
    "BSinMeasurementTheory/Course21651/Separation.lean":
        "Separation properties used by the Stone embedding argument.",
    "BSinMeasurementTheory/Course21651/StoneMap.lean":
        "The Stone clopen associated with an element of B.",
    "BSinMeasurementTheory/Course21651/TwoAlgebra.lean":
        "Stone space of the four-element Boolean algebra on Fin 2.",
    "BSinMeasurementTheory/Course21720/Boundedness.lean":
        "Positive linear functionals on C(X, R) are bounded.",
    "BSinMeasurementTheory/Course21720/Numerical.lean":
        "The concrete functional Lambda(f) = 3 f(0) + 2 f(1).",
    "BSinMeasurementTheory/Course21720/StoneMeasure.lean":
        "Finitely additive measures on a Boolean algebra from a positive functional.",
    "Numerical.lean": "Numerical checks reproducing the English example.",
}


def is_import_only(code: str) -> bool:
    lines = [
        ln.strip()
        for ln in code.splitlines()
        if ln.strip() and not ln.strip().startswith("--")
    ]
    return bool(lines) and all(ln.startswith("import ") for ln in lines)


def describe_lean(rel: str) -> str:
    """One-line English for the appendix index; sources stay inlined in the notes."""
    if rel == "BSinMeasurementTheory.lean":
        return "Root importer for the library."
    code = (ROOT / rel).read_text(encoding="utf-8")
    if is_import_only(code):
        stem = Path(rel).stem
        m = re.fullmatch(r"Course(\d{5})", stem)
        if m:
            num = m.group(1)
            return f"Umbrella importer for the 21-{num[2:]} modules."
        if stem.startswith("Course"):
            return f"Umbrella importer for the {stem} modules."
        return "Umbrella importer for this course."
    for key in (rel, Path(rel).name):
        if key in FILE_BLURBS:
            return _ascii(FILE_BLURBS[key])
    m = MODULE_DOC.search(code)
    if m:
        desc = _one_line(m.group(1))
        if desc and not _looks_like_identifier(desc):
            return desc
    m = DECL_DOC.search(code)
    if m:
        desc = _one_line(m.group(1))
        if desc and not _looks_like_identifier(desc):
            return desc
    return Path(rel).stem


def paper_title(arxiv_text: str) -> str:
    first = arxiv_text.splitlines()[0] if arxiv_text else "# Formalization of a BS in Measurement Theory"
    return first[2:].strip() if first.startswith("# ") else first.strip()


def narrative_without_references(arxiv_text: str) -> tuple[str, str]:
    body = arxiv_text
    if body.startswith("# "):
        idx = body.find("\n---\n")
        body = body[idx + len("\n---\n") :] if idx != -1 else body[body.find("\n") + 1 :]
    refs = ""
    m = re.search(r"^## References\s*$", body, re.MULTILINE)
    if m:
        refs = body[m.start():].rstrip()
        body = body[: m.start()].rstrip()
    return body, refs


def demote_headings(text: str, n: int = 2) -> str:
    def repl(match: re.Match[str]) -> str:
        hashes = match.group(1)
        rest = match.group(2)
        level = min(len(hashes) + n, 6)
        return "#" * level + rest

    return re.sub(r"^(#{1,6})([ \t].*)$", repl, text, flags=re.MULTILINE)


GEMINI_LINE = re.compile(r"^\*\*Gemini[^*]*\*\*\.?[^\n]*$", re.MULTILINE)
LEAN_INCLUDE = re.compile(
    r"<!--\s*lean:\s*(\S+?)\s*-->(?:\s*```lean\n.*?^```)*",
    re.MULTILINE | re.DOTALL,
)


def expand_lean_includes(text: str) -> str:
    """Replace `<!-- lean: path -->` with that file's source, as a lean fence."""

    def repl(match: re.Match[str]) -> str:
        rel = match.group(1)
        path = ROOT / rel
        if not path.is_file():
            raise FileNotFoundError(f"lean include missing: {rel}")
        code = path.read_text(encoding="utf-8").rstrip()
        return f"<!-- lean: {rel} -->\n\n```lean\n{code}\n```\n"

    return LEAN_INCLUDE.sub(repl, text)


def rewrite_lean_links(text: str) -> str:
    text = re.sub(r"^\[← Syllabus\]\([^)]+\)\s*\n+", "", text)
    text = GEMINI_LINE.sub("", text)
    text = expand_lean_includes(text)
    text = re.sub(
        r"Lean 4 formalization: \[`([^`]+)`\]\([^)]+\)\.",
        r"<!-- lean: \1 -->",
        text,
    )
    text = expand_lean_includes(text)
    return text


def ensure_blank_before_headings(text: str) -> str:
    return re.sub(r"(?<!\n)\n(#{1,6}[ \t])", r"\n\n\1", text)


def flatten_deep_headings(text: str) -> str:
    """Headings at five or six hashes become bold run-ins; Pandoc will not
    treat them as headings after a paragraph, and they print as raw ######."""

    def repl(match: re.Match[str]) -> str:
        return f"**{match.group(1).strip()}**\n\n"

    return re.sub(r"^#{5,6}[ \t]+(.+)$", repl, text, flags=re.MULTILINE)


def course_body(rel: str) -> str:
    text = (ROOT / "courses" / rel).read_text(encoding="utf-8")
    text = rewrite_lean_links(text)
    text = demote_headings(text, 2)
    text = flatten_deep_headings(text)
    text = ensure_blank_before_headings(text)
    return text.strip() + "\n"


def main() -> None:
    arxiv = (ROOT / "arxiv.md").read_text(encoding="utf-8")
    title = paper_title(arxiv)
    body, refs = narrative_without_references(arxiv)

    parts: list[str] = []
    parts.append(
        "<!-- AUTO-GENERATED: run scripts/generate_arxiv_with_code.sh to refresh -->\n"
    )
    parts.append(f"# {title} — narrative + Lean module index\n\n")
    parts.append(
        f"*Generated {date.today().isoformat()} from `arxiv.md`, `courses/`, "
        "and `BSinMeasurementTheory/`.*\n\n"
    )
    parts.append("---\n\n")
    parts.append("# Narrative (from arxiv.md)\n\n")
    parts.append(body.rstrip())
    parts.append("\n\n")

    for phase_title, blurb, courses in PHASES:
        parts.append(f"## {phase_title}\n\n")
        parts.append(f"{blurb}\n\n")
        for md, _leans in courses:
            parts.append(course_body(md))
            parts.append("\n")

    if refs:
        parts.append(refs)
        parts.append("\n\n")

    parts.append("## Lean module index\n\n")
    parts.append(
        f"Checked by `lake build`. Each module is inlined next to the English "
        f"it proves. This appendix lists the files only; the sources live at "
        f"[{GITHUB}]({GITHUB}).\n\n"
    )
    parts.append("| File | Contents |\n| --- | --- |\n")
    for rel in LEAN_FILES:
        link = f"[`{rel}`]({GITHUB}/blob/main/{rel})"
        parts.append(f"| {link} | {describe_lean(rel)} |\n")
    parts.append("\n")

    total_lines = sum(
        len((ROOT / rel).read_text(encoding="utf-8").splitlines()) for rel in LEAN_FILES
    )
    parts.append(f"**Total:** {len(LEAN_FILES)} modules, {total_lines} lines.\n")

    out = ROOT / "arxiv_with_code.md"
    out.write_text("".join(parts), encoding="utf-8")
    print(f"wrote {out} ({total_lines} Lean lines across {len(LEAN_FILES)} files)")


if __name__ == "__main__":
    main()
