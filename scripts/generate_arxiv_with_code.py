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
        f"Checked by `lake build`. Complete sources: [{GITHUB}]({GITHUB}). "
        "Each subsection is the corresponding library file.\n\n"
    )
    parts.append("| Role | File |\n| --- | --- |\n")
    parts.append("| Root importer | [`BSinMeasurementTheory.lean`]("
                  f"{GITHUB}/blob/main/BSinMeasurementTheory.lean) |\n")
    for _, _, courses in PHASES:
        for md, leans in courses:
            course = md.replace(".md", "")
            for lean in course_lean_files(leans):
                parts.append(
                    f"| {course} | [`{lean}`]({GITHUB}/blob/main/{lean}) |\n"
                )
    parts.append("\n")

    total_lines = 0
    for rel in LEAN_FILES:
        code = (ROOT / rel).read_text(encoding="utf-8")
        total_lines += len(code.splitlines())

    parts.append(
        f"The Lean sources are inlined in the course writeups above. "
        f"**Total:** {len(LEAN_FILES)} modules, {total_lines} lines.\n"
    )

    out = ROOT / "arxiv_with_code.md"
    out.write_text("".join(parts), encoding="utf-8")
    print(f"wrote {out} ({total_lines} Lean lines across {len(LEAN_FILES)} files)")


if __name__ == "__main__":
    main()
