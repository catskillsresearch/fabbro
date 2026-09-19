#!/usr/bin/env python3
"""Convert arxiv_with_code.md to a CMU SCS technical report."""

from __future__ import annotations

import re
import subprocess
import sys
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))
from lean_listing_sanitize import chunk_line_ranges, sanitize_lean_for_arxiv

SRC = ROOT / "arxiv_with_code.md"
OUT = ROOT / "arxiv.tex"
PREAMBLE = SCRIPTS / "tex_preamble_arxiv.tex"
LISTINGS_DIR = ROOT / "lean-listings"
LISTING_CHUNK_LINES = 400

GITHUB_URL = r"https://github.com/catskillsresearch/fabbro"
REPORT_NUMBER = "CMU-CS-26-XXX"
REPORT_DATE = "September 2026"


def extract_title() -> str:
    first = (ROOT / "arxiv.md").read_text(encoding="utf-8").splitlines()[0]
    title = first[2:].strip() if first.startswith("# ") else first.strip()
    return re.sub(r"\*([^*]+)\*", r"\\emph{\1}", title)


TITLE = extract_title()

GITHUB_INLINE_MATH = re.compile(r"\$`([^`\n]+?)`\$")
HTML_COMMENT = re.compile(r"<!--.*?-->", re.DOTALL)
FENCE_RE = re.compile(r"^```([^\n]*)\n(.*?)^```\s*$", re.MULTILINE | re.DOTALL)
MANUAL_SECTION_NUM = re.compile(r"^(#{1,6})[ \t]+\d+(?:\.\d+)*\.?[ \t]+", re.MULTILINE)
NARRATIVE_MARKER = "# Narrative (from arxiv.md)"
LEAN_MODULE_RE = re.compile(r"^###\s+(BSinMeasurementTheory(?:\.lean|/[^\s{]+))\s*$", re.MULTILINE)


def github_math_to_tex(text: str) -> str:
    text = GITHUB_INLINE_MATH.sub(r"$\1$", text)
    # Pandoc treats \[...\] as an escaped [span], not display math.
    text = re.sub(r"\\\[(.*?)\\\]", r"$$\1$$", text, flags=re.DOTALL)
    return text


def strip_html_comments(text: str) -> str:
    return HTML_COMMENT.sub("", text)


def strip_manual_section_numbers(text: str) -> str:
    return MANUAL_SECTION_NUM.sub(r"\1 ", text)


def drop_github_nav(text: str) -> str:
    idx = text.find(NARRATIVE_MARKER)
    if idx == -1:
        return text
    return text[idx + len(NARRATIVE_MARKER) :].lstrip("\n")


def extract_abstract(text: str) -> tuple[str, str]:
    m = re.search(r"^##\s+Abstract\s*\n(.*?)(?=^##\s)", text, re.DOTALL | re.MULTILINE)
    if not m:
        return "", text
    return m.group(1).strip(), text[: m.start()] + text[m.end() :]


def write_listing(code: str, listing_name: str) -> tuple[str, int]:
    LISTINGS_DIR.mkdir(parents=True, exist_ok=True)
    source = sanitize_lean_for_arxiv(code.rstrip("\n"))
    listing_path = LISTINGS_DIR / listing_name
    listing_path.write_text(source + "\n", encoding="utf-8")
    return listing_path.relative_to(ROOT).as_posix(), (len(source.splitlines()) if source else 0)


def lean_block_latex(code: str, listing_name: str) -> str:
    rel_path, line_count = write_listing(code, listing_name)
    ranges = chunk_line_ranges(line_count, LISTING_CHUNK_LINES)
    parts: list[str] = []
    for first, last in ranges:
        label = "Lean 4 source" if first == 1 and last == line_count else f"Lean 4 source (lines {first}--{last})"
        firstlast = "" if first == 1 and last == line_count else f",firstline={first},lastline={last}"
        parts.append(
            "\\vspace{0.5\\baselineskip}\n"
            f"\\noindent\\textcolor{{green!40!black}}{{\\textbf{{{label}}}}}"
            "\\par\\vspace{0.25\\baselineskip}\n"
            f"\\lstinputlisting[style=leanbox{firstlast}]{{{rel_path}}}\n"
            "\\vspace{0.5\\baselineskip}\n\n"
        )
    return "".join(parts)


def extract_lean_titles(text: str) -> dict[str, str]:
    titles: dict[str, str] = {}
    lean_starts = [m.start() for m in re.finditer(r"^```lean\s*$", text, re.MULTILINE)]
    for idx, pos in enumerate(lean_starts):
        module = None
        for line in reversed(text[:pos].rstrip("\n").splitlines()[-4:]):
            m = LEAN_MODULE_RE.match(line.strip())
            if m:
                module = m.group(1)
                break
        titles[f"LEANINCLUDE{idx:03d}"] = module or f"module-{idx + 1}"
    return titles


def replace_fences(text: str) -> tuple[str, dict[str, str]]:
    lean_titles = extract_lean_titles(text)
    placeholders: dict[str, str] = {}
    lean_idx = 0
    other_idx = 0

    def repl(match: re.Match[str]) -> str:
        nonlocal lean_idx, other_idx
        lang = match.group(1).strip().lower()
        body = match.group(2)
        if lang == "lean":
            key = f"LEANINCLUDE{lean_idx:03d}"
            module = lean_titles.get(key, f"module-{lean_idx}")
            lean_idx += 1
            safe_name = module.replace("/", "-")
            if not safe_name.endswith(".lean"):
                safe_name += ".lean"
            placeholders[key] = lean_block_latex(body, safe_name)
            return f"\n\n{key}\n\n"
        key = f"CODEINCLUDE{other_idx:03d}"
        rel_path, _ = write_listing(body, f"snippet-{other_idx:03d}.txt")
        other_idx += 1
        placeholders[key] = f"\\lstinputlisting[style=leanbox]{{{rel_path}}}\n"
        return f"\n\n{key}\n\n"

    return FENCE_RE.sub(repl, text), placeholders


def pandoc_to_latex(markdown: str, shift: bool = True) -> str:
    cmd = ["pandoc", "-f", "markdown+tex_math_dollars+raw_tex+smart", "-t", "latex", "--wrap=none"]
    if shift:
        cmd += ["--shift-heading-level-by=-1"]
    proc = subprocess.run(cmd, input=markdown, text=True, capture_output=True, check=False)
    if proc.returncode != 0:
        print(proc.stderr, file=sys.stderr)
        raise RuntimeError("pandoc failed")
    return proc.stdout


def inject_placeholders(latex: str, placeholders: dict[str, str]) -> str:
    out = latex
    for key, value in placeholders.items():
        for pat in (key, f"\\emph{{{key}}}", f"\\text{{{key}}}"):
            if pat in out:
                out = out.replace(pat, value)
                break
        else:
            out = out.replace(key, value)
    return out


def break_texttt_paths(latex: str) -> str:
    def fix(match: re.Match[str]) -> str:
        inner = match.group(1)
        inner = inner.replace("/", "/\\allowbreak{}")
        inner = inner.replace(r"\_", r"\_\allowbreak{}")
        inner = re.sub(r"(?<=[a-z])(?=[A-Z])", r"\\allowbreak{}", inner)
        inner = inner.replace(".lean", ".\\allowbreak{}lean")
        return "\\texttt{" + inner + "}"

    return re.sub(r"\\texttt\{([^{}]*)\}", fix, latex)


def cleanup_pandoc_latex(latex: str) -> str:
    latex = latex.replace("\\pandocbounded{", "{")
    latex = re.sub(r"\\tightlist\n", "", latex)
    latex = break_texttt_paths(latex)
    for cmd in ("section", "subsection", "subsubsection", "paragraph"):
        latex = re.sub(rf"(\\{cmd}\{{)\d+(?:\.\d+)*\.?\s+", r"\1", latex)
    latex = re.sub(r"\n{3,}", "\n\n", latex)
    return latex


def insert_appendix_command(latex: str) -> str:
    # Place these outside Pandoc's \hypertarget{...}{...} group so tocdepth
    # is not restored after the section command.
    marker = r"\hypertarget{lean-module-index}{%"
    if marker not in latex:
        marker = r"\section{Lean module index}"
        if marker not in latex:
            raise RuntimeError("missing Lean module index section in LaTeX output")
    return latex.replace(
        marker,
        (
            r"\appendix" + "\n"
            + r"\setcounter{tocdepth}{1}" + "\n"
            + r"\addtocontents{toc}{\protect\setcounter{tocdepth}{1}}" + "\n"
            + marker
        ),
        1,
    )


def cleanup_abstract_latex(latex: str) -> str:
    latex = latex.replace("\\pandocbounded{", "{")
    latex = re.sub(r"\\begin\{center\}\\rule\{.*?\}\\end\{center\}\s*", "", latex, flags=re.DOTALL)
    return latex


def build_title_page(abstract_latex: str) -> str:
    github_latex = rf"\url{{{GITHUB_URL}}}"
    pdf_subject = (
        f"Carnegie Mellon University School of Computer Science Technical Report {REPORT_NUMBER}"
    )
    return textwrap.dedent(
        f"""
        \\title{{{TITLE}}}

        \\author{{
          Lars Warren Ericson \\\\
          {{\\normalfont\\small Catskills Research Company}}
        }}

        \\date{{{REPORT_DATE}}}
        \\trnumber{{{REPORT_NUMBER}}}
        \\keywords{{Lean 4; formal verification; measurement theory; undergraduate curriculum;
          Scott 1964; Boolean algebras; Stone spaces}}
        \\citationinfo{{Source repository: {github_latex}}}
        \\copyrightnotice{{Copyright \\copyright\\ 2026 Lars Warren Ericson}}
        \\abstract{{
        {abstract_latex.strip()}
        }}
        \\hypersetup{{
          pdftitle={{{TITLE}}},
          pdfauthor={{Lars Warren Ericson}},
          pdfsubject={{{pdf_subject}}},
          pdfkeywords={{Lean 4, formal verification, measurement theory, undergraduate curriculum}}
        }}

        \\setcounter{{secnumdepth}}{{5}}
        \\setcounter{{tocdepth}}{{5}}

        \\begin{{document}}

        \\maketitle
        \\tableofcontents
        \\clearpage
        """
    ).strip()


def main() -> int:
    if not SRC.is_file():
        print(f"error: missing {SRC}; run scripts/generate_arxiv_with_code.sh first", file=sys.stderr)
        return 1
    if LISTINGS_DIR.exists():
        for path in LISTINGS_DIR.iterdir():
            if path.is_file():
                path.unlink()
    LISTINGS_DIR.mkdir(parents=True, exist_ok=True)

    body = drop_github_nav(SRC.read_text(encoding="utf-8"))
    body = strip_html_comments(body)
    abstract_md, body = extract_abstract(body)
    body = strip_manual_section_numbers(body)
    body = github_math_to_tex(body)
    body, placeholders = replace_fences(body)

    latex_body = pandoc_to_latex(body, shift=True)
    latex_body = inject_placeholders(latex_body, placeholders)
    latex_body = cleanup_pandoc_latex(latex_body)
    latex_body = insert_appendix_command(latex_body)

    abstract_latex = pandoc_to_latex(github_math_to_tex(abstract_md), shift=False) if abstract_md else ""
    abstract_latex = cleanup_abstract_latex(abstract_latex)

    document = (
        PREAMBLE.read_text(encoding="utf-8")
        + "\n\n"
        + build_title_page(abstract_latex)
        + "\n\n"
        + latex_body
        + "\n\n\\end{document}\n"
    )
    OUT.write_text(document, encoding="utf-8")
    n_listings = sum(1 for p in LISTINGS_DIR.iterdir() if p.is_file())
    print(f"wrote {OUT.relative_to(ROOT)} ({OUT.stat().st_size:,} bytes, {n_listings} listings)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
