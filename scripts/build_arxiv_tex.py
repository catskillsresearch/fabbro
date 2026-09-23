#!/usr/bin/env python3
"""Convert arxiv_with_code.md to a CMU SCS technical report.

Mermaid fences are rendered live to PNG via mermaid-cli (mmdc), never PDF.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
import textwrap
from pathlib import Path
from xml.etree import ElementTree as ET

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))
from lean_listing_sanitize import chunk_line_ranges, sanitize_lean_for_arxiv

SRC = ROOT / "arxiv_with_code.md"
OUT = ROOT / "arxiv.tex"
PREAMBLE = SCRIPTS / "tex_preamble_arxiv.tex"
LISTINGS_DIR = ROOT / "lean-listings"
FIGURES_DIR = ROOT / "figures"
PUPPETEER_CONFIG = SCRIPTS / "puppeteer-config.json"
LISTING_CHUNK_LINES = 400

GITHUB_URL = r"https://github.com/catskillsresearch/fabbro"
REPORT_NUMBER = "CMU-CS-26-XXX"
REPORT_DATE = "September 2026"

# Mermaid course node id -> pandoc hypertarget for that course subsection.
COURSE_ANCHORS = {
    "C120": "differential-and-integral-calculus-integration-and-approximation",
    "C127": "concepts-of-mathematics",
    "C241": "matrices-and-linear-transformations",
    "C228": "discrete-mathematics",
    "C355": "principles-of-real-analysis-i",
    "C373": "algebraic-structures",
    "C321": "interactive-theorem-proving",
    "C292": "operations-research-i",
    "C329": "set-theory",
    "C651": "general-topology",
    "C720": "measure-and-integration",
    "C640": "introduction-to-functional-analysis",
    "C410": "independent-study",
    "C322": "topics-in-formal-mathematics-opportunistic",
}

TRANSLATE_RE = re.compile(r"translate\(\s*([-\d.]+)\s*,\s*([-\d.]+)\s*\)")
FLOW_NODE_RE = re.compile(r"^flowchart-(C\d+)-\d+$")


def find_chrome() -> str | None:
    env = os.environ.get("PUPPETEER_EXECUTABLE_PATH")
    if env and Path(env).exists():
        return env
    for name in ("google-chrome", "google-chrome-stable", "chromium", "chromium-browser"):
        path = shutil.which(name)
        if path:
            return path
    return None


def run_mmdc(mmd_path: Path, out_path: Path, idx: int) -> None:
    mmdc = shutil.which("mmdc")
    if not mmdc:
        raise RuntimeError(
            "mermaid-cli (mmdc) not found; install with "
            "`npm install -g @mermaid-js/mermaid-cli`"
        )
    env = os.environ.copy()
    chrome = find_chrome()
    if chrome:
        env["PUPPETEER_EXECUTABLE_PATH"] = chrome
    cmd = [
        mmdc,
        "-i",
        str(mmd_path),
        "-o",
        str(out_path),
        "-b",
        "white",
        "-w",
        "1600",
        "-s",
        "2",
    ]
    if PUPPETEER_CONFIG.is_file():
        cmd += ["-p", str(PUPPETEER_CONFIG)]
    proc = subprocess.run(cmd, env=env, capture_output=True, text=True, check=False)
    if proc.returncode != 0 or not out_path.is_file():
        sys.stderr.write(proc.stdout + "\n" + proc.stderr + "\n")
        raise RuntimeError(f"mmdc failed to render figure {idx} ({out_path.suffix})")


def _parse_translate(transform: str | None) -> tuple[float, float]:
    if not transform:
        return 0.0, 0.0
    match = TRANSLATE_RE.search(transform)
    if not match:
        return 0.0, 0.0
    return float(match.group(1)), float(match.group(2))


def course_hotspots_from_svg(svg_path: Path) -> list[tuple[str, float, float, float, float]]:
    """Map course nodes to unit-square boxes (origin south-west) for TikZ."""
    root = ET.fromstring(svg_path.read_text(encoding="utf-8"))
    vb = (root.attrib.get("viewBox") or "0 0 1 1").split()
    min_x, min_y, width, height = (float(v) for v in vb)
    if width <= 0 or height <= 0:
        return []

    found: dict[str, tuple[str, float, float, float, float]] = {}

    def walk(el: ET.Element, tx: float, ty: float) -> None:
        dtx, dty = _parse_translate(el.attrib.get("transform"))
        tx, ty = tx + dtx, ty + dty
        match = FLOW_NODE_RE.match(el.attrib.get("id") or "")
        if match:
            node = match.group(1)
            anchor = COURSE_ANCHORS.get(node)
            if anchor:
                rect = next((c for c in el.iter() if c.tag.endswith("rect")), None)
                if rect is not None and "x" in rect.attrib:
                    x = float(rect.attrib["x"]) + tx
                    y = float(rect.attrib["y"]) + ty
                    w = float(rect.attrib["width"])
                    h = float(rect.attrib["height"])
                    x0 = (x - min_x) / width
                    x1 = (x + w - min_x) / width
                    y0 = 1.0 - (y + h - min_y) / height
                    y1 = 1.0 - (y - min_y) / height
                    found[node] = (anchor, x0, y0, x1, y1)
        for child in el:
            walk(child, tx, ty)

    walk(root, 0.0, 0.0)
    return [found[key] for key in COURSE_ANCHORS if key in found]


def figure_include_latex(
    rel_path: str,
    hotspots: list[tuple[str, float, float, float, float]],
) -> str:
    img = (
        f"\\includegraphics[max width=\\linewidth,"
        f"max totalheight=0.85\\textheight,keepaspectratio]{{{rel_path}}}"
    )
    if not hotspots:
        return img + "\n"
    spots = "\n".join(
        f"    \\coursehotspot{{{anchor}}}{{{x0:.5f}}}{{{y0:.5f}}}{{{x1:.5f}}}{{{y1:.5f}}}"
        for anchor, x0, y0, x1, y1 in hotspots
    )
    return (
        "\\begin{tikzpicture}\n"
        f"  \\node[anchor=south west,inner sep=0] (img) {{{img}}};\n"
        "  \\begin{scope}[x={(img.south east)},y={(img.north west)}]\n"
        f"{spots}\n"
        "  \\end{scope}\n"
        "\\end{tikzpicture}\n"
    )


def render_mermaid(code: str, idx: int) -> tuple[str, list[tuple[str, float, float, float, float]]]:
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    mmd_path = FIGURES_DIR / f"figure-{idx:03d}.mmd"
    png_path = FIGURES_DIR / f"figure-{idx:03d}.png"
    mmd_path.write_text(code.strip() + "\n", encoding="utf-8")
    run_mmdc(mmd_path, png_path, idx)

    hotspots: list[tuple[str, float, float, float, float]] = []
    if any(node in code for node in COURSE_ANCHORS):
        svg_path = FIGURES_DIR / f"figure-{idx:03d}.svg"
        run_mmdc(mmd_path, svg_path, idx)
        hotspots = course_hotspots_from_svg(svg_path)
    return png_path.relative_to(ROOT).as_posix(), hotspots


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
LEAN_PATH_RE = re.compile(r"<!--\s*lean:\s*(\S+?)\s*-->")
FIGURE_CAPTION_RE = re.compile(
    r"<!--\s*figure-caption:\s*(.*?)\s*-->\s*\n```mermaid",
    re.IGNORECASE | re.DOTALL,
)


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


LIB_PREFIX = "BSinMeasurementTheory/"


def github_blob_url(rel: str, first: int | None = None, last: int | None = None) -> str:
    url = f"{GITHUB_URL}/blob/main/{rel}"
    if first is not None and last is not None:
        url += f"\\#L{first}-L{last}"
    return url


def lean_display_path(rel: str) -> str:
    if rel.startswith(LIB_PREFIX):
        return rel[len(LIB_PREFIX) :]
    return rel


def lean_label_tex(label: str, github_rel: str | None, first: int, last: int, line_count: int) -> str:
    if not github_rel:
        return f"\\textcolor{{green!40!black}}{{\\textbf{{{label}}}}}"
    if first == 1 and last == line_count:
        url = github_blob_url(github_rel)
    else:
        url = github_blob_url(github_rel, first, last)
    return f"\\leansourcehref{{{url}}}{{{label}}}"


def lean_block_latex(code: str, listing_name: str, github_rel: str | None = None) -> str:
    rel_path, line_count = write_listing(code, listing_name)
    ranges = chunk_line_ranges(line_count, LISTING_CHUNK_LINES)
    parts: list[str] = []
    for first, last in ranges:
        label = "Lean 4 source"
        if github_rel:
            label += f" \\texttt{{{escape_latex_caption(lean_display_path(github_rel))}}}"
        if not (first == 1 and last == line_count):
            label += f" (lines {first}--{last})"
        firstlast = "" if first == 1 and last == line_count else f",firstline={first},lastline={last}"
        parts.append(
            "\\vspace{0.5\\baselineskip}\n"
            f"\\noindent{lean_label_tex(label, github_rel, first, last, line_count)}"
            "\\par\\vspace{0.25\\baselineskip}\n"
            f"\\lstinputlisting[style=leanbox{firstlast}]{{{rel_path}}}\n"
            "\\vspace{0.5\\baselineskip}\n\n"
        )
    return "".join(parts)


def parse_figure_captions(text: str) -> list[str]:
    return [m.group(1).strip() for m in FIGURE_CAPTION_RE.finditer(text)]


def escape_latex_caption(text: str) -> str:
    out: list[str] = []
    for ch in text:
        if ch in "&%$#_{}":
            out.append(f"\\{ch}" if ch != "}" else "\\}")
        elif ch == "~":
            out.append(r"\textasciitilde{}")
        elif ch == "^":
            out.append(r"\textasciicircum{}")
        elif ch == "\\":
            out.append(r"\textbackslash{}")
        else:
            out.append(ch)
    return "".join(out)


def extract_lean_titles(text: str) -> dict[str, str]:
    titles: dict[str, str] = {}
    lean_starts = [m.start() for m in re.finditer(r"^```lean\s*$", text, re.MULTILINE)]
    for idx, pos in enumerate(lean_starts):
        module = None
        for line in reversed(text[:pos].rstrip("\n").splitlines()[-6:]):
            stripped = line.strip()
            path_m = LEAN_PATH_RE.match(stripped)
            if path_m:
                module = path_m.group(1)
                break
            heading_m = LEAN_MODULE_RE.match(stripped)
            if heading_m:
                module = heading_m.group(1)
                break
        titles[f"LEANINCLUDE{idx:03d}"] = module or f"module-{idx + 1}"
    return titles


def replace_fences(
    text: str, figure_captions: list[str], lean_titles: dict[str, str] | None = None
) -> tuple[str, dict[str, str]]:
    lean_titles = lean_titles if lean_titles is not None else extract_lean_titles(text)
    placeholders: dict[str, str] = {}
    lean_idx = 0
    other_idx = 0
    figure_idx = 0

    def repl(match: re.Match[str]) -> str:
        nonlocal lean_idx, other_idx, figure_idx
        lang = match.group(1).strip().lower()
        body = match.group(2)
        if lang == "lean":
            key = f"LEANINCLUDE{lean_idx:03d}"
            module = lean_titles.get(key, f"module-{lean_idx}")
            lean_idx += 1
            github_rel = module if module.startswith("BSinMeasurementTheory") else None
            safe_name = module.replace("/", "-")
            if not safe_name.endswith(".lean"):
                safe_name += ".lean"
            placeholders[key] = lean_block_latex(body, safe_name, github_rel)
            return f"\n\n{key}\n\n"
        if lang == "mermaid":
            key = f"FIGINCLUDE{other_idx:03d}"
            rel_path, hotspots = render_mermaid(body, figure_idx)
            if figure_idx < len(figure_captions):
                caption = figure_captions[figure_idx]
            else:
                caption = f"Syllabus diagram {figure_idx + 1}."
            label = f"fig:bsmt-{figure_idx + 1:02d}"
            figure_idx += 1
            other_idx += 1
            cap = escape_latex_caption(caption)
            # Keep syllabus Figure 1 (and every other mermaid) from floating
            # past the next heading; solution maps stay under Solution.
            placement = "H"
            placeholders[key] = (
                f"\\begin{{figure}}[{placement}]\n\\centering\n"
                f"{figure_include_latex(rel_path, hotspots)}"
                f"\\caption{{{cap}}}\n"
                f"\\label{{{label}}}\n"
                "\\end{figure}\n"
            )
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
    # Numbered top-level sections start on a new page.  \section* (TOC/LOF)
    # is emitted in the title page, not here.
    latex = latex.replace(r"\section{", r"\clearpage\section{")
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
        \\listoffigures
        """
    ).strip()


def main() -> int:
    if not SRC.is_file():
        print(f"error: missing {SRC}; run scripts/generate_arxiv_with_code.sh first", file=sys.stderr)
        return 1
    for d in (LISTINGS_DIR, FIGURES_DIR):
        if d.exists():
            for path in d.iterdir():
                if path.is_file():
                    path.unlink()
        d.mkdir(parents=True, exist_ok=True)

    body = drop_github_nav(SRC.read_text(encoding="utf-8"))
    figure_captions = parse_figure_captions(body)
    lean_titles = extract_lean_titles(body)
    body = strip_html_comments(body)
    abstract_md, body = extract_abstract(body)
    body = strip_manual_section_numbers(body)
    body = github_math_to_tex(body)
    body, placeholders = replace_fences(body, figure_captions, lean_titles)

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
    n_figures = sum(1 for p in FIGURES_DIR.glob("*.png"))
    print(
        f"wrote {OUT.relative_to(ROOT)} ({OUT.stat().st_size:,} bytes, "
        f"{n_listings} listings, {n_figures} mermaid figures)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
