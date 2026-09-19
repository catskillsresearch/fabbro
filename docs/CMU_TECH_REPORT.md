# CMU School of Computer Science technical report

Publication checklist for *Formalization of a BS in Measurement Theory*.

## Report metadata

- **Series:** Carnegie Mellon University School of Computer Science Technical
  Report
- **Number:** `CMU-CS-26-XXX` (placeholder)
- **Date:** September 2026
- **Authors:** Lars Warren Ericson
- **Institutional address:** School of Computer Science, Carnegie Mellon
  University, Pittsburgh, PA 15213
- **arXiv cross-archive:** `cs.LO` / `math.LO`

Lars Warren Ericson is an independent researcher, d/b/a Catskills Research
Company (`lars.ericson@catskillsresearch.com`).

## Build

```bash
lake exe cache get
lake build
bash scripts/build_arxiv_pdf.sh
```

The build produces:

- `arxiv.pdf` — CMU-formatted report PDF;
- `arxiv.tex` — generated complete LaTeX source (gitignored);
- `lean-listings/` — generated report inputs (gitignored);
- `figures/` — live Mermaid diagrams rendered to PNG (gitignored; never PDF);
- `dist/arxiv_submit.zip` — pdfLaTeX-ready cross-archive bundle, including
  `cmu-titlepage2.sty` and `figures/*.png`.

The title page uses the report-mode layout from CMU's
`cmu-titlepage2.sty`. The same generated document is intended for the CMU
series and arXiv cross-archive.

## Before public release

1. Replace every `CMU-CS-26-XXX` occurrence with the assigned CMU report
   number.
2. Confirm the author, September 2026 date, and correspondence email.
3. Run `lake build` and `bash scripts/build_arxiv_pdf.sh`.
4. Inspect the cover, abstract, table of contents, list of figures, numbered
   figure captions, syllabus, course chapters, acknowledgments, references,
   and Lean module index (filenames and GitHub links, not source reprints).
5. Upload `dist/arxiv_submit.zip` only after deleting prior arXiv submission
   files so the source set is replaced rather than merged.
