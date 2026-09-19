[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/fabbro/build.yml?label=Lean%204)](https://github.com/catskillsresearch/fabbro/actions/workflows/build.yml)

# Formalization of a BS in Measurement Theory

The accompanying report, *Formalization of a BS in Measurement Theory*, is
by **Lars Warren Ericson** (independent researcher, d/b/a Catskills Research
Company). It is being prepared for the Carnegie Mellon University School of
Computer Science Technical Report series as **CMU-CS-26-XXX**, with
cross-archival to arXiv under cs.LO and math.LO.

This repository reconstructs an undergraduate path through the CMU 21-xxx
catalog, sequenced so that Dana Scott's 1964 measurement theorems (1.1--4.1)
and their extension to infinite Boolean algebras can be proved end to end.
Each course contributes one problem that requires the full toolkit of that
course. Solutions are written in English and formalized in Lean 4 / Mathlib.

The student of record for the problem set is Giovanni Fabbro. The capstone
source is Dana S. Scott, *Measurement Structures and Linear Inequalities*
(J. Math. Psychology 1 (1964), 233–247).

The pin is `leanprover/lean4:v4.34.0-rc1`.

## Report and archival files

| File | Role |
|---|---|
| `arxiv.md` | CMU technical-report narrative and syllabus |
| `arxiv.pdf` | Built CMU report PDF for cross-archival |
| `docs/CMU_TECH_REPORT.md` | Report-number, build, and release checklist |
| `courses/` | Per-course English solutions |
| `BSinMeasurementTheory/` | Sorry-free Lean 4 formalizations |
| `BSinMeasurementTheory.lean` | Root importer |

## Syllabus

| Phase | Course | Title | Role toward Scott (1964) |
| :---: | :---: | :--- | :--- |
| 1 | [21-120 / 21-122](courses/21-120-21-122.md) | Differential and Integral Calculus / Integration and Approximation | FTC, comparison, integration by parts, Taylor remainder |
| 1 | [21-127](courses/21-127.md) | Concepts of Mathematics | Equivalence relations, explicit bijections, induction |
| 1 | [21-241](courses/21-241.md) | Matrices and Linear Transformations | Bases, dual bases, and the vector-space language of Theorem 1.1 |
| 1 | [21-228](courses/21-228.md) | Discrete Mathematics | Permutations, multisets, and the counting behind Theorems 1.2 and 3.2 |
| 2 | [21-355](courses/21-355.md) | Principles of Real Analysis I | Completeness, limsup/liminf, and compactness from axioms |
| 2 | [21-373](courses/21-373.md) | Algebraic Structures | Atoms and characteristic functions of finite Boolean algebras |
| 2 | [21-321](courses/21-321.md) | Interactive Theorem Proving | Formal statements of Theorems 1.1 and 1.2, and their equivalence |
| 3 | [21-292](courses/21-292.md) | Operations Research I | Simplex and LP duality, deriving Kuhn--Tucker / Theorem 1.1 from the dual |
| 3 | [21-329](courses/21-329.md) | Set Theory | Zorn's lemma, ultrafilters, and cardinal arithmetic |
| 4 | [21-651](courses/21-651.md) | General Topology | Stone spaces, compactness via Tychonoff, Stone representation |
| 4 | [21-720](courses/21-720.md) | Measure and Integration | Riesz representation and the induced finitely additive measure on \(B\) |
| 5 | [21-640](courses/21-640.md) | Introduction to Functional Analysis | Hahn--Banach extension, the step Scott cites and leaves unproved |
| 6 | [21-410 / 21-599](courses/21-410-21-599.md) | Independent Study | Full reconstruction of the infinite-algebra extension of Theorem 4.1 |
| 6 | [21-322](courses/21-322.md) | Topics in Formal Mathematics | Proof that the finite atomic picture is what the infinite machinery reduces to |

The conceptual buildup of that sequence is Figure 1. The Mathlib
subsections required to read each course's Lean are Figure 2. The Lean
library does not import across courses.

<!-- figure-caption: Conceptual buildup of the reconstructed 21-xxx syllabus toward Scott (1964). Blue nodes are courses, grouped by phase. -->
```mermaid
%%{init: {"flowchart": {"htmlLabels": true, "nodeSpacing": 24, "rankSpacing": 40}}}%%
flowchart TB
  classDef course fill:#dbeafe,stroke:#1d4ed8,color:#1e3a8a,stroke-width:1.2px

  subgraph P1["Phase 1"]
    C120["21-120 / 21-122<br/>Calculus"]:::course
    C127["21-127<br/>Concepts of Mathematics"]:::course
    C241["21-241<br/>Matrices and Linear Transformations"]:::course
    C228["21-228<br/>Discrete Mathematics"]:::course
  end

  subgraph P2["Phase 2"]
    C355["21-355<br/>Real Analysis"]:::course
    C373["21-373<br/>Algebraic Structures"]:::course
    C321["21-321<br/>Interactive Theorem Proving"]:::course
  end

  subgraph P3["Phase 3"]
    C292["21-292<br/>Operations Research"]:::course
    C329["21-329<br/>Set Theory"]:::course
  end

  subgraph P4["Phase 4"]
    C651["21-651<br/>General Topology"]:::course
    C720["21-720<br/>Measure and Integration"]:::course
  end

  subgraph P5["Phase 5"]
    C640["21-640<br/>Functional Analysis"]:::course
  end

  subgraph P6["Phase 6"]
    C410["21-410 / 21-599<br/>Independent Study"]:::course
    C322["21-322<br/>Formal Mathematics"]:::course
  end

  C241 --> C292
  C241 --> C321
  C228 --> C321
  C127 --> C321
  C292 --> C321
  C120 --> C355
  C355 --> C720
  C373 --> C651
  C329 --> C651
  C651 --> C720
  C241 --> C640
  C355 --> C640
  C329 --> C410
  C651 --> C410
  C720 --> C410
  C640 --> C410
  C373 --> C322
  C321 --> C322
  C410 --> C322
```

<!-- figure-caption: Mathlib subsections required to read each course. Orange nodes are Mathlib; blue nodes are courses. -->
```mermaid
%%{init: {"flowchart": {"htmlLabels": false, "nodeSpacing": 18, "rankSpacing": 50}}}%%
flowchart LR
  classDef course fill:#dbeafe,stroke:#1d4ed8,color:#1e3a8a,stroke-width:1.2px
  classDef mathlib fill:#fff7ed,stroke:#c2410c,color:#7c2d12,stroke-width:1.2px

  subgraph ML["Mathlib subsections"]
    direction TB
    mlCalc["Analysis.Calculus"]:::mathlib
    mlInt["MeasureTheory.Integral"]:::mathlib
    mlTrig["Analysis.SpecialFunctions"]:::mathlib
    mlLimsup["Order.LiminfLimsup"]:::mathlib
    mlIPS["Analysis.InnerProductSpace"]:::mathlib
    mlNS["Analysis.NormedSpace"]:::mathlib
    mlMeas["MeasureTheory"]:::mathlib
    mlCpct["Topology.Compactness"]:::mathlib
    mlCMap["Topology.ContinuousMap"]:::mathlib
    mlLin["LinearAlgebra"]:::mathlib
    mlLMap["Algebra.Module.LinearMap"]:::mathlib
    mlRing["Algebra.Order.Ring"]:::mathlib
    mlBig["Algebra.BigOperators"]:::mathlib
    mlBA["Order.BooleanAlgebra"]:::mathlib
    mlZorn["Order.Zorn"]:::mathlib
    mlFilt["Order.Filter"]:::mathlib
    mlRat["Data.Rat / Quotient"]:::mathlib
    mlWF["Order.WellFounded"]:::mathlib
    mlPerm["Data.Fintype.Perm"]:::mathlib
    mlCard["SetTheory.Cardinal"]:::mathlib
  end

  subgraph CR["Courses"]
    direction TB
    C120["21-120 / 21-122"]:::course
    C127["21-127"]:::course
    C241["21-241"]:::course
    C228["21-228"]:::course
    C355["21-355"]:::course
    C373["21-373"]:::course
    C321["21-321"]:::course
    C292["21-292"]:::course
    C329["21-329"]:::course
    C651["21-651"]:::course
    C720["21-720"]:::course
    C640["21-640"]:::course
    C410["21-410 / 21-599"]:::course
    C322["21-322"]:::course
  end

  mlCalc --> C120
  mlInt --> C120
  mlTrig --> C120
  mlRat --> C127
  mlWF --> C127
  mlLin --> C241
  mlIPS --> C241
  mlLMap --> C241
  mlPerm --> C228
  mlBig --> C228
  mlLimsup --> C355
  mlCpct --> C355
  mlBA --> C373
  mlBig --> C373
  mlLMap --> C321
  mlRing --> C321
  mlBig --> C321
  mlRing --> C292
  mlLin --> C292
  mlZorn --> C329
  mlFilt --> C329
  mlCard --> C329
  mlBA --> C651
  mlCMap --> C651
  mlCpct --> C651
  mlCMap --> C720
  mlBA --> C720
  mlMeas --> C720
  mlNS --> C640
  mlLMap --> C640
  mlBA --> C410
  mlBig --> C410
  mlMeas --> C410
  mlBA --> C322
  mlCMap --> C322
  mlMeas --> C322
```

## Build

```bash
lake exe cache get
lake build
bash scripts/build_arxiv_pdf.sh
```

`lake build` typechecks `BSinMeasurementTheory`. The PDF script regenerates
`arxiv.tex` from `arxiv.md` and the course notes, compiles the CMU report
cover, and writes `dist/arxiv_submit.zip`.
