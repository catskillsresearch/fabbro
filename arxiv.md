# Formalization of a BS in Measurement Theory

**Authors.** Lars Warren Ericson (independent researcher, d/b/a Catskills
Research Company; lars.ericson@catskillsresearch.com).
**Technical report.** CMU-CS-26-XXX, School of Computer Science, Carnegie
Mellon University, Pittsburgh, PA 15213.
**Source paper.** Dana S. Scott, *Measurement Structures and Linear
Inequalities*, Journal of Mathematical Psychology 1 (1964), 233–247.
**Repository.** https://github.com/catskillsresearch/fabbro
**Cross-archive.** This report will also be deposited on arXiv in cs.LO and
math.LO.

---

## Abstract

This report presents a reconstructed Carnegie Mellon undergraduate path
through the Mathematical Sciences 21-xxx catalog, sequenced so that Dana
Scott's 1964 measurement theorems (1.1--4.1) and their extension to infinite
Boolean algebras can be proved end to end. Each course contributes one
problem that requires the full toolkit of that course rather than a single
technique in isolation. Solutions are written in English and then formalized
in Lean 4 / Mathlib. The accompanying library `BSinMeasurementTheory` is
sorry-free under the pinned toolchain `leanprover/lean4:v4.34.0-rc1` and
introduces no project axioms beyond Mathlib's classical footprint. Large-language-model
assistance was used in drafting solutions, but every accepted declaration is
checked by Lean's kernel. The complete source and a reproducible build
pipeline are publicly available with this report.

## Introduction

Measurement theory asks when qualitative comparisons can be represented by
real numbers. Scott's 1964 paper organizes several such representation
questions around a finite theory of homogeneous linear inequalities, with
applications to intransitive indifference, ordered utility differences, and
subjective probability. The infinite direction, which Scott announced but
did not carry out, runs through Stone spaces, positive functionals,
Hahn--Banach extension, and Riesz representation.

The pedagogical claim of this report is that a complete undergraduate
mathematics major at Carnegie Mellon already contains the pieces of that
argument, if the courses are taken in the right order and each is asked to
do real work. The syllabus below is that ordering. It is framed as a
Bachelor of Science in Measurement Theory: not a new degree program, but a
reading of the existing catalog as a single connected proof.

The student of record for the problem set is Giovanni Fabbro. Each problem
is built so that quoting a theorem from a later course is not available: the
calculus problem uses the fundamental theorem, comparison, and Taylor
remainders; the linear-algebra problem speaks the dual-space language of
Scott's Theorem 1.1; the discrete-mathematics problem is the combinatorial
counting behind Theorems 1.2 and 3.2; and the independent-study problem
assembles set theory, topology, measure, and functional analysis into the
infinite extension of Theorem 4.1.

The formalizations live in the Lean library `BSinMeasurementTheory`. Each
course snippet is a self-contained module. The root file
`BSinMeasurementTheory.lean` imports all of them. The English arguments occupy the body of this report, in syllabus order,
with each Lean module inlined next to the claim it proves. The appendix
is an index of filenames, each linking to the source on GitHub.

## Syllabus

| Phase | Course | Title | Role toward Scott (1964) |
| :---: | :---: | :--- | :--- |
| 1 | 21-120 / 21-122 | Differential and Integral Calculus / Integration and Approximation | FTC, comparison, integration by parts, Taylor remainder |
| 1 | 21-127 | Concepts of Mathematics | Equivalence relations, explicit bijections, induction |
| 1 | 21-241 | Matrices and Linear Transformations | Bases, dual bases, and the vector-space language of Theorem 1.1 |
| 1 | 21-228 | Discrete Mathematics | Permutations, multisets, and the counting behind Theorems 1.2 and 3.2 |
| 2 | 21-355 | Principles of Real Analysis I | Completeness, limsup/liminf, and compactness from axioms |
| 2 | 21-373 | Algebraic Structures | Atoms and characteristic functions of finite Boolean algebras |
| 2 | 21-321 | Interactive Theorem Proving | Formal statements of Theorems 1.1 and 1.2, and their equivalence |
| 3 | 21-292 | Operations Research I | Simplex and LP duality, deriving Kuhn--Tucker / Theorem 1.1 from the dual |
| 3 | 21-329 | Set Theory | Zorn's lemma, ultrafilters, and cardinal arithmetic |
| 4 | 21-651 | General Topology | Stone spaces, compactness via Tychonoff, Stone representation |
| 4 | 21-720 | Measure and Integration | Riesz representation and the induced finitely additive measure on $B$ |
| 5 | 21-640 | Introduction to Functional Analysis | Hahn--Banach extension, the step Scott cites and leaves unproved |
| 6 | 21-410 / 21-599 | Independent Study | Full reconstruction of the infinite-algebra extension of Theorem 4.1 |
| 6 | 21-322 | Topics in Formal Mathematics | Proof that the finite atomic picture is what the infinite machinery reduces to |

The conceptual buildup of that sequence is Figure 1. The Mathlib
subsections required to read each course's Lean are Figure 2. The Lean
library does not import across courses.

<!-- figure-caption: Conceptual buildup of the reconstructed 21-xxx syllabus toward Scott (1964). Blue nodes are courses, grouped by phase. Course nodes are hyperlinked to the corresponding section. -->
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

  click C120 "courses/21-120-21-122.md" "21-120 / 21-122"
  click C127 "courses/21-127.md" "21-127"
  click C241 "courses/21-241.md" "21-241"
  click C228 "courses/21-228.md" "21-228"
  click C355 "courses/21-355.md" "21-355"
  click C373 "courses/21-373.md" "21-373"
  click C321 "courses/21-321.md" "21-321"
  click C292 "courses/21-292.md" "21-292"
  click C329 "courses/21-329.md" "21-329"
  click C651 "courses/21-651.md" "21-651"
  click C720 "courses/21-720.md" "21-720"
  click C640 "courses/21-640.md" "21-640"
  click C410 "courses/21-410-21-599.md" "21-410 / 21-599"
  click C322 "courses/21-322.md" "21-322"
```

<!-- figure-caption: Mathlib subsections required to read each course. Orange nodes are Mathlib; blue nodes are courses. Course nodes are hyperlinked to the corresponding section. -->
```mermaid
%%{init: {"flowchart": {"htmlLabels": true, "nodeSpacing": 18, "rankSpacing": 50}}}%%
flowchart LR
  classDef course fill:#dbeafe,stroke:#1d4ed8,color:#1e3a8a,stroke-width:1.2px
  classDef mathlib fill:#fff7ed,stroke:#c2410c,color:#7c2d12,stroke-width:1.2px

  subgraph ML["Mathlib subsections"]
    direction TB
    style ML fill:#fff7ed,stroke:#c2410c,stroke-width:2px
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
    style CR fill:#eff6ff,stroke:#1d4ed8,stroke-width:2px
    C120["21-120 / 21-122<br/>Differential and Integral Calculus / Integration and Approximation"]:::course
    C127["21-127<br/>Concepts of Mathematics"]:::course
    C241["21-241<br/>Matrices and Linear Transformations"]:::course
    C228["21-228<br/>Discrete Mathematics"]:::course
    C355["21-355<br/>Principles of Real Analysis I"]:::course
    C373["21-373<br/>Algebraic Structures"]:::course
    C321["21-321<br/>Interactive Theorem Proving"]:::course
    C292["21-292<br/>Operations Research I"]:::course
    C329["21-329<br/>Set Theory"]:::course
    C651["21-651<br/>General Topology"]:::course
    C720["21-720<br/>Measure and Integration"]:::course
    C640["21-640<br/>Introduction to Functional Analysis"]:::course
    C410["21-410 / 21-599<br/>Independent Study"]:::course
    C322["21-322<br/>Topics in Formal Mathematics"]:::course
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

  click C120 "courses/21-120-21-122.md" "21-120 / 21-122"
  click C127 "courses/21-127.md" "21-127"
  click C241 "courses/21-241.md" "21-241"
  click C228 "courses/21-228.md" "21-228"
  click C355 "courses/21-355.md" "21-355"
  click C373 "courses/21-373.md" "21-373"
  click C321 "courses/21-321.md" "21-321"
  click C292 "courses/21-292.md" "21-292"
  click C329 "courses/21-329.md" "21-329"
  click C651 "courses/21-651.md" "21-651"
  click C720 "courses/21-720.md" "21-720"
  click C640 "courses/21-640.md" "21-640"
  click C410 "courses/21-410-21-599.md" "21-410 / 21-599"
  click C322 "courses/21-322.md" "21-322"
```

Every course problem is solved in two layers: an English mathematical
argument, and a Lean 4 formalization using Mathlib, with numerical examples
re-checked in Lean when they appear. Course 21-322 is opportunistic: it
should be taken in a term that overlaps real analysis or order theory in
Lean, but the standing problem is independent of that term's advertised
topic.

The remainder of this report is the problem set itself, in syllabus order.

## References

**[Sco64]** Dana S. Scott, *Measurement Structures and Linear Inequalities*,
Journal of Mathematical Psychology 1 (1964), 233–247.

**[KP59]** L. G. Kraft, J. D. Pratt, and A. Seidenberg, *Intuitive Probability
on Finite Sets*, Annals of Mathematical Statistics 30 (1959), 408–419.

**[Kel59]** J. L. Kelley, *Measures on Boolean Algebras*, Pacific Journal of
Mathematics 9 (1959), 1165–1177.
