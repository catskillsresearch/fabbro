[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/fabbro/build.yml?label=Lean%204)](https://github.com/catskillsresearch/fabbro/actions/workflows/build.yml)

# BS in Measurement Theory

**Carnegie Mellon University** — Department of Mathematical Sciences

**Student.** Giovanni Fabbro  
**Capstone.** Dana Scott, *Measurement Structures and Linear Inequalities* (1964)  
**Form.** One problem per course, in syllabus order. Each problem is built to require the full toolkit of its course — not a single technique in isolation. Solutions are written in English and then formalized in Lean 4 / Mathlib, without `sorry`, `admit`, or extra axioms.

This is a reconstructed undergraduate path through the CMU 21-xxx catalog, sequenced so that Scott’s finite-dimensional theorems (1.1–4.1) and their extension to infinite Boolean algebras can be proved end to end.

---

## Syllabus

| Phase | Course | Title | Role toward Scott (1964) |
| :---: | :---: | :--- | :--- |
| 1 | [21-120 / 21-122](courses/21-120-21-122.md) | Differential and Integral Calculus / Integration and Approximation | FTC, comparison, integration by parts, Taylor remainder — the analytic toolkit later problems assume |
| 1 | [21-127](courses/21-127.md) | Concepts of Mathematics | Equivalence relations, explicit bijections, induction, and spotting a false claim |
| 1 | [21-241](courses/21-241.md) | Matrices and Linear Transformations | Bases, dual bases, and the vector-space language of Theorem 1.1 |
| 1 | [21-228](courses/21-228.md) | Discrete Mathematics | Permutations, multisets, and the combinatorial counting behind Theorems 1.2 and 3.2 |
| 2 | [21-355](courses/21-355.md) | Principles of Real Analysis I | Completeness, limsup/liminf, and compactness proved from axioms |
| 2 | [21-373](courses/21-373.md) | Algebraic Structures | Atoms and characteristic functions of finite Boolean algebras — the finite case of Theorem 4.1 |
| 2 | [21-321](courses/21-321.md) | Interactive Theorem Proving | Formal statements of Theorems 1.1 and 1.2, and a Lean proof that they are equivalent |
| 3 | [21-292](courses/21-292.md) | Operations Research I | Simplex and LP duality, deriving Kuhn–Tucker / Theorem 1.1 from the dual rather than the other way around |
| 3 | [21-329](courses/21-329.md) | Set Theory | Zorn’s lemma, ultrafilters, and cardinal arithmetic — the set-theoretic engine of the infinite case |
| 4 | [21-651](courses/21-651.md) | General Topology | Stone spaces, compactness via Tychonoff, and Stone’s representation theorem |
| 4 | [21-720](courses/21-720.md) | Measure and Integration | Riesz representation: a positive functional on \(C(X)\) becomes a regular Borel measure, then a finitely additive measure on \(B\) |
| 5 | [21-640](courses/21-640.md) | Introduction to Functional Analysis | Hahn–Banach extension of the functional on simple functions — the step Scott cites and leaves unproved |
| 6 | [21-410 / 21-599](courses/21-410-21-599.md) | Independent Study | Full reconstruction of the infinite-algebra extension of Theorem 4.1, citing the four prior solutions as lemmas |
| 6 | [21-322](courses/21-322.md) | Topics in Formal Mathematics | Proof that the finite atomic picture of 21-373 is exactly what the Phase 4–6 Stone machinery reduces to |

---

## Phase map

| Phase | Theme | Courses |
| :---: | :--- | :--- |
| 1 | Language and linear structure | [21-120/122](courses/21-120-21-122.md), [21-127](courses/21-127.md), [21-241](courses/21-241.md), [21-228](courses/21-228.md) |
| 2 | Analysis, algebras, and formal proof | [21-355](courses/21-355.md), [21-373](courses/21-373.md), [21-321](courses/21-321.md) |
| 3 | Duality and set theory | [21-292](courses/21-292.md), [21-329](courses/21-329.md) |
| 4 | Stone spaces and measures | [21-651](courses/21-651.md), [21-720](courses/21-720.md) |
| 5 | The missing extension | [21-640](courses/21-640.md) |
| 6 | Assembly and consistency check | [21-410/599](courses/21-410-21-599.md), [21-322](courses/21-322.md) |

---

## Standing requirements

Every course problem is solved in two layers:

1. An English mathematical argument.
2. A Lean 4 formalization using Mathlib, with numerical examples re-checked in Lean when they appear.

The formalizations live in the `BSinMeasurementTheory` library (Lean `v4.34.0-rc1`). Each snippet is a self-contained module under [`BSinMeasurementTheory/`](BSinMeasurementTheory/); [`BSinMeasurementTheory.lean`](BSinMeasurementTheory.lean) imports all of them. Build with `lake exe cache get && lake build`.

21-322 is opportunistic: take it in a term that overlaps real analysis or order theory in Lean. The standing problem is independent of that term’s advertised topic.
