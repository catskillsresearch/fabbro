/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Real intervalIntegral MeasureTheory

/-!
# Challenge — Course 21-120 / 21-122

Mathlib-only restatement of the calculus capstone headline theorems.
Proofs are deliberate `sorry` holes for Palomar Comparator.

Definitions match `BSinMeasurementTheory.Course21120.{FTC,TailBound,TaylorExpansion,TaylorError}`.
-/

namespace Course21120FTC

/-- Definition of f(x) = ∫₀ˣ sin(t²) / (1 + t²) dt -/
noncomputable def f (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, sin (t ^ 2) / (1 + t ^ 2)

/-- (a) Part 2: f'(x) = sin(x²) / (1 + x²). -/
theorem part_a_deriv (x : ℝ) : deriv f x = sin (x ^ 2) / (1 + x ^ 2) := by
  sorry

end Course21120FTC

namespace Course21120

/-- Combined comparison + integration-by-parts bound:
$|f(\infty)| \le \arctan M + 1/(M(1+M^2))$. -/
noncomputable def limAbsBound (M : ℝ) : ℝ :=
  arctan M + 1 / (M * (1 + M ^ 2))

/-- At $M = 1$ the bound is exactly $\pi/4 + 1/2$. -/
theorem limAbsBound_one : limAbsBound 1 = π / 4 + 1 / 2 := by
  sorry

end Course21120

namespace Course21120Taylor

/-- Formal indefinite integral of a monomial $c\,t^n$, evaluated at $x$
(vanishing at $0$). -/
def integrateMonomial (c : ℚ) (n : ℕ) (x : ℚ) : ℚ :=
  c * x ^ (n + 1) / (n + 1)

/-- Alternating-series / integrated remainder bound
$|R_f(1/2)| \le \int_0^{1/2} R_{\mathrm{integrand}}(t)\,dt$. -/
def truncation_error : ℚ := integrateMonomial (101 / 120) 10 (1 / 2)

/-- The truncation error is strictly less than $10^{-4}$. -/
theorem truncation_error_lt : truncation_error < 1 / 10000 := by
  sorry

end Course21120Taylor
