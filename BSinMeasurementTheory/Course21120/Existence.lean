import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith

open Real

namespace Course21120

/-- Pointwise comparison: the integrand is dominated by $1/(1+t^2)$,
which is the majorant used to get absolute convergence of the improper
integral. -/
theorem abs_integrand_le (t : ℝ) :
    |sin (t ^ 2) / (1 + t ^ 2)| ≤ 1 / (1 + t ^ 2) := by
  have hpos : 0 < 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  rw [abs_div, abs_of_pos hpos]
  exact div_le_div_of_nonneg_right (abs_sin_le_one _) hpos.le

end Course21120
