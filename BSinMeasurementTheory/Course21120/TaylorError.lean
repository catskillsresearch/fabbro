import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import BSinMeasurementTheory.Course21120.TaylorExpansion

namespace Course21120Taylor

/-- Alternating-series tail bound
$|R(0.5)| \le (101 / 1320) \cdot (1/2)^{11}$. -/
def truncation_error : ℚ := (101 / 1320) * (1 / 2) ^ 11

theorem truncation_error_eq : truncation_error = 101 / 2703360 := by
  dsimp [truncation_error]
  norm_num

/-- The truncation error is strictly less than $10^{-4}$. -/
theorem truncation_error_lt : truncation_error < 1 / 10000 := by
  rw [truncation_error_eq]
  norm_num

#eval (101.0 / 2703360.0 : Float)

end Course21120Taylor
