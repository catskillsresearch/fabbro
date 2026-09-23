import Mathlib.Data.Rat.Defs
import BSinMeasurementTheory.Course21120.TaylorEstimate
import BSinMeasurementTheory.Course21120.TaylorError

namespace Course21120Taylor

/-- Term-by-term values used in the degree-9 estimate at \(1/2\). -/
theorem summary_terms :
    (1 / 2 : ℚ) ^ 3 / 3 = 1 / 24 ∧
    (1 / 2 : ℚ) ^ 5 / 5 = 1 / 160 ∧
    5 * (1 / 2 : ℚ) ^ 7 / 42 = 5 / 5376 ∧
    5 * (1 / 2 : ℚ) ^ 9 / 54 = 5 / 27648 :=
  ⟨term1_eq, term2_eq, term3_eq, term4_eq⟩

/-- Exact rational value of the degree-9 truncation. -/
theorem summary_exact : T9 (1 / 2) = 34997 / 967680 :=
  T9_half_exact

/-- The truncation rounds to four decimals as \(0.0362\). -/
theorem summary_rounding :
    (3615 : ℚ) / 100000 < T9 (1 / 2) ∧ T9 (1 / 2) < 3625 / 100000 :=
  T9_half_rounds_to_0_0362

/-- Remainder bound used for the four-decimal claim. -/
theorem summary_error : truncation_error = 101 / 2703360 ∧ truncation_error < 1 / 10000 :=
  ⟨truncation_error_eq, truncation_error_lt⟩

end Course21120Taylor
