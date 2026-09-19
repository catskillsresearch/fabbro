import Mathlib
import BSinMeasurementTheory.Course21120.TaylorExpansion

namespace Course21120Taylor

theorem term1_eq : (1 / 2 : ℚ) ^ 3 / 3 = 1 / 24 := by norm_num
theorem term2_eq : (1 / 2 : ℚ) ^ 5 / 5 = 1 / 160 := by norm_num
theorem term3_eq : 5 * (1 / 2 : ℚ) ^ 7 / 42 = 5 / 5376 := by norm_num
theorem term4_eq : 5 * (1 / 2 : ℚ) ^ 9 / 54 = 5 / 27648 := by norm_num

/-- The exact rational value of $T_9(1/2)$ is $34997 / 967680$. -/
theorem T9_half_eq : T9 (1 / 2) = 34997 / 967680 := by
  dsimp [T9]
  norm_num

/-- $T_9(1/2)$ lies strictly between $0.03615$ and $0.03625$. -/
theorem T9_half_rounds_to_0_0362 :
    (3615 : ℚ) / 100000 < T9 (1 / 2) ∧ T9 (1 / 2) < 3625 / 100000 := by
  rw [T9_half_eq]
  norm_num

/-- Explicit distance to $0.0362$ is less than $0.00005$. -/
theorem T9_half_close_to_0_0362 :
    T9 (1 / 2) - 362 / 10000 < 5 / 100000 ∧
    362 / 10000 - T9 (1 / 2) < 5 / 100000 := by
  rw [T9_half_eq]
  norm_num

#eval (1.0 / 24.0 : Float)
#eval (1.0 / 160.0 : Float)
#eval (5.0 / 5376.0 : Float)
#eval (5.0 / 27648.0 : Float)
#eval (34997.0 / 967680.0 : Float)

end Course21120Taylor
