import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import BSinMeasurementTheory.Course21120.TaylorExpansion

namespace Course21120Taylor

/-! ### Estimation at $x = 1/2$

Start from `T9_simplified`, evaluate each summand, then combine. -/

/-- Specialize the integrated expansion at $x = 1/2$. -/
theorem T9_at_half :
    T9 (1 / 2) =
      (1 / 2 : ℚ) ^ 3 / 3 - (1 / 2) ^ 5 / 5 + 5 * (1 / 2) ^ 7 / 42 -
        5 * (1 / 2) ^ 9 / 54 :=
  T9_simplified (1 / 2)

/-- First summand of `T9_simplified` at $1/2$: $(1/2)^3/3 = 1/24$. -/
theorem term1_eq : (1 / 2 : ℚ) ^ 3 / 3 = 1 / 24 := by norm_num

/-- Second summand: $(1/2)^5/5 = 1/160$. -/
theorem term2_eq : (1 / 2 : ℚ) ^ 5 / 5 = 1 / 160 := by norm_num

/-- Third summand: $5(1/2)^7/42 = 5/5376$. -/
theorem term3_eq : 5 * (1 / 2 : ℚ) ^ 7 / 42 = 5 / 5376 := by norm_num

/-- Fourth summand: $5(1/2)^9/54 = 5/27648$. -/
theorem term4_eq : 5 * (1 / 2 : ℚ) ^ 9 / 54 = 5 / 27648 := by norm_num

/-- $T_9(1/2)$ as the sum of the four evaluated summands from `T9_simplified`. -/
theorem T9_half_eq :
    T9 (1 / 2) = (1 : ℚ) / 24 - 1 / 160 + 5 / 5376 - 5 / 27648 := by
  rw [T9_at_half, term1_eq, term2_eq, term3_eq, term4_eq]

/-- Combining those four fractions over a common denominator. -/
theorem T9_half_combined :
    (1 : ℚ) / 24 - 1 / 160 + 5 / 5376 - 5 / 27648 = 34997 / 967680 := by
  norm_num

/-- Exact single-fraction value of $T_9(1/2)$. -/
theorem T9_half_exact : T9 (1 / 2) = 34997 / 967680 := by
  rw [T9_half_eq, T9_half_combined]

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

#eval ((1 / 24 : Float))
#eval -((1 / 160 : Float))
#eval ((5 / 5376 : Float))
#eval -((5 / 27648 : Float))
#eval (((1 : Float) / 24 - 1 / 160 + 5 / 5376 - 5 / 27648))

end Course21120Taylor
