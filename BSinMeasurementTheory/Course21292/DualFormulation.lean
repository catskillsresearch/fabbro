import Mathlib
import BSinMeasurementTheory.Course21292.ScottInstance

open scoped BigOperators

namespace Course21292

namespace LPDuality

/-- Dual objective \(3y_1 + 3y_2 + y_3\). -/
def dualObjective (y : Fin 3 → ℚ) : ℚ :=
  dot b_inst y

/-- Dual constraints \(A^\top y \le c\), \(y \ge 0\). -/
def DualFeasible (y : Fin 3 → ℚ) : Prop :=
  NonNeg y ∧ ∀ j, matTransposeMulVec A_inst y j ≤ c_inst j

theorem dual_constraint_0 (y : Fin 3 → ℚ) :
    matTransposeMulVec A_inst y 0 = 2 * y 0 + y 1 := by
  dsimp [matTransposeMulVec, A_inst]
  rw [Fin.sum_univ_three]
  ring

theorem dual_constraint_1 (y : Fin 3 → ℚ) :
    matTransposeMulVec A_inst y 1 = y 0 + 2 * y 1 := by
  dsimp [matTransposeMulVec, A_inst]
  rw [Fin.sum_univ_three]
  ring

theorem dual_constraint_2 (y : Fin 3 → ℚ) :
    matTransposeMulVec A_inst y 2 = y 2 := by
  dsimp [matTransposeMulVec, A_inst]
  rw [Fin.sum_univ_three]
  ring

end LPDuality

end Course21292
