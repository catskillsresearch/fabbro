import Mathlib
import BSinMeasurementTheory.Course21292.DualFormulation

open scoped BigOperators

namespace Course21292

namespace LPDuality

def x_star : Fin 3 → ℚ
  | 0 => 1 | 1 => 1 | 2 => 1

def y_star : Fin 3 → ℚ
  | 0 => 1/3 | 1 => 1/3 | 2 => 2

theorem primal_cost_eval : dot c_inst x_star = 4 := by
  dsimp [dot, c_inst, x_star]
  rw [Fin.sum_univ_three]
  norm_num

theorem dual_cost_eval : dot b_inst y_star = 4 := by
  dsimp [dot, b_inst, y_star]
  rw [Fin.sum_univ_three]
  norm_num

theorem x_star_feasible :
    NonNeg x_star ∧ (∀ i, b_inst i ≤ matMulVec A_inst x_star i) := by
  constructor
  · refine ⟨?_⟩
    intro i
    fin_cases i <;> norm_num [x_star]
  · intro i
    fin_cases i <;> {
      dsimp [b_inst, matMulVec, dot, A_inst, x_star]
      rw [Fin.sum_univ_three]
      norm_num
    }

theorem y_star_feasible : DualFeasible y_star := by
  constructor
  · refine ⟨?_⟩
    intro i
    fin_cases i <;> norm_num [y_star]
  · intro j
    fin_cases j <;> {
      dsimp [c_inst, matTransposeMulVec, A_inst, y_star]
      rw [Fin.sum_univ_three]
      norm_num
    }

theorem strong_duality_certificate :
    dot c_inst x_star = dot b_inst y_star := by
  rw [primal_cost_eval, dual_cost_eval]

end LPDuality

end Course21292
