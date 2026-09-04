import Mathlib

open scoped BigOperators

namespace Course21292Numerical

namespace LPDualityCalculations

-- 1. Definitions of Vector/Matrix Operations
def dot {n : ℕ} (u v : Fin n → ℚ) : ℚ :=
  ∑ i : Fin n, u i * v i

def matMulVec {m n : ℕ} (A : Fin m → Fin n → ℚ) (x : Fin n → ℚ) : Fin m → ℚ :=
  fun i => dot (A i) x

def matTransposeMulVec {m n : ℕ} (A : Fin m → Fin n → ℚ) (y : Fin m → ℚ) : Fin n → ℚ :=
  fun j => ∑ i : Fin m, y i * A i j

-- Definition of the Slack Vectors
def primalSlack (A : Fin 3 → Fin 3 → ℚ) (b : Fin 3 → ℚ) (x : Fin 3 → ℚ) : Fin 3 → ℚ :=
  fun i => matMulVec A x i - b i

def dualSlack (A : Fin 3 → Fin 3 → ℚ) (c : Fin 3 → ℚ) (y : Fin 3 → ℚ) : Fin 3 → ℚ :=
  fun j => c j - matTransposeMulVec A y j

-- 2. Instance Data
def A_inst : Fin 3 → Fin 3 → ℚ
  | 0, 0 => 2 | 0, 1 => 1 | 0, 2 => 0
  | 1, 0 => 1 | 1, 1 => 2 | 1, 2 => 0
  | 2, 0 => 0 | 2, 1 => 0 | 2, 2 => 1

def b_inst : Fin 3 → ℚ
  | 0 => 3 | 1 => 3 | 2 => 1

def c_inst : Fin 3 → ℚ
  | 0 => 1 | 1 => 1 | 2 => 2

def x_star : Fin 3 → ℚ
  | 0 => 1 | 1 => 1 | 2 => 1

def y_star : Fin 3 → ℚ
  | 0 => 1/3 | 1 => 1/3 | 2 => 2

/-!
### 3. Formal Proofs of the Four Numerical Calculations
-/

-- (1) Primal Cost = 4
theorem primal_cost_eq_four : dot c_inst x_star = 4 := by
  dsimp [dot, c_inst, x_star]
  rw [Fin.sum_univ_three]
  norm_num

-- (2) Dual Cost = 4
theorem dual_cost_eq_four : dot b_inst y_star = 4 := by
  dsimp [dot, b_inst, y_star]
  rw [Fin.sum_univ_three]
  norm_num

-- (3) Primal Slack Vector = 0
theorem primal_slack_is_zero : primalSlack A_inst b_inst x_star = 0 := by
  ext i
  fin_cases i <;> {
    dsimp [primalSlack, matMulVec, dot, A_inst, b_inst, x_star]
    rw [Fin.sum_univ_three]
    norm_num
  }

-- (4) Dual Slack Vector = 0
theorem dual_slack_is_zero : dualSlack A_inst c_inst y_star = 0 := by
  ext j
  fin_cases j <;> {
    dsimp [dualSlack, matTransposeMulVec, A_inst, c_inst, y_star]
    rw [Fin.sum_univ_three]
    norm_num
  }

-- Summary: Exact Complementary Slackness & Zero Duality Gap
theorem complementary_slackness_and_optimality :
    dot c_inst x_star = dot b_inst y_star ∧
    primalSlack A_inst b_inst x_star = 0 ∧
    dualSlack A_inst c_inst y_star = 0 := by
  refine ⟨by rw [primal_cost_eq_four, dual_cost_eq_four],
          primal_slack_is_zero,
          dual_slack_is_zero⟩

end LPDualityCalculations


end Course21292Numerical
