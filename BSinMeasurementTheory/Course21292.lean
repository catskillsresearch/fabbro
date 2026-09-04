import Mathlib

open scoped BigOperators

namespace Course21292

namespace LPDuality

-- Vector inner product over Rational numbers for Fin n
def dot {n : ℕ} (u v : Fin n → ℚ) : ℚ :=
  ∑ i : Fin n, u i * v i

-- Non-negativity of a vector
def NonNeg {n : ℕ} (v : Fin n → ℚ) : Prop :=
  ∀ i : Fin n, 0 ≤ v i

-- Matrix-vector multiplication (A * x)
def matMulVec {m n : ℕ} (A : Fin m → Fin n → ℚ) (x : Fin n → ℚ) : Fin m → ℚ :=
  fun i => dot (A i) x

-- Transpose matrix-vector multiplication (Aᵀ * y)
def matTransposeMulVec {m n : ℕ} (A : Fin m → Fin n → ℚ) (y : Fin m → ℚ) : Fin n → ℚ :=
  fun j => ∑ i : Fin m, y i * A i j

/-!
### 1. General Weak Duality Theorem
-/

theorem transpose_dot_assoc {m n : ℕ} (A : Fin m → Fin n → ℚ)
    (y : Fin m → ℚ) (x : Fin n → ℚ) :
    dot y (matMulVec A x) = dot (matTransposeMulVec A y) x := by
  dsimp [dot, matMulVec, matTransposeMulVec]
  -- Distribute multiplications inside the sums before commuting
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem weak_duality {m n : ℕ} (A : Fin m → Fin n → ℚ)
    (b : Fin m → ℚ) (c : Fin n → ℚ)
    (x : Fin n → ℚ) (y : Fin m → ℚ)
    (hx_nonneg : NonNeg x)
    (hy_nonneg : NonNeg y)
    (h_primal_feas : ∀ i, b i ≤ matMulVec A x i)
    (h_dual_feas : ∀ j, matTransposeMulVec A y j ≤ c j) :
    dot b y ≤ dot c x := by
  have h1 : dot b y ≤ dot (matMulVec A x) y := by
    dsimp [dot]
    have h_term : ∀ i : Fin m, b i * y i ≤ matMulVec A x i * y i := by
      intro i
      have hy : 0 ≤ y i := hy_nonneg i
      have hfeas : b i ≤ matMulVec A x i := h_primal_feas i
      nlinarith
    exact Finset.sum_le_sum fun i _ => h_term i
  have h_comm : dot (matMulVec A x) y = dot y (matMulVec A x) := by
    dsimp [dot]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h_comm, transpose_dot_assoc] at h1
  have h2 : dot (matTransposeMulVec A y) x ≤ dot c x := by
    dsimp [dot]
    have h_term : ∀ j : Fin n, matTransposeMulVec A y j * x j ≤ c j * x j := by
      intro j
      have hx : 0 ≤ x j := hx_nonneg j
      have hfeas : matTransposeMulVec A y j ≤ c j := h_dual_feas j
      nlinarith
    exact Finset.sum_le_sum fun j _ => h_term j
  exact le_trans h1 h2

/-!
### 2. Concrete 3x3 Instance Verification (Scott 1.1 Cone Setting)
-/

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

-- Primal Cost Evaluation: dot(c, x*) = 4
theorem primal_cost_eval : dot c_inst x_star = 4 := by
  dsimp [dot, c_inst, x_star]
  rw [Fin.sum_univ_three]
  norm_num

-- Dual Cost Evaluation: dot(b, y*) = 4
theorem dual_cost_eval : dot b_inst y_star = 4 := by
  dsimp [dot, b_inst, y_star]
  rw [Fin.sum_univ_three]
  norm_num

-- Primal Feasibility Proof
theorem x_star_feasible :
    NonNeg x_star ∧ (∀ i, b_inst i ≤ matMulVec A_inst x_star i) := by
  constructor
  · intro i
    fin_cases i <;> norm_num [x_star, NonNeg]
  · intro i
    fin_cases i <;> {
      dsimp [b_inst, matMulVec, dot, A_inst, x_star]
      rw [Fin.sum_univ_three]
      norm_num
    }

-- Dual Feasibility Proof
theorem y_star_feasible :
    NonNeg y_star ∧ (∀ j, matTransposeMulVec A_inst y_star j ≤ c_inst j) := by
  constructor
  · intro i
    fin_cases i <;> norm_num [y_star, NonNeg]
  · intro j
    fin_cases j <;> {
      dsimp [c_inst, matTransposeMulVec, A_inst, y_star]
      rw [Fin.sum_univ_three]
      norm_num
    }

-- Certificate of Zero Duality Gap
theorem strong_duality_certificate :
    dot c_inst x_star = dot b_inst y_star := by
  rw [primal_cost_eval, dual_cost_eval]

end LPDuality


end Course21292
