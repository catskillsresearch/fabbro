import Mathlib
import BSinMeasurementTheory.Course21292.LinearProgram

open scoped BigOperators

namespace Course21292

namespace LPDuality

theorem transpose_dot_assoc {m n : ℕ} (A : Fin m → Fin n → ℚ)
    (y : Fin m → ℚ) (x : Fin n → ℚ) :
    dot y (matMulVec A x) = dot (matTransposeMulVec A y) x := by
  dsimp [dot, matMulVec, matTransposeMulVec]
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
      have hy : 0 ≤ y i := hy_nonneg.nonneg i
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
      have hx : 0 ≤ x j := hx_nonneg.nonneg j
      have hfeas : matTransposeMulVec A y j ≤ c j := h_dual_feas j
      nlinarith
    exact Finset.sum_le_sum fun j _ => h_term j
  exact le_trans h1 h2

end LPDuality

end Course21292
