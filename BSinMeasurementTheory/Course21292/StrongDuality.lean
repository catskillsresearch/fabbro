import Mathlib
import BSinMeasurementTheory.Course21292.WeakDuality

open scoped BigOperators

namespace Course21292

namespace LPDuality

/-- If a primal-feasible \(x\) and dual-feasible \(y\) attain the same value,
    then both are optimal: this is strong duality in certificate form. -/
theorem strong_duality_of_equal_value {m n : ℕ}
    (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ) (c : Fin n → ℚ)
    (x : Fin n → ℚ) (y : Fin m → ℚ)
    (hx_nonneg : NonNeg x) (hy_nonneg : NonNeg y)
    (h_primal_feas : ∀ i, b i ≤ matMulVec A x i)
    (h_dual_feas : ∀ j, matTransposeMulVec A y j ≤ c j)
    (h_eq : dot b y = dot c x) :
    (∀ x' : Fin n → ℚ, NonNeg x' → (∀ i, b i ≤ matMulVec A x' i) →
      dot c x ≤ dot c x') ∧
    (∀ y' : Fin m → ℚ, NonNeg y' → (∀ j, matTransposeMulVec A y' j ≤ c j) →
      dot b y' ≤ dot b y) := by
  constructor
  · intro x' hx' hfeas'
    have := weak_duality A b c x' y hx' hy_nonneg hfeas' h_dual_feas
    linarith
  · intro y' hy' hfeas'
    have := weak_duality A b c x y' hx_nonneg hy' h_primal_feas hfeas'
    linarith

end LPDuality

end Course21292
