import Mathlib.Topology.ContinuousMap.Compact

namespace Course21720

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- A linear functional on `C(X, ℝ)` is positive if `(∀ x, 0 ≤ f x) → 0 ≤ Λ f`. -/
class IsPositiveLinearMap {X : Type*} [TopologicalSpace X] (Λ : C(X, ℝ) →ₗ[ℝ] ℝ) : Prop where
  pos : ∀ f : C(X, ℝ), (∀ x : X, 0 ≤ f x) → 0 ≤ Λ f

/-- Part (a): A positive linear functional on `C(X, ℝ)` for compact `X`
    is bounded by `Λ 1 * ‖f‖`. -/
theorem positive_linear_map_bounded (Λ : C(X, ℝ) →ₗ[ℝ] ℝ) (hpos : IsPositiveLinearMap Λ)
    (f : C(X, ℝ)) : |Λ f| ≤ Λ 1 * ‖f‖ := by
  have h1 : ∀ x : X, 0 ≤ (‖f‖ • (1 : C(X, ℝ)) - f) x := by
    intro x
    rw [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
        smul_eq_mul, mul_one]
    have := ContinuousMap.apply_le_norm f x
    linarith
  have h2 : ∀ x : X, 0 ≤ (‖f‖ • (1 : C(X, ℝ)) + f) x := by
    intro x
    rw [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
        smul_eq_mul, mul_one]
    have := ContinuousMap.neg_norm_le_apply f x
    linarith
  have l1 := hpos.pos (‖f‖ • (1 : C(X, ℝ)) - f) h1
  have l2 := hpos.pos (‖f‖ • (1 : C(X, ℝ)) + f) h2
  rw [map_sub, LinearMap.map_smul, smul_eq_mul, sub_nonneg] at l1
  rw [map_add, LinearMap.map_smul, smul_eq_mul, ← sub_le_iff_le_add'] at l2
  rw [abs_le]
  constructor
  · rw [mul_comm]
    linarith
  · rw [mul_comm]
    linarith

end Course21720
