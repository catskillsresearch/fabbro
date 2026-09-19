import Mathlib

namespace Course21640

noncomputable section

/-- A sublinear functional on a real vector space. -/
structure SublinearFunctional (V : Type*) [AddCommGroup V] [Module ℝ V] where
  toFun : V → ℝ
  map_add_le : ∀ x y : V, toFun (x + y) ≤ toFun x + toFun y
  map_smul_nonneg : ∀ (c : ℝ) (x : V), 0 ≤ c → toFun (c • x) = c * toFun x

instance (V : Type*) [AddCommGroup V] [Module ℝ V] :
    CoeFun (SublinearFunctional V) (fun _ => V → ℝ) where
  coe p := p.toFun

/-- Step (b): Given a linear functional `φ` dominated by `p(f) = C * ‖f‖` with `0 ≤ C`,
    `φ` is positive on non-negative elements. -/
theorem positive_of_dominated_by_norm
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (φ : V →ₗ[ℝ] ℝ) (one : V) (C : ℝ) (hC : 0 ≤ C)
    (h_one : φ one = C)
    (h_dom : ∀ f : V, φ f ≤ C * ‖f‖)
    (f : V) (hf_norm : ‖‖f‖ • one - f‖ ≤ ‖f‖) :
    0 ≤ φ f := by
  have h_le : φ (‖f‖ • one - f) ≤ C * ‖‖f‖ • one - f‖ := h_dom (‖f‖ • one - f)
  have h_decomp : φ (‖f‖ • one - f) = ‖f‖ * C - φ f := by
    rw [map_sub, map_smul, h_one, smul_eq_mul]
  rw [h_decomp] at h_le
  have h_bound : C * ‖‖f‖ • one - f‖ ≤ C * ‖f‖ :=
    mul_le_mul_of_nonneg_left hf_norm hC
  linarith

end

end Course21640
