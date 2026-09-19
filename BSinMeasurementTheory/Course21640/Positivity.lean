import Mathlib
import BSinMeasurementTheory.Course21640.Sublinear

namespace Course21640

noncomputable section

/-- Step (b): a linear functional dominated by $p(f) = C \cdot \|f\|$ with
$0 \le C$ is positive on the indicated cone. -/
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
