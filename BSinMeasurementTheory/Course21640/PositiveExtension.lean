import Mathlib
import BSinMeasurementTheory.Course21640.ApplyHahnBanach
import BSinMeasurementTheory.Course21640.Positivity

namespace Course21640

noncomputable section

/-- Wrap-up of part (b): a dominated extension that fixes the unit is positive. -/
theorem positive_extension
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (φ : V →ₗ[ℝ] ℝ) (one : V) (C : ℝ) (hC : 0 ≤ C)
    (h_one : φ one = C)
    (h_dom : ∀ f : V, φ f ≤ C * ‖f‖)
    (f : V) (hf_norm : ‖‖f‖ • one - f‖ ≤ ‖f‖) :
    0 ≤ φ f :=
  positive_of_dominated_by_norm φ one C hC h_one h_dom f hf_norm

end

end Course21640
