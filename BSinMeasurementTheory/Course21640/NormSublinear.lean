import Mathlib
import BSinMeasurementTheory.Course21640.Sublinear

namespace Course21640

noncomputable section

/-- The norm-based dominating functional \(p(f) = C\|f\|\). -/
def normSublinear (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (C : ℝ) (hC : 0 ≤ C) : SublinearFunctional V where
  toFun f := C * ‖f‖
  map_add_le x y := by
    have := norm_add_le x y
    nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x + y)]
  map_smul_nonneg c x hc := by
    simp [norm_smul, abs_of_nonneg hc]
    ring

theorem normSublinear_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (C : ℝ) (hC : 0 ≤ C) (f : V) :
    (normSublinear V C hC) f = C * ‖f‖ :=
  rfl

end

end Course21640
