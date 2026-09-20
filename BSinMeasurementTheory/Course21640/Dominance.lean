import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import BSinMeasurementTheory.Course21640.NormSublinear

namespace Course21640

noncomputable section

/-- Dominance on the indicated subspace: if \(\|g\|\mathbf{1} - g\) is sent
    to a nonnegative value, then \(\varphi_0(g) \le C\|g\|\). -/
theorem dominance_of_positive
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (φ : V →ₗ[ℝ] ℝ) (one : V) (C : ℝ)
    (h_one : φ one = C)
    (g : V) (hpos : 0 ≤ φ (‖g‖ • one - g)) :
    φ g ≤ C * ‖g‖ := by
  have : φ (‖g‖ • one - g) = ‖g‖ * C - φ g := by
    rw [map_sub, map_smul, h_one, smul_eq_mul]
  linarith

end

end Course21640
