import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Real.Basic
import BSinMeasurementTheory.Course21640.PreciseStatement
import BSinMeasurementTheory.Course21640.NormSublinear
import BSinMeasurementTheory.Course21640.Dominance

namespace Course21640

noncomputable section

/-- Applying dominated extension: a functional dominated by \(C\|f\|\) on a
    subspace extends to one dominated by the same bound on the whole space. -/
theorem apply_hahn_banach
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hHB : HahnBanachStatement V)
    (M : Submodule ℝ V) (φ0 : M →ₗ[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ g : M, φ0 g ≤ C * ‖(g : V)‖) :
    ∃ φ : V →ₗ[ℝ] ℝ, (∀ g : M, φ g = φ0 g) ∧ (∀ f : V, φ f ≤ C * ‖f‖) := by
  let p := normSublinear V C hC
  have hdom' : ∀ g : M, φ0 g ≤ p g := hdom
  obtain ⟨ext⟩ := hHB p M φ0 hdom'
  exact ⟨ext.φ, ext.extends_φ0, ext.dominated⟩

end

end Course21640
