import Mathlib
import BSinMeasurementTheory.Course21640.Sublinear

namespace Course21640

noncomputable section

/-- One-step bounds: any admissible value \(c = \varphi(v)\) sits between
    \(\sup_m(\varphi_0(m) - p(m-v))\) and \(\inf_m(p(m+v) - \varphi_0(m))\). -/
theorem one_step_bounds {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : SublinearFunctional V) {M : Submodule ℝ V} (φ0 : M →ₗ[ℝ] ℝ)
    (hdom : ∀ x : M, φ0 x ≤ p x) (v : V) (m₁ m₂ : M) :
    φ0 m₁ - p ((m₁ : V) - v) ≤ p ((m₂ : V) + v) - φ0 m₂ := by
  have hsum : ((m₁ : V) - v) + ((m₂ : V) + v) = (m₁ : V) + (m₂ : V) := by
    abel
  have hp : p ((m₁ : V) + m₂) ≤ p ((m₁ : V) - v) + p ((m₂ : V) + v) := by
    have := p.map_add_le ((m₁ : V) - v) ((m₂ : V) + v)
    rw [hsum] at this
    simpa using this
  have : φ0 m₁ + φ0 m₂ ≤ p ((m₁ : V) - v) + p ((m₂ : V) + v) :=
    le_trans (by simpa [map_add] using hdom (m₁ + m₂)) hp
  linarith

end

end Course21640
