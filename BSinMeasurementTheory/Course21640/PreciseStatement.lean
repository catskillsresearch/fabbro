import Mathlib
import BSinMeasurementTheory.Course21640.Sublinear

namespace Course21640

/-- Data of a dominated extension of \(\varphi_0\) from a subspace \(M\). -/
structure DominatedExtension {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : SublinearFunctional V) (M : Submodule ℝ V) (φ0 : M →ₗ[ℝ] ℝ) where
  φ : V →ₗ[ℝ] ℝ
  extends_φ0 : ∀ x : M, φ x = φ0 x
  dominated : ∀ x : V, φ x ≤ p x

/-- Precise statement of Hahn–Banach (dominated extension form). -/
def HahnBanachStatement (V : Type*) [AddCommGroup V] [Module ℝ V] : Prop :=
  ∀ (p : SublinearFunctional V) (M : Submodule ℝ V) (φ0 : M →ₗ[ℝ] ℝ),
    (∀ x : M, φ0 x ≤ p x) → Nonempty (DominatedExtension p M φ0)

end Course21640
