import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Compact
import BSinMeasurementTheory.Course21720.Boundedness

namespace Course21720

variable {X : Type*} [TopologicalSpace X]

/-- Outer content of an open set from a positive functional, as in the
    Riesz–Markov construction. -/
noncomputable def openContent [CompactSpace X] (Λ : C(X, ℝ) →ₗ[ℝ] ℝ) (U : Set X) : ℝ :=
  sSup {Λ f | (f : C(X, ℝ)) (_ : ∀ x, 0 ≤ f x) (_ : ∀ x, x ∈ U → f x ≤ 1)
    (_ : ∀ x, x ∉ U → f x = 0)}

/-- A positive functional is monotone. This is the comparison used to
    identify \(\Lambda\) with integration against a regular Borel measure. -/
theorem riesz_comparison (Λ : C(X, ℝ) →ₗ[ℝ] ℝ) (hpos : IsPositiveLinearMap Λ)
    (f g : C(X, ℝ)) (h : ∀ x, f x ≤ g x) :
    Λ f ≤ Λ g := by
  have : ∀ x, 0 ≤ (g - f) x := by
    intro x
    simp [sub_nonneg, h x]
  have := hpos.pos (g - f) this
  simpa [map_sub, sub_nonneg] using this

/-- Boundedness from positivity, restated as the operator-norm half of Riesz. -/
theorem riesz_bounded [CompactSpace X] (Λ : C(X, ℝ) →ₗ[ℝ] ℝ) (hpos : IsPositiveLinearMap Λ)
    (f : C(X, ℝ)) : |Λ f| ≤ Λ 1 * ‖f‖ :=
  positive_linear_map_bounded Λ hpos f

end Course21720
