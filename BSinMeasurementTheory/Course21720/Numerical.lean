import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Course21720

/-- Linear map instance for the concrete functional `Λ(f) = 3 f(0) + 2 f(1)`. -/
def lambda_linear : (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun f := 3 * f.1 + 2 * f.2
  map_add' x y := by
    dsimp
    ring
  map_smul' c x := by
    dsimp
    ring

/-- Value of Λ on the constant function 1 = (1, 1). -/
theorem concrete_lambda_one : lambda_linear (1, 1) = 5 := by
  dsimp [lambda_linear]
  norm_num

/-- Values on the 4 elements of the Boolean algebra P({0, 1}). -/
theorem concrete_measure_bot : lambda_linear (0, 0) = 0 := by
  dsimp [lambda_linear]
  norm_num

theorem concrete_measure_singleton_0 : lambda_linear (1, 0) = 3 := by
  dsimp [lambda_linear]
  norm_num

theorem concrete_measure_singleton_1 : lambda_linear (0, 1) = 2 := by
  dsimp [lambda_linear]
  norm_num

theorem concrete_measure_top : lambda_linear (1, 1) = 5 := by
  dsimp [lambda_linear]
  norm_num

/-- Verification of finite additivity for disjoint singletons:
    μ({0} ∪ {1}) = μ({0}) + μ({1}) = 3 + 2 = 5. -/
theorem concrete_additivity :
    lambda_linear (1 + 0, 0 + 1) = lambda_linear (1, 0) + lambda_linear (0, 1) := by
  dsimp [lambda_linear]
  norm_num

end Course21720
