import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.Tactic.FinCases
import BSinMeasurementTheory.Course21241.PrimalBasis

open BigOperators
open Finset

namespace Course21241

/-- Explicit dual basis functionals \(e^* i \in V^*\). -/
def e_star (i : Fin 3) : V →ₗ[ℝ] ℝ where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Duality relation: \(e^* i\,(e\,j) = \delta_{ij}\). -/
theorem e_star_apply_e (i j : Fin 3) :
    e_star i (e j) = if i = j then (1 : ℝ) else 0 := by
  dsimp [e_star, e]
  fin_cases i <;> fin_cases j <;> rfl

/-- Every linear functional \(\varphi \in V^*\) expands uniquely in the dual basis. -/
theorem dual_eq_sum (φ : V →ₗ[ℝ] ℝ) :
    φ = ∑ i : Fin 3, φ (e i) • e_star i := by
  apply LinearMap.ext
  intro x
  have hx : x = ∑ i : Fin 3, x i • e i := vector_eq_sum x
  conv_lhs => rw [hx]
  rw [map_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  dsimp [e_star]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.map_smul, smul_eq_mul, mul_comm]

end Course21241
