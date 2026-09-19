import Mathlib
import BSinMeasurementTheory.Course21241.Space

open BigOperators
open Finset

namespace Course21241

/-- Standard primal basis vectors of V -/
def e (i : Fin 3) : V := fun j => if i = j then 1 else 0

/-- Explicit dual basis functionals e_star i ∈ V* -/
def e_star (i : Fin 3) : V →ₗ[ℝ] ℝ where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Duality relation between primal and dual bases: e_star i (e j) = δ_{ij} -/
theorem e_star_apply_e (i j : Fin 3) :
    e_star i (e j) = if i = j then (1 : ℝ) else 0 := by
  dsimp [e_star, e]
  fin_cases i <;> fin_cases j <;> rfl

/-- Every vector x ∈ V expands uniquely in the primal basis -/
theorem vector_eq_sum (x : V) :
    x = ∑ i : Fin 3, x i • e i := by
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_three]
  fin_cases j <;> { dsimp [e]; ring }

/-- The basis vectors {e 0, e 1, e 2} are linearly independent -/
theorem e_linearIndependent :
    LinearIndependent ℝ e := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := congr_fun hg i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e, Pi.zero_apply] at h
  rw [Finset.sum_eq_single_of_mem i hi] at h
  · simp only [ite_true, mul_one] at h
    exact h
  · intro j _ hj
    simp only [hj, ite_false, mul_zero]

/-- Every linear functional φ ∈ V* expands uniquely in the dual basis -/
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
