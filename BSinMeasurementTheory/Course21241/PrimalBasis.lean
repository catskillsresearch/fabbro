import Mathlib
import BSinMeasurementTheory.Course21241.Space

open BigOperators
open Finset

namespace Course21241

/-- Standard primal basis vectors of V. -/
def e (i : Fin 3) : V := fun j => if i = j then 1 else 0

/-- Every vector \(x \in V\) expands uniquely in the primal basis. -/
theorem vector_eq_sum (x : V) :
    x = ∑ i : Fin 3, x i • e i := by
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_three]
  fin_cases j <;> { dsimp [e]; ring }

/-- The basis vectors \(\{e\,0, e\,1, e\,2\}\) are linearly independent. -/
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

end Course21241
