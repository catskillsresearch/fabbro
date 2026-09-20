import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import BSinMeasurementTheory.Course21410.Measure

open scoped BigOperators Classical

namespace Course21410

namespace ScottMeasurementTheory

def w4 : Fin 4 → ℝ
  | 0 => 0.1
  | 1 => 0.2
  | 2 => 0.3
  | 3 => 0.4

lemma w4_nonneg : ∀ x : Fin 4, 0 ≤ w4 x := by
  intro x
  fin_cases x <;> norm_num [w4]

lemma w4_sum : ∑ x : Fin 4, w4 x = 1 := by
  rw [Fin.sum_univ_four]
  norm_num [w4]

noncomputable def μ4 : FinitelyAdditiveMeasure (Fin 4) :=
  measureOfWeights w4 w4_nonneg w4_sum

def setA : Set (Fin 4) := {0, 1}
def setB : Set (Fin 4) := {1, 2, 3}

theorem example_probA : μ4.prob setA = 0.3 := by
  dsimp [μ4, measureOfWeights, setA]
  rw [Fin.sum_univ_four]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff]
  norm_num [w4]

theorem example_probB : μ4.prob setB = 0.9 := by
  dsimp [μ4, measureOfWeights, setB]
  rw [Fin.sum_univ_four]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff]
  norm_num [w4]

theorem example_prob_inter : μ4.prob (setA ∩ setB) = 0.2 := by
  dsimp [μ4, measureOfWeights, setA, setB]
  rw [Fin.sum_univ_four]
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff]
  norm_num [w4]

theorem example_prob_union : μ4.prob (setA ∪ setB) = 1.0 := by
  dsimp [μ4, measureOfWeights, setA, setB]
  rw [Fin.sum_univ_four]
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff]
  norm_num [w4]

theorem example_inclusion_exclusion :
    μ4.prob (setA ∪ setB) + μ4.prob (setA ∩ setB) = μ4.prob setA + μ4.prob setB := by
  rw [example_prob_union, example_prob_inter, example_probA, example_probB]
  norm_num

end ScottMeasurementTheory

end Course21410
