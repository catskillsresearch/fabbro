import Mathlib
import BSinMeasurementTheory.Course21322.MeasureCollapse

open scoped BigOperators Classical

namespace Course21322

namespace FiniteStoneCollapse

set_option linter.unusedSectionVars false

def w3 : Fin 3 → ℝ
  | 0 => 0.2
  | 1 => 0.5
  | 2 => 0.3

lemma w3_sum : ∑ x : Fin 3, w3 x = 1 := by
  rw [Fin.sum_univ_three]
  norm_num [w3]

def testSet : Set (Fin 3) := {0, 2}

/-- Direct calculation of the atomic measure on {0, 2}: 0.2 + 0.3 = 0.5 -/
theorem atomic_test_eval : atomicMeasure w3 testSet = 0.5 := by
  dsimp [atomicMeasure, testSet]
  rw [Fin.sum_univ_three]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff]
  norm_num [w3]

/-- Calculation via the Stone representation map on {0, 2}: 0.2 + 0.3 = 0.5 -/
theorem stone_test_eval : stoneMeasure w3 testSet = 0.5 := by
  rw [stone_measure_eq_atomic_measure]
  exact atomic_test_eval

end FiniteStoneCollapse

end Course21322
