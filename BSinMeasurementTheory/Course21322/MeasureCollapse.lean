import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import BSinMeasurementTheory.Course21322.StoneClopen

open scoped BigOperators Classical

namespace Course21322

namespace FiniteStoneCollapse

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Linear evaluation on step functions over the Stone space with weights `w`. -/
noncomputable def stoneMeasure (w : α → ℝ) (s : Set α) : ℝ :=
  ∑ a : α, if atomToStone a ∈ stoneMap s then w a else 0

/-- Discrete atomic measure sum from Phase 2 / Phase 3. -/
noncomputable def atomicMeasure (w : α → ℝ) (s : Set α) : ℝ :=
  ∑ a : α, if a ∈ s then w a else 0

/-- THE COLLAPSE THEOREM: The Stone space measure evaluation reduces identically
    to the finite atomic characteristic sum with ZERO discrepancy. -/
theorem stone_measure_eq_atomic_measure (w : α → ℝ) (s : Set α) :
    stoneMeasure w s = atomicMeasure w s := by
  dsimp [stoneMeasure, atomicMeasure]
  apply Finset.sum_congr rfl
  intro a _
  rw [← atom_mem_iff_stone_mem]

end FiniteStoneCollapse

end Course21322
