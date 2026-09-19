import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import BSinMeasurementTheory.Course21321.ScottPair

namespace Course21321

noncomputable section

/-- Kraft–Pratt–Seidenberg difference vectors in `ℝ⁵`. -/
def y1 : Fin 5 → ℝ := ![-1, -1, 1, 1, 0]
def y2 : Fin 5 → ℝ := ![-1, 1, -1, 0, 1]
def y3 : Fin 5 → ℝ := ![1, -1, -1, 1, 0]
def y4 : Fin 5 → ℝ := ![1, 1, 1, -2, -1]

theorem kraft_sum_zero : y1 + y2 + y3 + y4 = 0 := by
  ext i
  fin_cases i <;> norm_num [y1, y2, y3, y4]

/-- The comparative-probability pair whose `Y` is the four Kraft vectors. -/
def KraftPair : ScottPair ℝ (Fin 5 → ℝ) where
  X := ∅
  Y := {y1, y2, y3, y4}

theorem no_strictly_positive_functional (f : (Fin 5 → ℝ) →ₗ[ℝ] ℝ)
    (h1 : 0 < f y1) (h2 : 0 < f y2) (h3 : 0 < f y3) (h4 : 0 < f y4) : False := by
  have h_sum : f (y1 + y2 + y3 + y4) = 0 := by
    rw [kraft_sum_zero, map_zero]
  have h_pos : 0 < f (y1 + y2 + y3 + y4) := by
    rw [map_add, map_add, map_add]
    linarith
  linarith

/-- The Kraft pair admits no separating functional. -/
theorem KraftPair.not_separable : ¬ Separable KraftPair := by
  intro h
  rcases h.exists_sep with ⟨f, -, hfY⟩
  have hy1 : y1 ∈ KraftPair.Y := by simp [KraftPair]
  have hy2 : y2 ∈ KraftPair.Y := by simp [KraftPair]
  have hy3 : y3 ∈ KraftPair.Y := by simp [KraftPair]
  have hy4 : y4 ∈ KraftPair.Y := by simp [KraftPair]
  exact no_strictly_positive_functional f (hfY y1 hy1) (hfY y2 hy2)
    (hfY y3 hy3) (hfY y4 hy4)

end

end Course21321
