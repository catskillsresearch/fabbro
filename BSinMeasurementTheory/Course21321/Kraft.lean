import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import BSinMeasurementTheory.Course21321.ScottPair
import BSinMeasurementTheory.Course21321.Theorem11

namespace Course21321

noncomputable section

/-- Kraft–Pratt–Seidenberg difference vectors in `ℝ⁵`. These are data, not a
new class: they assemble into a particular `ScottPair` below. -/
def y1 : Fin 5 → ℝ := ![-1, -1, 1, 1, 0]
def y2 : Fin 5 → ℝ := ![-1, 1, -1, 0, 1]
def y3 : Fin 5 → ℝ := ![1, -1, -1, 1, 0]
def y4 : Fin 5 → ℝ := ![1, 1, 1, -2, -1]

theorem kraft_sum_zero : y1 + y2 + y3 + y4 = 0 := by
  ext i
  fin_cases i <;> norm_num [y1, y2, y3, y4]

/-- A concrete Scott pair — an inhabitant, like a particular monoid, not a
new typeclass. -/
def KraftPair : ScottPair ℝ (Fin 5 → ℝ) where
  X := ∅
  Y := {y1, y2, y3, y4}

lemma kraftY_sum : ∑ y ∈ KraftPair.Y, y = y1 + y2 + y3 + y4 := by
  ext i
  rw [Finset.sum_apply]
  simp [KraftPair]
  fin_cases i <;> norm_num [y1, y2, y3, y4]

/-- Unit weights on the four Kraft vectors are a `CancellationWitness`. -/
instance : CancellationWitness KraftPair where
  c := fun _ => 0
  d := fun _ => 1
  c_nonneg := fun _ _ => le_rfl
  d_nonneg := fun _ _ => zero_le_one
  d_mass := by
    change (0 : ℝ) < ∑ y ∈ ({y1, y2, y3, y4} : Finset (Fin 5 → ℝ)), (1 : ℝ)
    simp
  sum_zero := by
    simp [one_smul, KraftPair]
    exact kraftY_sum.trans kraft_sum_zero

/-- A cancellation witness rules out a separating functional. -/
theorem not_separable_of_cancellationWitness
    {V : Type*} [AddCommGroup V] [Module ℝ V] [DecidableEq V]
    (P : ScottPair ℝ V) [w : CancellationWitness P] : ¬ Separable P := by
  intro h
  have inst : NoCancellation P := NoCancellation.of_separable (P := P)
  exact inst.no_cancel w.c w.d w.c_nonneg w.d_nonneg w.d_mass w.sum_zero

theorem KraftPair.not_separable : ¬ Separable KraftPair :=
  not_separable_of_cancellationWitness KraftPair

end

end Course21321
