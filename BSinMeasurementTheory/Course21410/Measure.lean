import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Data.Set.Disjoint
import Mathlib.Order.Disjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators Classical

namespace Course21410

namespace ScottMeasurementTheory

/-- A finitely additive probability measure on subsets of a finite space `α`. -/
structure FinitelyAdditiveMeasure (α : Type*) [Fintype α] where
  prob : Set α → ℝ
  prob_nonneg : ∀ A, 0 ≤ prob A
  prob_univ : prob Set.univ = 1
  prob_empty : prob ∅ = 0
  prob_disjoint : ∀ A B, Disjoint A B → prob (A ∪ B) = prob A + prob B

/-- Linear evaluation functional from weight assignments. -/
noncomputable def measureOfWeights {α : Type*} [Fintype α]
    (w : α → ℝ) (hw_nonneg : ∀ x, 0 ≤ w x) (hw_sum : ∑ x, w x = 1) :
    FinitelyAdditiveMeasure α where
  prob A := ∑ x : α, if x ∈ A then w x else 0
  prob_nonneg A := by
    apply Finset.sum_nonneg
    intro x _
    split_ifs <;> linarith [hw_nonneg x]
  prob_univ := by
    simp [hw_sum]
  prob_empty := by
    simp
  prob_disjoint A B hAB := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hA : x ∈ A
    · have hB : x ∉ B := fun h => Set.disjoint_left.mp hAB hA h
      have hu : x ∈ A ∪ B := Or.inl hA
      split_ifs
      ring
    · by_cases hB : x ∈ B
      · have hu : x ∈ A ∪ B := Or.inr hB
        split_ifs
        ring
      · have hu : x ∉ A ∪ B := by
          intro h
          rcases h with h1 | h2
          · exact hA h1
          · exact hB h2
        split_ifs
        ring

end ScottMeasurementTheory

end Course21410
