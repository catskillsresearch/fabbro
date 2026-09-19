import Mathlib
import BSinMeasurementTheory.Course21410.Measure

open scoped BigOperators Classical

namespace Course21410

namespace ScottMeasurementTheory

/-- GLUE LEMMA 1: Inclusion-exclusion for finitely additive measures. -/
theorem measure_union {α : Type*} [Fintype α]
    (μ : FinitelyAdditiveMeasure α) (A B : Set α) :
    μ.prob (A ∪ B) + μ.prob (A ∩ B) = μ.prob A + μ.prob B := by
  have h1 : A ∪ B = (A \ B) ∪ B := by
    ext x
    constructor
    · intro h
      rcases h with hA | hB
      · by_cases hB : x ∈ B
        · exact Or.inr hB
        · exact Or.inl ⟨hA, hB⟩
      · exact Or.inr hB
    · intro h
      rcases h with ⟨hA, _⟩ | hB
      · exact Or.inl hA
      · exact Or.inr hB
  have h1_disj : Disjoint (A \ B) B := by
    rw [Set.disjoint_left]
    intro x hx
    exact hx.2
  have h2 : A = (A \ B) ∪ (A ∩ B) := by
    ext x
    constructor
    · intro hA
      by_cases hB : x ∈ B
      · exact Or.inr ⟨hA, hB⟩
      · exact Or.inl ⟨hA, hB⟩
    · intro h
      rcases h with ⟨hA, _⟩ | ⟨hA, _⟩
      · exact hA
      · exact hA
  have h2_disj : Disjoint (A \ B) (A ∩ B) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx.2 hx'.2
  have eq1 : μ.prob (A ∪ B) = μ.prob (A \ B) + μ.prob B := by
    nth_rw 1 [h1]
    exact μ.prob_disjoint (A \ B) B h1_disj
  have eq2 : μ.prob A = μ.prob (A \ B) + μ.prob (A ∩ B) := by
    nth_rw 1 [h2]
    exact μ.prob_disjoint (A \ B) (A ∩ B) h2_disj
  rw [eq1, eq2]
  ring

/-- GLUE LEMMA 2: Monotonicity of finitely additive measures. -/
theorem measure_mono {α : Type*} [Fintype α]
    (w : α → ℝ) (hw_nonneg : ∀ x, 0 ≤ w x) (hw_sum : ∑ x, w x = 1)
    (A B : Set α) (hAB : A ⊆ B) :
    (measureOfWeights w hw_nonneg hw_sum).prob A ≤ (measureOfWeights w hw_nonneg hw_sum).prob B := by
  dsimp [measureOfWeights]
  apply Finset.sum_le_sum
  intro x _
  split_ifs with hA hB
  · exact le_rfl
  · exfalso
    exact hB (hAB hA)
  · exact hw_nonneg x
  · exact le_rfl

/-- GLUE LEMMA 3: Preservation of qualitative preference order by linear functional restriction. -/
theorem qualitative_agreement {α : Type*} [Fintype α]
    (w : α → ℝ) (hw_nonneg : ∀ x, 0 ≤ w x) (hw_sum : ∑ x, w x = 1)
    (A B : Set α)
    (h_diff : 0 ≤ (∑ x : α, if x ∈ B then w x else 0) - (∑ x : α, if x ∈ A then w x else 0)) :
    (measureOfWeights w hw_nonneg hw_sum).prob A ≤ (measureOfWeights w hw_nonneg hw_sum).prob B := by
  dsimp [measureOfWeights]
  linarith

end ScottMeasurementTheory

end Course21410
