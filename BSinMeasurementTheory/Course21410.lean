import Mathlib

open scoped BigOperators Classical

namespace Course21410

namespace ScottMeasurementTheory

/-!
### 1. Finite-Dimensional Step Function Space and Additive Measures
-/

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

/-!
### 2. Glue Lemmas: Finite Additivity, Inclusion-Exclusion, and Monotonicity
-/

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

/-!
### 3. Concrete Example in Lean 4
-/

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
