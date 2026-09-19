import Mathlib
import BSinMeasurementTheory.Course21241.Basis

open BigOperators
open Finset

namespace Course21241

/-- Standard Euclidean inner product on V -/
def dot (u v : V) : ℝ := ∑ i : Fin 3, u i * v i

lemma dot_comm (u v : V) : dot u v = dot v u := by
  dsimp [dot]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma dot_e (u : V) (i : Fin 3) : dot u (e i) = u i := by
  dsimp [dot]
  rw [Fin.sum_univ_three]
  fin_cases i <;> { dsimp [e]; ring }

/-- Riesz map from V to V* -/
def toDual (u : V) : V →ₗ[ℝ] ℝ where
  toFun v := dot u v
  map_add' v w := by
    dsimp [dot]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  map_smul' c v := by
    dsimp [dot]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Inverse Riesz map from V* to V -/
def toVec (φ : V →ₗ[ℝ] ℝ) : V := fun i => φ (e i)

theorem toDual_toVec (φ : V →ₗ[ℝ] ℝ) : toDual (toVec φ) = φ := by
  apply LinearMap.ext
  intro x
  have hx : x = ∑ i : Fin 3, x i • e i := vector_eq_sum x
  conv_rhs => rw [hx]
  rw [map_sum]
  change (∑ i : Fin 3, φ (e i) * x i) = ∑ i : Fin 3, φ (x i • e i)
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.map_smul, smul_eq_mul, mul_comm]

theorem toVec_toDual (u : V) : toVec (toDual u) = u := by
  ext i
  exact dot_e u i

/-- Characterization of functionals nonnegative on C -/
theorem nonneg_on_C_iff (u : V) :
    (∀ c ∈ C, 0 ≤ dot u c) ↔ ∀ i : Fin 3, 0 ≤ u i := by
  constructor
  · intro h i
    have hei : e i ∈ C := by
      intro j
      dsimp [e]
      split_ifs <;> linarith
    have h_dot := h (e i) hei
    rw [dot_e] at h_dot
    exact h_dot
  · intro hu c hc
    dsimp [dot]
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hu i) (hc i)

/-- Existence of a separating vector under the inner product for any v ∉ C -/
theorem exists_separating_vector (v : V) (hv : v ∉ C) :
    ∃ u : V, (∀ c ∈ C, 0 ≤ dot u c) ∧ dot u v < 0 := by
  change ¬ (∀ i : Fin 3, 0 ≤ v i) at hv
  push Not at hv
  rcases hv with ⟨i, hi⟩
  use e i
  constructor
  · rw [nonneg_on_C_iff]
    intro j
    dsimp [e]
    split_ifs <;> linarith
  · rw [dot_comm, dot_e]
    exact hi

end Course21241
