import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import BSinMeasurementTheory.Course21241.Basis

open BigOperators
open Finset

namespace Course21241

/-- The dual cone C* in V* -/
def dualCone (C : Set V) : Set (V →ₗ[ℝ] ℝ) :=
  {φ | ∀ c ∈ C, 0 ≤ φ c}

theorem dualCone_smul_mem {φ : V →ₗ[ℝ] ℝ} (hφ : φ ∈ dualCone C) {a : ℝ} (ha : 0 ≤ a) :
    a • φ ∈ dualCone C := by
  intro c hc_mem
  simp only [LinearMap.smul_apply, smul_eq_mul]
  exact mul_nonneg ha (hφ c hc_mem)

theorem dualCone_add_mem {φ ψ : V →ₗ[ℝ] ℝ} (hφ : φ ∈ dualCone C) (hψ : ψ ∈ dualCone C) :
    φ + ψ ∈ dualCone C := by
  intro c hc_mem
  simp only [LinearMap.add_apply]
  exact add_nonneg (hφ c hc_mem) (hψ c hc_mem)

theorem dualCone_conic_combination {φ ψ : V →ₗ[ℝ] ℝ} (hφ : φ ∈ dualCone C) (hψ : ψ ∈ dualCone C)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • φ + b • ψ ∈ dualCone C := by
  intro c hc_mem
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hφ c hc_mem)) (mul_nonneg hb (hψ c hc_mem))

theorem mem_dualCone_iff (φ : V →ₗ[ℝ] ℝ) :
    φ ∈ dualCone C ↔ ∀ i : Fin 3, 0 ≤ φ (e i) := by
  constructor
  · intro hφ i
    have hei : e i ∈ C := by
      intro j
      dsimp [e]
      split_ifs <;> linarith
    exact hφ (e i) hei
  · intro hφ c hc
    have hc_sum : c = ∑ i : Fin 3, c i • e i := vector_eq_sum c
    conv_rhs => rw [hc_sum]
    rw [map_sum]
    simp only [LinearMap.map_smul, smul_eq_mul]
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hc i) (hφ i)

/-- Dual cone represented as non-negative linear combinations of {e_star i} -/
def dualCone_representation : Set (V →ₗ[ℝ] ℝ) :=
  {φ | ∃ a : Fin 3 → ℝ, (∀ i, 0 ≤ a i) ∧ φ = ∑ i : Fin 3, a i • e_star i}

theorem dualCone_eq_representation :
    dualCone C = dualCone_representation := by
  ext φ
  constructor
  · intro hφ
    rw [mem_dualCone_iff] at hφ
    use fun i => φ (e i)
    refine ⟨hφ, ?_⟩
    exact dual_eq_sum φ
  · rintro ⟨a, ha, rfl⟩
    rw [mem_dualCone_iff]
    intro i
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    have h_sum : (∑ j : Fin 3, a j * e_star j (e i)) = a i := by
      rw [Fin.sum_univ_three]
      fin_cases i <;> simp [e_star_apply_e]
    rw [h_sum]
    exact ha i

end Course21241
