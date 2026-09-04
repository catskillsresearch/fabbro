import Mathlib

open BigOperators
open Finset

namespace Course21241

/-!
# Convex Cones, Dual Bases, and Separation

This file formalizes:
(a) Explicit basis and dual basis constructions for `V = Fin 3 → ℝ`.
(b) Riesz representation under the standard inner product and separation of `v ∉ C`.
(c) The dual cone `C*` is a convex cone, identified in the dual basis coordinates.
-/

abbrev V := Fin 3 → ℝ

/-- The non-negative orthant cone C in V = ℝ³ -/
def C : Set V := {x | ∀ i : Fin 3, 0 ≤ x i}

/-! ### Part (a): Basis and Dual Basis Construction -/

/-- Standard primal basis vectors of V -/
def e (i : Fin 3) : V := fun j => if i = j then 1 else 0

/-- Explicit dual basis functionals e_star i ∈ V* -/
def e_star (i : Fin 3) : V →ₗ[ℝ] ℝ where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Duality relation between primal and dual bases: e_star i (e j) = δ_{ij} -/
theorem e_star_apply_e (i j : Fin 3) :
    e_star i (e j) = if i = j then (1 : ℝ) else 0 := by
  dsimp [e_star, e]
  fin_cases i <;> fin_cases j <;> rfl

/-- Every vector x ∈ V expands uniquely in the primal basis -/
theorem vector_eq_sum (x : V) :
    x = ∑ i : Fin 3, x i • e i := by
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_three]
  fin_cases j <;> { dsimp [e]; ring }

/-- The basis vectors {e 0, e 1, e 2} are linearly independent -/
theorem e_linearIndependent :
    LinearIndependent ℝ e := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := congr_fun hg i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e, Pi.zero_apply] at h
  rw [Finset.sum_eq_single_of_mem i hi] at h
  · simp only [ite_true, mul_one] at h
    exact h
  · intro j _ hj
    simp only [hj, ite_false, mul_zero]

/-- Every linear functional φ ∈ V* expands uniquely in the dual basis -/
theorem dual_eq_sum (φ : V →ₗ[ℝ] ℝ) :
    φ = ∑ i : Fin 3, φ (e i) • e_star i := by
  apply LinearMap.ext
  intro x
  have hx : x = ∑ i : Fin 3, x i • e i := vector_eq_sum x
  conv_lhs => rw [hx]
  rw [map_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  dsimp [e_star]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.map_smul, smul_eq_mul, mul_comm]

/-! ### Part (b): Inner Product and Separating Functional -/

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

/-! ### Numerical Separation Example -/

/-- A concrete point v = (-1, 1, 1) ∉ C -/
def v_example : V := fun i =>
  if i = 0 then -1 else 1

/-- Separating vector u = e 0 = (1, 0, 0) -/
def u_example : V := e 0

theorem v_example_not_mem_C : v_example ∉ C := by
  intro h
  have h0 := h 0
  dsimp [v_example] at h0
  linarith

theorem dot_u_example_v_example : dot u_example v_example = -1 := by
  dsimp [u_example, dot]
  rw [Fin.sum_univ_three]
  dsimp [e, v_example]
  ring

theorem u_example_separates_v_example : dot u_example v_example < 0 := by
  rw [dot_u_example_v_example]
  linarith

theorem u_example_nonneg_on_C (c : V) (hc : c ∈ C) : 0 ≤ dot u_example c := by
  dsimp [u_example, dot]
  rw [Fin.sum_univ_three]
  dsimp [e]
  have hc0 := hc 0
  linarith

/-! ### Part (c): The Dual Cone C* and its Dual Basis Representation -/

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
