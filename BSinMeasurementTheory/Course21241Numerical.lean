import Mathlib

open BigOperators
open Finset

namespace Course21241Numerical

abbrev V := Fin 3 → ℝ

/-- The convex cone C = {x ∈ ℝ³ : x₁ ≥ 0, x₂ ≥ 0, x₃ ≥ 0} -/
def C : Set V := {x | ∀ i : Fin 3, 0 ≤ x i}

/-- Standard basis vector e_i -/
def e (i : Fin 3) : V := fun j => if i = j then 1 else 0

/-- Standard Euclidean inner product on V -/
def dot (u v : V) : ℝ := ∑ i : Fin 3, u i * v i

/-- Embedding of V into V* via the inner product -/
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

/-!
### 1. Choice of point v ∉ C:
    v = (-1, 1, 1) ⟹ v₀ = -1 < 0 ⟹ v ∉ C
-/

def v : V := fun i => if i = 0 then -1 else 1

lemma v_zero : v 0 = -1 := rfl
lemma v_one  : v 1 = 1  := rfl
lemma v_two  : v 2 = 1  := rfl

/-- Coordinates of v are (-1, 1, 1) -/
theorem v_coords : v 0 = -1 ∧ v 1 = 1 ∧ v 2 = 1 :=
  ⟨v_zero, v_one, v_two⟩

/-- v₀ = -1 < 0 -/
theorem v_zero_neg : v 0 < 0 := by
  rw [v_zero]
  norm_num

/-- v ∉ C because v 0 < 0 -/
theorem v_not_mem_C : v ∉ C := by
  intro hc
  have h0 : 0 ≤ v 0 := hc 0
  rw [v_zero] at h0
  norm_num at h0

/-!
### 2. Separating vector u ∈ V:
    u = e₀ = (1, 0, 0)
-/

def u : V := e 0

lemma u_zero : u 0 = 1 := rfl
lemma u_one  : u 1 = 0 := rfl
lemma u_two  : u 2 = 0 := rfl

/-- u is e₀ -/
theorem u_eq_e_zero : u = e 0 := rfl

/-- Coordinates of u are (1, 0, 0) -/
theorem u_coords : u 0 = 1 ∧ u 1 = 0 ∧ u 2 = 0 :=
  ⟨u_zero, u_one, u_two⟩

/-!
### 3. Inner product value at v:
    ⟨u, v⟩ = ∑_{i=0}² u_i v_i = (1)(-1) + (0)(1) + (0)(1) = -1 < 0
-/

theorem dot_u_v_sum :
    dot u v = ∑ i : Fin 3, u i * v i := rfl

/-- ⟨u, v⟩ = (1)(-1) + (0)(1) + (0)(1) -/
theorem dot_u_v_expansion :
    dot u v = (1 : ℝ) * (-1) + 0 * 1 + 0 * 1 := by
  dsimp [dot]
  rw [Fin.sum_univ_three]
  rw [u_zero, u_one, u_two, v_zero, v_one, v_two]

/-- ⟨u, v⟩ = -1 -/
theorem dot_u_v_eval : dot u v = -1 := by
  rw [dot_u_v_expansion]
  ring

/-- ⟨u, v⟩ < 0 -/
theorem dot_u_v_neg : dot u v < 0 := by
  rw [dot_u_v_eval]
  norm_num

/-!
### 4. Inner product on arbitrary c ∈ C:
    ⟨u, c⟩ = ∑_{i=0}² u_i c_i = (1) c₀ + (0) c₁ + (0) c₂ = c₀ ≥ 0
-/

theorem dot_u_c_sum (c : V) :
    dot u c = ∑ i : Fin 3, u i * c i := rfl

/-- ⟨u, c⟩ = (1) c₀ + (0) c₁ + (0) c₂ -/
theorem dot_u_c_expansion (c : V) :
    dot u c = (1 : ℝ) * c 0 + 0 * c 1 + 0 * c 2 := by
  dsimp [dot]
  rw [Fin.sum_univ_three]
  rw [u_zero, u_one, u_two]

/-- ⟨u, c⟩ = c₀ -/
theorem dot_u_c_eq_coord (c : V) :
    dot u c = c 0 := by
  rw [dot_u_c_expansion]
  ring

/-- ⟨u, c⟩ ≥ 0 for all c ∈ C because c₀ ≥ 0 -/
theorem dot_u_c_nonneg (c : V) (hc : c ∈ C) :
    0 ≤ dot u c := by
  rw [dot_u_c_eq_coord]
  exact hc 0

/-!
### 5. Linear functional separation:
    φ_u(v) = -1 < 0 ≤ c₀ = φ_u(c)  for all c ∈ C
-/

/-- The linear functional φ_u corresponding to u under the standard inner product -/
def phi_u : V →ₗ[ℝ] ℝ := toDual u

/-- φ_u(v) = -1 -/
theorem phi_u_v_eval : phi_u v = -1 := by
  change dot u v = -1
  exact dot_u_v_eval

/-- φ_u(c) = c₀ -/
theorem phi_u_c_eval (c : V) : phi_u c = c 0 := by
  change dot u c = c 0
  exact dot_u_c_eq_coord c

/-- φ_u(v) < 0 -/
theorem phi_u_v_neg : phi_u v < 0 := by
  rw [phi_u_v_eval]
  norm_num

/-- 0 ≤ φ_u(c) for all c ∈ C -/
theorem phi_u_c_nonneg (c : V) (hc : c ∈ C) : 0 ≤ phi_u c := by
  rw [phi_u_c_eval]
  exact hc 0

/-- Separation: φ_u(v) < 0 ≤ φ_u(c) for all c ∈ C -/
theorem phi_u_separates (c : V) (hc : c ∈ C) :
    phi_u v < 0 ∧ 0 ≤ phi_u c :=
  ⟨phi_u_v_neg, phi_u_c_nonneg c hc⟩

/-- Complete separation chain: φ_u(v) = -1 < 0 ≤ φ_u(c) = c₀ -/
theorem phi_u_separation_chain (c : V) (hc : c ∈ C) :
    phi_u v = -1 ∧ phi_u v < 0 ∧ 0 ≤ phi_u c ∧ phi_u c = c 0 :=
  ⟨phi_u_v_eval, phi_u_v_neg, phi_u_c_nonneg c hc, phi_u_c_eval c⟩


end Course21241Numerical
