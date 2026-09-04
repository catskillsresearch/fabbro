import Mathlib

open BigOperators

namespace Course21321

namespace Scott1964

/-!
## Section 1: Theorem 1.1 (Separating Hyperplane / Real Duality Form)
Quantified universally over an arbitrary real vector space `V`.
-/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A real linear functional strictly separating `Y` from 0 while keeping `X` non-negative. -/
def RealSolvable (X Y : Finset V) : Prop :=
  ∃ f : V →ₗ[ℝ] ℝ, (∀ x ∈ X, 0 ≤ f x) ∧ (∀ y ∈ Y, 0 < f y)

/-- The real non-cancellation condition: no non-trivial non-negative linear combination sums to 0. -/
def RealNoCancellation (X Y : Finset V) : Prop :=
  ∀ (c_coeff d_coeff : V → ℝ),
    (∀ x ∈ X, 0 ≤ c_coeff x) →
    (∀ y ∈ Y, 0 ≤ d_coeff y) →
    (0 < ∑ y ∈ Y, d_coeff y) →
    (∑ x ∈ X, c_coeff x • x) + (∑ y ∈ Y, d_coeff y • y) ≠ 0

/-- Scott's Theorem 1.1: Solvability implies real non-cancellation. -/
theorem theorem_1_1_real_separation [DecidableEq V] {X Y : Finset V}
    (hsol : RealSolvable X Y) : RealNoCancellation X Y := by
  intro c_coeff d_coeff hc hd hd_pos hsum
  rcases hsol with ⟨f, hfX, hfY⟩
  have f_linear_sum : f ((∑ x ∈ X, c_coeff x • x) + (∑ y ∈ Y, d_coeff y • y)) = 0 := by
    rw [hsum, map_zero]
  rw [map_add, map_sum, map_sum] at f_linear_sum
  have f_terms_X : ∀ x ∈ X, 0 ≤ c_coeff x * f x := by
    intro x hx
    exact mul_nonneg (hc x hx) (hfX x hx)
  have f_terms_Y : ∀ y ∈ Y, 0 ≤ d_coeff y * f y := by
    intro y hy
    exact mul_nonneg (hd y hy) (le_of_lt (hfY y hy))
  have exists_strict_pos : ∃ y0 ∈ Y, 0 < d_coeff y0 * f y0 := by
    by_contra! hall
    have hall_zero : ∀ y ∈ Y, d_coeff y = 0 := by
      intro y hy
      have hle := hall y hy
      have hnonneg := hd y hy
      have hfpos := hfY y hy
      obtain heq | hgt := le_iff_eq_or_lt.mp hnonneg
      · exact heq.symm
      · exfalso
        have : 0 < d_coeff y * f y := mul_pos hgt hfpos
        linarith
    have sum_zero : ∑ y ∈ Y, d_coeff y = 0 :=
      Finset.sum_eq_zero hall_zero
    linarith
  rcases exists_strict_pos with ⟨y0, hy0, hy0_pos⟩
  have sum_Y_pos : 0 < ∑ y ∈ Y, f (d_coeff y • y) := by
    rw [← Finset.add_sum_erase _ _ hy0]
    have h_rest : 0 ≤ ∑ y ∈ Y.erase y0, f (d_coeff y • y) := by
      apply Finset.sum_nonneg
      intro y hy
      have hyY := Finset.mem_of_mem_erase hy
      rw [map_smul, smul_eq_mul]
      exact f_terms_Y y hyY
    rw [map_smul, smul_eq_mul]
    linarith
  have hX_nonneg : 0 ≤ ∑ x ∈ X, f (c_coeff x • x) := by
    apply Finset.sum_nonneg
    intro x hx
    rw [map_smul, smul_eq_mul]
    exact f_terms_X x hx
  have total_pos : 0 < (∑ x ∈ X, f (c_coeff x • x)) + (∑ y ∈ Y, f (d_coeff y • y)) := by
    linarith
  linarith

/-!
## Section 2: Theorem 1.2 (Combinatorial / Integer Cancellation Form)
Quantified universally over an arbitrary rational vector space `V_Q`.
-/

variable {V_Q : Type*} [AddCommGroup V_Q] [Module ℚ V_Q]

/-- Existence of a rational separating linear functional. -/
def RatSolvable (X Y : Finset V_Q) : Prop :=
  ∃ f : V_Q →ₗ[ℚ] ℚ, (∀ x ∈ X, 0 ≤ f x) ∧ (∀ y ∈ Y, 0 < f y)

/-- Scott's Combinatorial Finite Cancellation condition with natural-number multipliers. -/
def CombinatorialNoCancellation (X Y : Finset V_Q) : Prop :=
  ∀ (n m : V_Q → ℕ),
    (0 < ∑ y ∈ Y, m y) →
    (∑ x ∈ X, (n x : ℚ) • x) + (∑ y ∈ Y, (m y : ℚ) • y) ≠ 0

/-- Scott's Theorem 1.2: Rational solvability implies combinatorial non-cancellation. -/
theorem theorem_1_2_combinatorial_cancellation [DecidableEq V_Q] {X Y : Finset V_Q}
    (hsol : RatSolvable X Y) : CombinatorialNoCancellation X Y := by
  intro n m hm_pos hsum
  rcases hsol with ⟨f, hfX, hfY⟩
  have f_sum : f ((∑ x ∈ X, (n x : ℚ) • x) + (∑ y ∈ Y, (m y : ℚ) • y)) = 0 := by
    rw [hsum, map_zero]
  rw [map_add, map_sum, map_sum] at f_sum
  have f_terms_X : ∀ x ∈ X, 0 ≤ (n x : ℚ) * f x := by
    intro x hx
    exact mul_nonneg (Nat.cast_nonneg (n x)) (hfX x hx)
  have exists_strict_pos : ∃ y0 ∈ Y, 0 < (m y0 : ℚ) * f y0 := by
    by_contra! hall
    have hall_zero : ∀ y ∈ Y, m y = 0 := by
      intro y hy
      have hle := hall y hy
      have hfpos := hfY y hy
      by_contra hm_ne
      have hm_gt : 0 < (m y : ℚ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm_ne)
      have : 0 < (m y : ℚ) * f y := mul_pos hm_gt hfpos
      linarith
    have sum_zero : ∑ y ∈ Y, m y = 0 :=
      Finset.sum_eq_zero hall_zero
    linarith
  rcases exists_strict_pos with ⟨y0, hy0, hy0_pos⟩
  have sum_Y_pos : 0 < ∑ y ∈ Y, f ((m y : ℚ) • y) := by
    rw [← Finset.add_sum_erase _ _ hy0]
    have h_rest : 0 ≤ ∑ y ∈ Y.erase y0, f ((m y : ℚ) • y) := by
      apply Finset.sum_nonneg
      intro y hy
      have hyY := Finset.mem_of_mem_erase hy
      rw [map_smul, smul_eq_mul]
      exact mul_nonneg (Nat.cast_nonneg (m y)) (le_of_lt (hfY y hyY))
    rw [map_smul, smul_eq_mul]
    linarith
  have hX_nonneg : 0 ≤ ∑ x ∈ X, f ((n x : ℚ) • x) := by
    apply Finset.sum_nonneg
    intro x hx
    rw [map_smul, smul_eq_mul]
    exact f_terms_X x hx
  have total_pos : 0 < (∑ x ∈ X, f ((n x : ℚ) • x)) + (∑ y ∈ Y, f ((m y : ℚ) • y)) := by
    linarith
  linarith

/-!
## Section 3: Theorem 1.3 (Equivalence of Combinatorial and Rational Conditions)
-/

/-- Rational non-cancellation condition over non-negative rational coefficients. -/
def RatNoCancellation (X Y : Finset V_Q) : Prop :=
  ∀ (c_coeff d_coeff : V_Q → ℚ),
    (∀ x ∈ X, 0 ≤ c_coeff x) →
    (∀ y ∈ Y, 0 ≤ d_coeff y) →
    (0 < ∑ y ∈ Y, d_coeff y) →
    (∑ x ∈ X, c_coeff x • x) + (∑ y ∈ Y, d_coeff y • y) ≠ 0

/-- Equivalence: Rational non-cancellation implies combinatorial non-cancellation. -/
theorem combinatorial_of_rat_no_cancellation {X Y : Finset V_Q}
    (hrat : RatNoCancellation X Y) : CombinatorialNoCancellation X Y := by
  intro n m hm_pos hsum
  have hc : ∀ x ∈ X, 0 ≤ (n x : ℚ) := fun x _ => Nat.cast_nonneg (n x)
  have hd : ∀ y ∈ Y, 0 ≤ (m y : ℚ) := fun y _ => Nat.cast_nonneg (m y)
  have hd_sum : (0 : ℚ) < ∑ y ∈ Y, (m y : ℚ) := by
    have hpos : (0 : ℚ) < ((∑ y ∈ Y, m y : ℕ) : ℚ) := Nat.cast_pos.mpr hm_pos
    rwa [Nat.cast_sum] at hpos
  exact hrat (fun x => (n x : ℚ)) (fun y => (m y : ℚ)) hc hd hd_sum hsum

end Scott1964


end Course21321
