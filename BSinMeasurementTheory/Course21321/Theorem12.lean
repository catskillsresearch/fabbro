import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import BSinMeasurementTheory.Course21321.ScottPair

namespace Course21321

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Scott's finite cancellation axiom: integer weights cannot sum to zero
unless they all vanish on `Y`. A property of a rational `ScottPair`. -/
class CombinatorialNoCancellation (P : ScottPair ℚ V) : Prop where
  no_cancel : ∀ (n m : V → ℕ),
    (0 < ∑ y ∈ P.Y, m y) →
    (∑ x ∈ P.X, (n x : ℚ) • x) + (∑ y ∈ P.Y, (m y : ℚ) • y) ≠ 0

/-- Scott's Theorem 1.2: rational separability implies combinatorial
non-cancellation. -/
theorem CombinatorialNoCancellation.of_separable [DecidableEq V]
    {P : ScottPair ℚ V} [hsol : Separable P] :
    CombinatorialNoCancellation P where
  no_cancel n m hm_pos hsum := by
    rcases hsol.exists_sep with ⟨f, hfX, hfY⟩
    have f_sum :
        f ((∑ x ∈ P.X, (n x : ℚ) • x) + (∑ y ∈ P.Y, (m y : ℚ) • y)) = 0 := by
      rw [hsum, map_zero]
    rw [map_add, map_sum, map_sum] at f_sum
    have f_terms_X : ∀ x ∈ P.X, 0 ≤ (n x : ℚ) * f x := by
      intro x hx
      exact mul_nonneg (Nat.cast_nonneg (n x)) (hfX x hx)
    have exists_strict_pos : ∃ y0 ∈ P.Y, 0 < (m y0 : ℚ) * f y0 := by
      by_contra! hall
      have hall_zero : ∀ y ∈ P.Y, m y = 0 := by
        intro y hy
        have hle := hall y hy
        have hfpos := hfY y hy
        by_contra hm_ne
        have hm_gt : 0 < (m y : ℚ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm_ne)
        have : 0 < (m y : ℚ) * f y := mul_pos hm_gt hfpos
        linarith
      have sum_zero : ∑ y ∈ P.Y, m y = 0 := Finset.sum_eq_zero hall_zero
      linarith
    rcases exists_strict_pos with ⟨y0, hy0, hy0_pos⟩
    have sum_Y_pos : 0 < ∑ y ∈ P.Y, f ((m y : ℚ) • y) := by
      rw [← Finset.add_sum_erase _ _ hy0]
      have h_rest : 0 ≤ ∑ y ∈ P.Y.erase y0, f ((m y : ℚ) • y) := by
        apply Finset.sum_nonneg
        intro y hy
        have hyY := Finset.mem_of_mem_erase hy
        rw [map_smul, smul_eq_mul]
        exact mul_nonneg (Nat.cast_nonneg (m y)) (le_of_lt (hfY y hyY))
      rw [map_smul, smul_eq_mul]
      linarith
    have hX_nonneg : 0 ≤ ∑ x ∈ P.X, f ((n x : ℚ) • x) := by
      apply Finset.sum_nonneg
      intro x hx
      rw [map_smul, smul_eq_mul]
      exact f_terms_X x hx
    have total_pos :
        0 < (∑ x ∈ P.X, f ((n x : ℚ) • x)) + (∑ y ∈ P.Y, f ((m y : ℚ) • y)) := by
      linarith
    linarith

end Course21321
