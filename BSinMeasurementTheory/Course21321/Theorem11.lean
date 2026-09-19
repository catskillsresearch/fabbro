import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import BSinMeasurementTheory.Course21321.ScottPair

namespace Course21321

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Scott's Theorem 1.1: a separable pair satisfies real non-cancellation. -/
theorem NoCancellation.of_separable [DecidableEq V] {P : ScottPair ℝ V}
    [hsol : Separable P] : NoCancellation P where
  no_cancel c d hc hd hd_pos hsum := by
    rcases hsol.exists_sep with ⟨f, hfX, hfY⟩
    have f_linear_sum :
        f ((∑ x ∈ P.X, c x • x) + (∑ y ∈ P.Y, d y • y)) = 0 := by
      rw [hsum, map_zero]
    rw [map_add, map_sum, map_sum] at f_linear_sum
    have f_terms_X : ∀ x ∈ P.X, 0 ≤ c x * f x := by
      intro x hx
      exact mul_nonneg (hc x hx) (hfX x hx)
    have f_terms_Y : ∀ y ∈ P.Y, 0 ≤ d y * f y := by
      intro y hy
      exact mul_nonneg (hd y hy) (le_of_lt (hfY y hy))
    have exists_strict_pos : ∃ y0 ∈ P.Y, 0 < d y0 * f y0 := by
      by_contra! hall
      have hall_zero : ∀ y ∈ P.Y, d y = 0 := by
        intro y hy
        have hle := hall y hy
        have hnonneg := hd y hy
        have hfpos := hfY y hy
        obtain heq | hgt := le_iff_eq_or_lt.mp hnonneg
        · exact heq.symm
        · exfalso
          have : 0 < d y * f y := mul_pos hgt hfpos
          linarith
      have sum_zero : ∑ y ∈ P.Y, d y = 0 := Finset.sum_eq_zero hall_zero
      linarith
    rcases exists_strict_pos with ⟨y0, hy0, hy0_pos⟩
    have sum_Y_pos : 0 < ∑ y ∈ P.Y, f (d y • y) := by
      rw [← Finset.add_sum_erase _ _ hy0]
      have h_rest : 0 ≤ ∑ y ∈ P.Y.erase y0, f (d y • y) := by
        apply Finset.sum_nonneg
        intro y hy
        have hyY := Finset.mem_of_mem_erase hy
        rw [map_smul, smul_eq_mul]
        exact f_terms_Y y hyY
      rw [map_smul, smul_eq_mul]
      linarith
    have hX_nonneg : 0 ≤ ∑ x ∈ P.X, f (c x • x) := by
      apply Finset.sum_nonneg
      intro x hx
      rw [map_smul, smul_eq_mul]
      exact f_terms_X x hx
    have total_pos :
        0 < (∑ x ∈ P.X, f (c x • x)) + (∑ y ∈ P.Y, f (d y • y)) := by
      linarith
    linarith

/-- Witness form: a separating functional yields non-cancellation. -/
theorem SeparatingFunctional.noCancellation [DecidableEq V]
    (P : SeparatingFunctional ℝ V) : NoCancellation P.toScottPair :=
  NoCancellation.of_separable

end Course21321
