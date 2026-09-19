import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Rat.Defs
import BSinMeasurementTheory.Course21321.ScottPair
import BSinMeasurementTheory.Course21321.Theorem12

namespace Course21321

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Scott's Theorem 1.3 (one direction): rational non-cancellation implies
the combinatorial finite-cancellation axiom. -/
theorem CombinatorialNoCancellation.of_noCancellation {P : ScottPair ℚ V}
    [hrat : NoCancellation P] : CombinatorialNoCancellation P where
  no_cancel n m hm_pos hsum := by
    have hc : ∀ x ∈ P.X, 0 ≤ (n x : ℚ) := fun x _ => Nat.cast_nonneg (n x)
    have hd : ∀ y ∈ P.Y, 0 ≤ (m y : ℚ) := fun y _ => Nat.cast_nonneg (m y)
    have hd_sum : (0 : ℚ) < ∑ y ∈ P.Y, (m y : ℚ) := by
      have hpos : (0 : ℚ) < ((∑ y ∈ P.Y, m y : ℕ) : ℚ) := Nat.cast_pos.mpr hm_pos
      rwa [Nat.cast_sum] at hpos
    exact hrat.no_cancel (fun x => (n x : ℚ)) (fun y => (m y : ℚ)) hc hd hd_sum hsum

end Course21321
