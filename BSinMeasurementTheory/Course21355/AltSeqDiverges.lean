import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import BSinMeasurementTheory.Course21355.AltSeqValues

open Filter Topology

namespace Course21355

noncomputable section

theorem altSeq_no_limit : ¬ ∃ (L : ℝ), Tendsto altSeq atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  rw [Metric.tendsto_atTop] at hL
  have h_eps : (0 : ℝ) < 1 := by norm_num
  rcases hL 1 h_eps with ⟨N, hN⟩
  have h_even : dist (altSeq (2 * N)) L < 1 := hN (2 * N) (Nat.le_mul_of_pos_left _ (by norm_num))
  have h_odd : dist (altSeq (2 * N + 1)) L < 1 := hN (2 * N + 1) (by omega)
  rw [altSeq_even N, Real.dist_eq] at h_even
  rw [altSeq_odd N, Real.dist_eq] at h_odd
  have h_triangle : (2 : ℝ) ≤ |1 - L| + |-1 - L| := by
    have h2 : (2 : ℝ) = (1 - L) - (-1 - L) := by ring
    rw [h2]
    exact le_trans (le_abs_self _) (abs_sub (1 - L) (-1 - L))
  have h_lt : |1 - L| + |-1 - L| < 2 := by linarith
  linarith

end

end Course21355
