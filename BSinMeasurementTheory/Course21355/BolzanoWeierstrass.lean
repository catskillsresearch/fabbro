import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Real
import BSinMeasurementTheory.Course21355.MonotoneConvergence
import BSinMeasurementTheory.Course21355.PeakPoints

open Filter Topology

namespace Course21355

noncomputable section

/-- Bolzano–Weierstrass: a bounded real sequence has a convergent subsequence.
    The peak-point lemmas sit beside this wrap-up; Mathlib supplies compactness
    of a closed bounded interval. -/
theorem bolzano_weierstrass (x : ℕ → ℝ) (h_bdd : ∃ M : ℝ, ∀ n, |x n| ≤ M) :
    ∃ (φ : ℕ → ℕ) (l : ℝ), StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 l) := by
  rcases h_bdd with ⟨M, hM⟩
  have h_mem : ∀ n, x n ∈ Set.Icc (-M) M := fun n => abs_le.mp (hM n)
  have h_freq : ∃ᶠ n in atTop, x n ∈ Set.Icc (-M) M :=
    Filter.frequently_atTop.2 (fun N => ⟨N, le_rfl, h_mem N⟩)
  rcases isCompact_Icc.tendsto_subseq' h_freq with ⟨l, _, φ, hφ_mono, hφ_lim⟩
  exact ⟨φ, l, hφ_mono, hφ_lim⟩

/-- A peak point of a bounded sequence is an upper bound for the tail. -/
theorem peak_tail_le_of_bounded (x : ℕ → ℝ) {m : ℕ} (hm : IsPeakPoint x m)
    {k : ℕ} (hk : m < k) : x k ≤ x m :=
  peak_bounds_tail x hm hk

end

end Course21355
