import Mathlib

open Filter Topology

namespace Course21355

noncomputable section

/-- Bolzano–Weierstrass: a bounded real sequence has a convergent subsequence.
Mathlib obtains this from compactness of a closed bounded interval. -/
theorem bolzano_weierstrass (x : ℕ → ℝ) (h_bdd : ∃ M : ℝ, ∀ n, |x n| ≤ M) :
    ∃ (φ : ℕ → ℕ) (l : ℝ), StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 l) := by
  rcases h_bdd with ⟨M, hM⟩
  have h_mem : ∀ n, x n ∈ Set.Icc (-M) M := fun n => abs_le.mp (hM n)
  have h_freq : ∃ᶠ n in atTop, x n ∈ Set.Icc (-M) M :=
    Filter.frequently_atTop.2 (fun N => ⟨N, le_rfl, h_mem N⟩)
  rcases isCompact_Icc.tendsto_subseq' h_freq with ⟨l, _, φ, hφ_mono, hφ_lim⟩
  exact ⟨φ, l, hφ_mono, hφ_lim⟩

end

end Course21355
