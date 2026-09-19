import Mathlib

open Filter Topology

namespace Course21355

noncomputable section

/-- Tail supremum $y_k = \sup_{n\ge k} x_n$. -/
def tailSup (x : ℕ → ℝ) (k : ℕ) : ℝ := ⨆ n : ℕ, x (n + k)

/-- Tail infimum $z_k = \inf_{n\ge k} x_n$. -/
def tailInf (x : ℕ → ℝ) (k : ℕ) : ℝ := ⨅ n : ℕ, x (n + k)

theorem tailSup_antitone (x : ℕ → ℝ) (M : ℝ) (hM : ∀ n, x n ≤ M) :
    Antitone (tailSup x) := by
  intro j k hjk
  apply ciSup_le
  intro n
  have h_eq : n + k = (n + (k - j)) + j := by omega
  rw [h_eq]
  have h_bdd : BddAbove (Set.range (fun i : ℕ => x (i + j))) :=
    ⟨M, fun r ⟨i, hi⟩ => hi ▸ hM (i + j)⟩
  exact le_ciSup h_bdd (n + (k - j))

theorem tailInf_monotone (x : ℕ → ℝ) (m : ℝ) (hm : ∀ n, m ≤ x n) :
    Monotone (tailInf x) := by
  intro j k hjk
  apply le_ciInf
  intro n
  have h_eq : n + k = (n + (k - j)) + j := by omega
  rw [h_eq]
  have h_bdd : BddBelow (Set.range (fun i : ℕ => x (i + j))) :=
    ⟨m, fun r ⟨i, hi⟩ => hi ▸ hm (i + j)⟩
  exact ciInf_le h_bdd (n + (k - j))

end

end Course21355
