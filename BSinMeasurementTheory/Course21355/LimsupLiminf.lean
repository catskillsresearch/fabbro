import Mathlib

open Filter Topology

namespace Course21355

noncomputable section

/-- Tail supremum $y_k = \sup_{n\ge k} x_n$. A construction on sequences, not a
new structure. -/
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

theorem limsup_liminf_exist (x : ℕ → ℝ) (m M : ℝ) (h : ∀ n, m ≤ x n ∧ x n ≤ M) :
    (∃ L_sup : ℝ, Tendsto (tailSup x) atTop (𝓝 L_sup)) ∧
    (∃ L_inf : ℝ, Tendsto (tailInf x) atTop (𝓝 L_inf)) := by
  have h_sup_bdd : BddBelow (Set.range (tailSup x)) := by
    refine ⟨m, fun y ⟨k, hk⟩ => ?_⟩
    subst hk
    have h1 : m ≤ x (0 + k) := (h (0 + k)).1
    have hb : BddAbove (Set.range (fun n : ℕ => x (n + k))) :=
      ⟨M, fun r ⟨i, hi⟩ => hi ▸ (h (i + k)).2⟩
    have h2 : x (0 + k) ≤ tailSup x k := le_ciSup hb 0
    exact le_trans h1 h2
  have h_inf_bdd : BddAbove (Set.range (tailInf x)) := by
    refine ⟨M, fun y ⟨k, hk⟩ => ?_⟩
    subst hk
    have hb : BddBelow (Set.range (fun n : ℕ => x (n + k))) :=
      ⟨m, fun r ⟨i, hi⟩ => hi ▸ (h (i + k)).1⟩
    have h1 : tailInf x k ≤ x (0 + k) := ciInf_le hb 0
    have h2 : x (0 + k) ≤ M := (h (0 + k)).2
    exact le_trans h1 h2
  exact ⟨⟨⨅ k, tailSup x k, tendsto_atTop_ciInf (tailSup_antitone x M (fun n => (h n).2)) h_sup_bdd⟩,
         ⟨⨆ k, tailInf x k, tendsto_atTop_ciSup (tailInf_monotone x m (fun n => (h n).1)) h_inf_bdd⟩⟩

end

end Course21355
