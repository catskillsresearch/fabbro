import Mathlib

open Filter Topology

namespace Course21355

noncomputable section

/-!
### (a) Bolzano–Weierstrass Theorem
Mathlib derives sequential compactness of closed bounded intervals in ℝ from the
completeness axiom / Heine-Borel compactness (`IsCompact.tendsto_subseq'`).
-/

theorem bolzano_weierstrass (x : ℕ → ℝ) (h_bdd : ∃ M : ℝ, ∀ n, |x n| ≤ M) :
    ∃ (φ : ℕ → ℕ) (l : ℝ), StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 l) := by
  rcases h_bdd with ⟨M, hM⟩
  have h_mem : ∀ n, x n ∈ Set.Icc (-M) M := fun n => abs_le.mp (hM n)
  have h_freq : ∃ᶠ n in atTop, x n ∈ Set.Icc (-M) M :=
    Filter.frequently_atTop.2 (fun N => ⟨N, le_rfl, h_mem N⟩)
  rcases isCompact_Icc.tendsto_subseq' h_freq with ⟨l, _, φ, hφ_mono, hφ_lim⟩
  exact ⟨φ, l, hφ_mono, hφ_lim⟩

/-!
### (b) Existence and Characterization of limsup and liminf
The tail supremum sequence y_k = ⨆ n, x (n + k) is monotone non-increasing,
and the tail infimum sequence z_k = ⨅ n, x (n + k) is monotone non-decreasing.
Both converge to the limsup and liminf via monotone convergence in ℝ.
-/

def tailSup (x : ℕ → ℝ) (k : ℕ) : ℝ := ⨆ n : ℕ, x (n + k)
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

/-!
### (c) Divergence of x_n = (-1)^n via an ε-argument (ε = 1)
-/

def altSeq (n : ℕ) : ℝ := (-1 : ℝ) ^ n

lemma altSeq_even (k : ℕ) : altSeq (2 * k) = 1 := by
  dsimp [altSeq]
  rw [pow_mul]
  have : (-1 : ℝ) ^ 2 = 1 := by norm_num
  rw [this, one_pow]

lemma altSeq_odd (k : ℕ) : altSeq (2 * k + 1) = -1 := by
  dsimp [altSeq]
  rw [pow_add, pow_one, pow_mul]
  have : (-1 : ℝ) ^ 2 = 1 := by norm_num
  rw [this, one_pow, one_mul]

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

/-!
### (d) Compactness of [a, b] from Open Covers
-/

theorem compact_Icc (a b : ℝ) : IsCompact (Set.Icc a b) :=
  isCompact_Icc

/-!
### Numerical Calculations
Computable evaluation of the alternating values:
-/
def altSeqZ (n : ℕ) : ℤ := (-1 : ℤ) ^ n

#eval altSeqZ 0  -- 1
#eval altSeqZ 1  -- -1
#eval altSeqZ 2  -- 1
#eval altSeqZ 3  -- -1


end

end Course21355
