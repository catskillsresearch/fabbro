import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.ByContra

namespace Course21355

/-- An index \(m\) is a peak point if every later term is \(\le x_m\). -/
def IsPeakPoint (x : ℕ → ℝ) (m : ℕ) : Prop :=
  ∀ n, m < n → x n ≤ x m

/-- A peak point bounds the entire tail. -/
theorem peak_bounds_tail (x : ℕ → ℝ) {m k : ℕ} (hm : IsPeakPoint x m) (hk : m < k) :
    x k ≤ x m :=
  hm k hk

/-- An infinite set of peaks is unbounded in \(\mathbb{N}\). -/
theorem infinite_peaks_unbounded (x : ℕ → ℝ)
    (hinf : {m | IsPeakPoint x m}.Infinite) (N : ℕ) :
    ∃ n, N ≤ n ∧ IsPeakPoint x n := by
  by_contra h
  push Not at h
  have hsub : {m | IsPeakPoint x m} ⊆ {n : ℕ | n < N} := by
    intro n hn
    exact lt_of_not_ge fun hge => h n hge hn
  exact hinf ((Set.finite_Iio N).subset hsub)

/-- If there are no peaks after \(N\), the sequence keeps ascending. -/
theorem ascent_of_no_late_peaks (x : ℕ → ℝ) {N k : ℕ}
    (hN : ∀ m ≥ N, ¬ IsPeakPoint x m) (hk : N ≤ k) :
    ∃ n, k < n ∧ x k < x n := by
  have : ¬ IsPeakPoint x k := hN k hk
  simp [IsPeakPoint] at this
  exact this

end Course21355
