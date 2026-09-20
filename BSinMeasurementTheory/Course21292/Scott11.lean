import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import BSinMeasurementTheory.Course21292.WeakDuality

open scoped BigOperators

namespace Course21292

namespace LPDuality

/-- Feasibility of \(Vy \ge \mathbf{1}\): a separating functional after scaling. -/
def ScottPrimalFeasible {m n : ℕ} (V : Fin m → Fin n → ℚ) (y : Fin n → ℚ) : Prop :=
  ∀ i, (1 : ℚ) ≤ matMulVec V y i

/-- Nonnegative weights, not all zero, with \(V^\top\lambda = 0\). -/
def ScottDualWitness {m n : ℕ} (V : Fin m → Fin n → ℚ) (lam : Fin m → ℚ) : Prop :=
  NonNeg lam ∧ (∃ i, 0 < lam i) ∧ matTransposeMulVec V lam = 0

/-- If a separator exists, no nontrivial nonnegative dependence can. -/
theorem scott11_no_witness_of_feasible {m n : ℕ} (V : Fin m → Fin n → ℚ)
    (y : Fin n → ℚ) (hy : ScottPrimalFeasible V y)
    (lam : Fin m → ℚ) (hlam : NonNeg lam) (hdep : matTransposeMulVec V lam = 0) :
    ∀ i, lam i = 0 := by
  have h_left : dot lam (matMulVec V y) = 0 := by
    rw [transpose_dot_assoc V lam y, hdep]
    simp [dot]
  have h_ge : (∑ i : Fin m, lam i) ≤ dot lam (matMulVec V y) := by
    dsimp [dot]
    apply Finset.sum_le_sum
    intro i _
    have hlami : 0 ≤ lam i := hlam.nonneg i
    have hfeas : (1 : ℚ) ≤ matMulVec V y i := hy i
    nlinarith
  have h_sum : (∑ i : Fin m, lam i) ≤ 0 := by
    simpa [h_left] using h_ge
  intro i
  have hrest : 0 ≤ ∑ j : Fin m, lam j := Finset.sum_nonneg fun j _ => hlam.nonneg j
  have : ∑ j : Fin m, lam j = 0 := le_antisymm h_sum hrest
  exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hlam.nonneg j).mp this i (Finset.mem_univ _)

/-- A dual witness rules out a separator. -/
theorem scott11_infeasible_of_witness {m n : ℕ} (V : Fin m → Fin n → ℚ)
    (lam : Fin m → ℚ) (hlam : ScottDualWitness V lam) :
    ¬ ∃ y, ScottPrimalFeasible V y := by
  rintro ⟨y, hy⟩
  rcases hlam with ⟨hnonneg, ⟨i, hi⟩, hdep⟩
  have h0 := scott11_no_witness_of_feasible V y hy lam hnonneg hdep i
  linarith

end LPDuality

end Course21292
