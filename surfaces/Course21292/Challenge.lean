/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Rat.Defs

open scoped BigOperators

/-!
# Challenge — Course 21-292

Imports match `BSinMeasurementTheory.Course21292.LinearProgram` so Zero/instance
paths in theorem types match Solution (Palomar Comparator).
-/

namespace Course21292

namespace LPDuality

/-- Vector inner product over Rational numbers for Fin n. -/
def dot {n : ℕ} (u v : Fin n → ℚ) : ℚ :=
  ∑ i : Fin n, u i * v i

/-- Non-negativity of a vector: a property of an existing `Fin n → ℚ`. -/
class NonNeg {n : ℕ} (v : Fin n → ℚ) : Prop where
  nonneg : ∀ i : Fin n, 0 ≤ v i

/-- Matrix-vector multiplication (A * x). -/
def matMulVec {m n : ℕ} (A : Fin m → Fin n → ℚ) (x : Fin n → ℚ) : Fin m → ℚ :=
  fun i => dot (A i) x

/-- Transpose matrix-vector multiplication (Aᵀ * y). -/
def matTransposeMulVec {m n : ℕ} (A : Fin m → Fin n → ℚ) (y : Fin m → ℚ) : Fin n → ℚ :=
  fun j => ∑ i : Fin m, y i * A i j

/-- If a primal-feasible \(x\) and dual-feasible \(y\) attain the same value,
    then both are optimal: this is strong duality in certificate form. -/
theorem strong_duality_of_equal_value {m n : ℕ}
    (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ) (c : Fin n → ℚ)
    (x : Fin n → ℚ) (y : Fin m → ℚ)
    (hx_nonneg : NonNeg x) (hy_nonneg : NonNeg y)
    (h_primal_feas : ∀ i, b i ≤ matMulVec A x i)
    (h_dual_feas : ∀ j, matTransposeMulVec A y j ≤ c j)
    (h_eq : dot b y = dot c x) :
    (∀ x' : Fin n → ℚ, NonNeg x' → (∀ i, b i ≤ matMulVec A x' i) →
      dot c x ≤ dot c x') ∧
    (∀ y' : Fin m → ℚ, NonNeg y' → (∀ j, matTransposeMulVec A y' j ≤ c j) →
      dot b y' ≤ dot b y) := by
  sorry

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
  sorry

end LPDuality

end Course21292
