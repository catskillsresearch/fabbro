import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Rat.Defs

open scoped BigOperators

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

/-- Inequality-form linear program: minimize `cᵀx` subject to `Ax ≥ b`, `x ≥ 0`. -/
structure LinearProgram (m n : ℕ) where
  A : Fin m → Fin n → ℚ
  b : Fin m → ℚ
  c : Fin n → ℚ

end LPDuality

end Course21292
