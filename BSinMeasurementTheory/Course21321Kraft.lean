import Mathlib

open BigOperators

namespace Course21321Kraft

noncomputable section

namespace KraftExample

/-!
### 1. Definition of the Difference Vectors in ℝ⁵
Let Ω = {0, 1, 2, 3, 4}.
We define 4 difference vectors corresponding to comparative probability claims:
  y₁ = (-1, -1,  1,  1,  0)
  y₂ = (-1,  1, -1,  0,  1)
  y₃ = ( 1, -1, -1,  1,  0)
  y₄ = ( 1,  1,  1, -2, -1)
-/

def y1 : Fin 5 → ℝ := ![-1, -1,  1,  1,  0]
def y2 : Fin 5 → ℝ := ![-1,  1, -1,  0,  1]
def y3 : Fin 5 → ℝ := ![ 1, -1, -1,  1,  0]
def y4 : Fin 5 → ℝ := ![ 1,  1,  1, -2, -1]

/-!
### 2. Numerical Cancellation Check: ∑ yᵢ = 0
Verified coordinate-by-coordinate using `fin_cases` and `norm_num`.
-/

theorem kraft_sum_zero : y1 + y2 + y3 + y4 = 0 := by
  ext i
  fin_cases i <;> norm_num [y1, y2, y3, y4]

/-!
### 3. Proof that No Linear Functional Can Strictly Separate These Vectors
Applying any linear functional `f` with `f(yᵢ) > 0` produces a contradiction:
  0 = f(0) = f(y₁ + y₂ + y₃ + y₄) = f(y₁) + f(y₂) + f(y₃) + f(y₄) > 0
-/

theorem no_strictly_positive_functional (f : (Fin 5 → ℝ) →ₗ[ℝ] ℝ)
    (h1 : 0 < f y1) (h2 : 0 < f y2) (h3 : 0 < f y3) (h4 : 0 < f y4) : False := by
  have h_sum : f (y1 + y2 + y3 + y4) = 0 := by
    rw [kraft_sum_zero, map_zero]
  have h_pos : 0 < f (y1 + y2 + y3 + y4) := by
    rw [map_add, map_add, map_add]
    linarith
  linarith

/-!
### 4. Connection to Scott's Solvability Condition
Defining Y = {y₁, y₂, y₃, y₄}, we prove `¬ RealSolvable ∅ Y`.
-/

def Y : Finset (Fin 5 → ℝ) := {y1, y2, y3, y4}

/-- Scott's Real Solvability on (∅, Y) fails. -/
theorem kraft_not_solvable :
    ¬ (∃ f : (Fin 5 → ℝ) →ₗ[ℝ] ℝ, ∀ y ∈ Y, 0 < f y) := by
  intro ⟨f, hf⟩
  have hy1 : y1 ∈ Y := by simp [Y]
  have hy2 : y2 ∈ Y := by simp [Y]
  have hy3 : y3 ∈ Y := by simp [Y]
  have hy4 : y4 ∈ Y := by simp [Y]
  exact no_strictly_positive_functional f (hf y1 hy1) (hf y2 hy2) (hf y3 hy3) (hf y4 hy4)

end KraftExample


end

end Course21321Kraft
