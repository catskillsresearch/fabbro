import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Course21640

noncomputable section

/-- The sup-norm on ℝ². -/
def supNorm (v : ℝ × ℝ) : ℝ := max (|v.1|) (|v.2|)

/-- The sublinear dominating functional on ℝ² associated with weight C = 1. -/
def p_concrete (v : ℝ × ℝ) : ℝ := supNorm v

/-- Subadditivity check for concrete p on ℝ². -/
theorem p_concrete_subadditive (u v : ℝ × ℝ) :
    p_concrete (u + v) ≤ p_concrete u + p_concrete v := by
  dsimp [p_concrete, supNorm]
  apply max_le
  · have h2 : |u.1 + v.1| ≤ |u.1| + |v.1| := abs_add_le u.1 v.1
    have hu : |u.1| ≤ max (|u.1|) (|u.2|) := le_max_left _ _
    have hv : |v.1| ≤ max (|v.1|) (|v.2|) := le_max_left _ _
    linarith
  · have h2 : |u.2 + v.2| ≤ |u.2| + |v.2| := abs_add_le u.2 v.2
    have hu : |u.2| ≤ max (|u.1|) (|u.2|) := le_max_right _ _
    have hv : |v.2| ≤ max (|v.1|) (|v.2|) := le_max_right _ _
    linarith

/-- Positive homogeneity of concrete p. -/
theorem p_concrete_smul (c : ℝ) (hc : 0 ≤ c) (v : ℝ × ℝ) :
    p_concrete (c • v) = c * p_concrete v := by
  dsimp [p_concrete, supNorm]
  rw [abs_mul, abs_mul, abs_of_nonneg hc]
  exact (mul_max_of_nonneg (|v.1|) (|v.2|) hc).symm

/-- Extension functional φ(x, y) = (1/3) x + (2/3) y. -/
def phi_ext (v : ℝ × ℝ) : ℝ := (1 / 3) * v.1 + (2 / 3) * v.2

/-- Verification that φ extends φ₀ on the diagonal subspace M = span{(1,1)}. -/
theorem phi_ext_extends (c : ℝ) : phi_ext (c, c) = c := by
  dsimp [phi_ext]
  ring

/-- Verification of dominance for φ: φ(x, y) ≤ max(|x|, |y|). -/
theorem phi_ext_dominated (x y : ℝ) : phi_ext (x, y) ≤ p_concrete (x, y) := by
  dsimp [phi_ext, p_concrete, supNorm]
  have hx : x ≤ |x| := le_abs_self x
  have hy : y ≤ |y| := le_abs_self y
  have hx_max : |x| ≤ max (|x|) (|y|) := le_max_left _ _
  have hy_max : |y| ≤ max (|x|) (|y|) := le_max_right _ _
  linarith

/-- Positivity verification: if x ≥ 0 and y ≥ 0, then φ(x, y) ≥ 0. -/
theorem phi_ext_positive (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ phi_ext (x, y) := by
  dsimp [phi_ext]
  positivity

end

end Course21640
