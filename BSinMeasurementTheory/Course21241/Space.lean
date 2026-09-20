import Mathlib.Data.Real.Basic

namespace Course21241

abbrev V := Fin 3 → ℝ

/-- The non-negative orthant cone C in V = ℝ³ -/
def C : Set V := {x | ∀ i : Fin 3, 0 ≤ x i}

end Course21241
