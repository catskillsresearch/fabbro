import Mathlib

namespace Course21355

/-- Closed bounded intervals in `ℝ` are compact. -/
theorem compact_Icc (a b : ℝ) : IsCompact (Set.Icc a b) :=
  isCompact_Icc

end Course21355
