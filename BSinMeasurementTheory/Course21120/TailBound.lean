import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Tactic.Linarith
import BSinMeasurementTheory.Course21120.Existence

open Real intervalIntegral

namespace Course21120

/-- The comparison majorant integrates to an arctan increment. -/
theorem majorant_integral (M x : ℝ) :
    ∫ t in M..x, (1 : ℝ) / (1 + t ^ 2) = arctan x - arctan M := by
  simp [one_div, integral_inv_one_add_sq]

/-- Remaining majorant mass on $[M,x]$ is at most the improper tail
$\pi/2 - \arctan M$. -/
theorem tail_mass_le (M x : ℝ) (_hMx : M ≤ x) :
    arctan x - arctan M ≤ Real.pi / 2 - arctan M := by
  nlinarith [arctan_lt_pi_div_two x]

end Course21120
