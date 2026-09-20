import Mathlib
import BSinMeasurementTheory.Course21292.LinearProgram

open scoped BigOperators

namespace Course21292

namespace LPDuality

def A_inst : Fin 3 → Fin 3 → ℚ
  | 0, 0 => 2 | 0, 1 => 1 | 0, 2 => 0
  | 1, 0 => 1 | 1, 1 => 2 | 1, 2 => 0
  | 2, 0 => 0 | 2, 1 => 0 | 2, 2 => 1

def b_inst : Fin 3 → ℚ
  | 0 => 3 | 1 => 3 | 2 => 1

def c_inst : Fin 3 → ℚ
  | 0 => 1 | 1 => 1 | 2 => 2

/-- Concrete Scott-type \(3\times 3\) program. -/
def scottInstance : LinearProgram 3 3 where
  A := A_inst
  b := b_inst
  c := c_inst

end LPDuality

end Course21292
