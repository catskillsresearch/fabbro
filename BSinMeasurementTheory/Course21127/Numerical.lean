import Mathlib
import BSinMeasurementTheory.Course21127.NonzeroDenomInt
import BSinMeasurementTheory.Course21127.ToRat

namespace Course21127

-- Example 1: (1, 2) ~ (2, 4) since 1 * 4 = 2 * 2 = 4
def pair1 : NonzeroDenomInt := ⟨1, 2, by decide⟩
def pair2 : NonzeroDenomInt := ⟨2, 4, by decide⟩

example : Rel pair1 pair2 := by
  dsimp [Rel, pair1, pair2]

-- Example 2: Both pairs map to 1/2 in ℚ under toRat
example : toRat pair1 = 1 / 2 := by
  norm_num [toRat, pair1]

example : toRat pair2 = 1 / 2 := by
  norm_num [toRat, pair2]

-- Example 3: Minimal element in the set {1/2, 1/3} is 1/3
example : min (1 / 2 : ℚ) (1 / 3) = 1 / 3 := by
  norm_num

end Course21127
