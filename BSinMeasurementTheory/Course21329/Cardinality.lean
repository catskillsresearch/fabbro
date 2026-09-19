import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic

namespace Course21329

open Cardinal

/-- (c) Cardinal-arithmetic argument:
If `|B| = ℵ₀` and `2^ℵ₀ ≤ |S(B)| ≤ 2^|B|`, then `|S(B)| = 2^ℵ₀`. -/
theorem ultrafilter_cardinality {S_B : Type*} (card_B : Cardinal)
    (hB : card_B = aleph0)
    (h_upper : #S_B ≤ 2 ^ card_B)
    (h_lower : 2 ^ aleph0 ≤ #S_B) :
    #S_B = 2 ^ aleph0 := by
  rw [hB] at h_upper
  exact le_antisymm h_upper h_lower

end Course21329
