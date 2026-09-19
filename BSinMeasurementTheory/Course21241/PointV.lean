import Mathlib
import BSinMeasurementTheory.Course21241.Space

namespace Course21241

def v : V := fun i => if i = 0 then -1 else 1

lemma v_zero : v 0 = -1 := rfl
lemma v_one  : v 1 = 1  := rfl
lemma v_two  : v 2 = 1  := rfl

theorem v_coords : v 0 = -1 ∧ v 1 = 1 ∧ v 2 = 1 :=
  ⟨v_zero, v_one, v_two⟩

theorem v_zero_neg : v 0 < 0 := by
  rw [v_zero]
  norm_num

theorem v_not_mem_C : v ∉ C := by
  intro hc
  have h0 : 0 ≤ v 0 := hc 0
  rw [v_zero] at h0
  norm_num at h0

end Course21241
