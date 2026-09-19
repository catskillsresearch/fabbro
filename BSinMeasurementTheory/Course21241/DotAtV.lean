import Mathlib
import BSinMeasurementTheory.Course21241.PointV
import BSinMeasurementTheory.Course21241.SeparatingU
import BSinMeasurementTheory.Course21241.Separation

open BigOperators
open Finset

namespace Course21241

theorem dot_u_v_sum :
    dot u v = ∑ i : Fin 3, u i * v i := rfl

theorem dot_u_v_expansion :
    dot u v = (1 : ℝ) * (-1) + 0 * 1 + 0 * 1 := by
  dsimp [dot]
  rw [Fin.sum_univ_three]
  rw [u_zero, u_one, u_two, v_zero, v_one, v_two]

theorem dot_u_v_eval : dot u v = -1 := by
  rw [dot_u_v_expansion]
  ring

theorem dot_u_v_neg : dot u v < 0 := by
  rw [dot_u_v_eval]
  norm_num

end Course21241
