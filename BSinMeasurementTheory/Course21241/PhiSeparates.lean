import Mathlib
import BSinMeasurementTheory.Course21241.DotAtV
import BSinMeasurementTheory.Course21241.DotOnC

namespace Course21241

def phi_u : V →ₗ[ℝ] ℝ := toDual u

theorem phi_u_v_eval : phi_u v = -1 := by
  change dot u v = -1
  exact dot_u_v_eval

theorem phi_u_c_eval (c : V) : phi_u c = c 0 := by
  change dot u c = c 0
  exact dot_u_c_eq_coord c

theorem phi_u_v_neg : phi_u v < 0 := by
  rw [phi_u_v_eval]
  norm_num

theorem phi_u_c_nonneg (c : V) (hc : c ∈ C) : 0 ≤ phi_u c := by
  rw [phi_u_c_eval]
  exact hc 0

theorem phi_u_separates (c : V) (hc : c ∈ C) :
    phi_u v < 0 ∧ 0 ≤ phi_u c :=
  ⟨phi_u_v_neg, phi_u_c_nonneg c hc⟩

theorem phi_u_separation_chain (c : V) (hc : c ∈ C) :
    phi_u v = -1 ∧ phi_u v < 0 ∧ 0 ≤ phi_u c ∧ phi_u c = c 0 :=
  ⟨phi_u_v_eval, phi_u_v_neg, phi_u_c_nonneg c hc, phi_u_c_eval c⟩

end Course21241
