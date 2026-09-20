import Mathlib.LinearAlgebra.Basis.Basic
import BSinMeasurementTheory.Course21241.Basis

namespace Course21241

def u : V := e 0

lemma u_zero : u 0 = 1 := rfl
lemma u_one  : u 1 = 0 := rfl
lemma u_two  : u 2 = 0 := rfl

theorem u_eq_e_zero : u = e 0 := rfl

theorem u_coords : u 0 = 1 ∧ u 1 = 0 ∧ u 2 = 0 :=
  ⟨u_zero, u_one, u_two⟩

end Course21241
