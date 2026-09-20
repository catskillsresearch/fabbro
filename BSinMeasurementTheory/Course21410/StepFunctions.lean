import Mathlib
import BSinMeasurementTheory.Course21410.StoneSpace

namespace Course21410

namespace ScottMeasurementTheory

variable {B : Type*} [BooleanAlgebra B]

open scoped Classical

/-- Indicator of a basic clopen, as a function on the Stone space. -/
noncomputable def stoneIndicator (a : B) : Stone B → ℝ :=
  fun U => if a ∈ U.1 then (1 : ℝ) else 0

/-- Pointwise nonnegative cone on functions on the Stone space. -/
def NonnegCone : Set (Stone B → ℝ) :=
  {f | ∀ U, 0 ≤ f U}

/-- Preference difference \(\mathbf{1}_{\widehat{b}} - \mathbf{1}_{\widehat{a}}\). -/
noncomputable def preferenceDiff (a b : B) : Stone B → ℝ :=
  stoneIndicator b - stoneIndicator a

theorem stoneIndicator_nonneg (a : B) : stoneIndicator a ∈ NonnegCone := by
  intro U
  dsimp [stoneIndicator]
  split_ifs <;> norm_num

theorem preferenceDiff_apply (a b : B) (U : Stone B) :
    preferenceDiff a b U = stoneIndicator b U - stoneIndicator a U :=
  rfl

end ScottMeasurementTheory

end Course21410
