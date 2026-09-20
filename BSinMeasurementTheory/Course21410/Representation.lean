import Mathlib.Order.BooleanAlgebra.Basic
import BSinMeasurementTheory.Course21410.RestrictToB

namespace Course21410

namespace ScottMeasurementTheory

variable {B : Type*} [BooleanAlgebra B]

/-- Wrap-up of the infinite-algebra extension: restriction of a positive
    preference-preserving functional is a monotone assignment on \(B\). -/
theorem representation_on_B (Λ : StoneFunctional B) (hpos : IsPositive Λ)
    {R : B → B → Prop} (hR : AgreesWith Λ R) {a b : B} (hab : R a b) :
    0 ≤ restrictToB Λ a ∧ restrictToB Λ a ≤ restrictToB Λ b :=
  ⟨positive_on_indicators Λ hpos a, restrict_mono Λ hR hab⟩

end ScottMeasurementTheory

end Course21410
