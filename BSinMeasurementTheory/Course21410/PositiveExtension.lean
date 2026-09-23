import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.BooleanAlgebra.Basic
import BSinMeasurementTheory.Course21410.StepFunctions

namespace Course21410

variable {B : Type*} [BooleanAlgebra B]

/-- A linear functional on functions on the Stone space. -/
abbrev StoneFunctional (B : Type*) [BooleanAlgebra B] :=
  (Stone B → ℝ) →ₗ[ℝ] ℝ

/-- Positivity of a functional. -/
def IsPositive (Λ : StoneFunctional B) : Prop :=
  ∀ f : Stone B → ℝ, (∀ U, 0 ≤ f U) → 0 ≤ Λ f

/-- Preference agreement: \(a \precsim b\) implies \(\Lambda(\mathbf{1}_{\widehat{b}} - \mathbf{1}_{\widehat{a}}) \ge 0\). -/
def AgreesWith (Λ : StoneFunctional B) (R : B → B → Prop) : Prop :=
  ∀ a b, R a b → 0 ≤ Λ (preferenceDiff a b)

theorem positive_on_indicators (Λ : StoneFunctional B) (hpos : IsPositive Λ) (a : B) :
    0 ≤ Λ (stoneIndicator a) :=
  hpos _ (stoneIndicator_nonneg a)

end Course21410
