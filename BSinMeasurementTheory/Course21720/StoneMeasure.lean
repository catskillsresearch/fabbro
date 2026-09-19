import Mathlib.Topology.ContinuousMap.Compact
import BSinMeasurementTheory.Course21720.Boundedness

namespace Course21720

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Part (c): Definition of a finitely additive measure on a Boolean algebra `B`. -/
structure FinitelyAdditiveMeasure (B : Type*) [BooleanAlgebra B] where
  toFun : B → ℝ
  nonneg' : ∀ b, 0 ≤ toFun b
  bot_zero' : toFun ⊥ = 0
  add_disjoint' : ∀ a b, Disjoint a b → toFun (a ⊔ b) = toFun a + toFun b

/-- Given an assignment of continuous indicator functions `χ : B → C(X, ℝ)` preserving
    disjoint sums and the empty set, any positive linear functional induces a finitely
    additive measure on `B`. -/
def measureOfStoneRepresentation {B : Type*} [BooleanAlgebra B]
    (χ : B → C(X, ℝ))
    (h_bot : χ ⊥ = 0)
    (h_disj : ∀ a b : B, Disjoint a b → χ (a ⊔ b) = χ a + χ b)
    (h_pos_ind : ∀ b : B, ∀ x : X, 0 ≤ χ b x)
    (Λ : C(X, ℝ) →ₗ[ℝ] ℝ) (hpos : IsPositiveLinearMap Λ) :
    FinitelyAdditiveMeasure B where
  toFun b := Λ (χ b)
  nonneg' b := hpos.pos (χ b) (h_pos_ind b)
  bot_zero' := by
    rw [h_bot, map_zero]
  add_disjoint' a b h := by
    rw [h_disj a b h, map_add]

end Course21720
