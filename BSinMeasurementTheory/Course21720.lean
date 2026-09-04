import Mathlib.Topology.ContinuousMap.Compact

namespace Course21720

/-!
# Positive Linear Functionals, Riesz Representation, and Stone Duality

This file formalizes:
1. Positivity implies boundedness for linear functionals on `C(X, ℝ)` with `X` compact.
2. The finite additivity of measures induced on Boolean algebras via Stone duality.
3. Concrete numerical calculations verifying bounds and additivity.
-/

section Theory

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- A linear functional on `C(X, ℝ)` is positive if `(∀ x, 0 ≤ f x) → 0 ≤ Λ f`. -/
def IsPositiveLinearMap (Λ : C(X, ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ f : C(X, ℝ), (∀ x : X, 0 ≤ f x) → 0 ≤ Λ f

/-- Part (a): A positive linear functional on `C(X, ℝ)` for compact `X`
    is bounded by `Λ 1 * ‖f‖`. -/
theorem positive_linear_map_bounded (Λ : C(X, ℝ) →ₗ[ℝ] ℝ) (hpos : IsPositiveLinearMap Λ)
    (f : C(X, ℝ)) : |Λ f| ≤ Λ 1 * ‖f‖ := by
  have h1 : ∀ x : X, 0 ≤ (‖f‖ • (1 : C(X, ℝ)) - f) x := by
    intro x
    rw [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
        smul_eq_mul, mul_one]
    have := ContinuousMap.apply_le_norm f x
    linarith
  have h2 : ∀ x : X, 0 ≤ (‖f‖ • (1 : C(X, ℝ)) + f) x := by
    intro x
    rw [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
        smul_eq_mul, mul_one]
    have := ContinuousMap.neg_norm_le_apply f x
    linarith
  have l1 := hpos (‖f‖ • (1 : C(X, ℝ)) - f) h1
  have l2 := hpos (‖f‖ • (1 : C(X, ℝ)) + f) h2
  rw [map_sub, LinearMap.map_smul, smul_eq_mul, sub_nonneg] at l1
  rw [map_add, LinearMap.map_smul, smul_eq_mul, ← sub_le_iff_le_add'] at l2
  rw [abs_le]
  constructor
  · rw [mul_comm]
    linarith
  · rw [mul_comm]
    linarith

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
  nonneg' b := hpos (χ b) (h_pos_ind b)
  bot_zero' := by
    rw [h_bot, map_zero]
  add_disjoint' a b h := by
    rw [h_disj a b h, map_add]

end Theory

/-!
### Concrete Numerical Calculations in Lean 4
-/

section ConcreteExample

/-- Linear map instance for the concrete functional `Λ(f) = 3 f(0) + 2 f(1)`. -/
def lambda_linear : (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun f := 3 * f.1 + 2 * f.2
  map_add' x y := by
    dsimp
    ring
  map_smul' c x := by
    dsimp
    ring

/-- Value of Λ on the constant function 1 = (1, 1). -/
theorem concrete_lambda_one : lambda_linear (1, 1) = 5 := by
  dsimp [lambda_linear]
  norm_num

/-- Values on the 4 elements of the Boolean algebra P({0, 1}). -/
theorem concrete_measure_bot : lambda_linear (0, 0) = 0 := by
  dsimp [lambda_linear]
  norm_num

theorem concrete_measure_singleton_0 : lambda_linear (1, 0) = 3 := by
  dsimp [lambda_linear]
  norm_num

theorem concrete_measure_singleton_1 : lambda_linear (0, 1) = 2 := by
  dsimp [lambda_linear]
  norm_num

theorem concrete_measure_top : lambda_linear (1, 1) = 5 := by
  dsimp [lambda_linear]
  norm_num

/-- Verification of finite additivity for disjoint singletons:
    μ({0} ∪ {1}) = μ({0}) + μ({1}) = 3 + 2 = 5. -/
theorem concrete_additivity :
    lambda_linear (1 + 0, 0 + 1) = lambda_linear (1, 0) + lambda_linear (0, 1) := by
  dsimp [lambda_linear]
  norm_num

end ConcreteExample


end Course21720
