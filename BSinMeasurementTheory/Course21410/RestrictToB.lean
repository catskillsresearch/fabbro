import Mathlib
import BSinMeasurementTheory.Course21410.PositiveExtension

namespace Course21410

namespace ScottMeasurementTheory

variable {B : Type*} [BooleanAlgebra B]

/-- Restriction of a Stone-space functional back to \(B\). -/
noncomputable def restrictToB (Λ : StoneFunctional B) : B → ℝ :=
  fun a => Λ (stoneIndicator a)

theorem restrict_top (Λ : StoneFunctional B)
    (hone : stoneIndicator (⊤ : B) = fun _ => 1)
    (h1 : Λ (fun _ => 1) = 1) :
    restrictToB Λ ⊤ = 1 := by
  dsimp [restrictToB]
  simpa [hone] using h1

theorem restrict_bot (Λ : StoneFunctional B)
    (hbot : stoneIndicator (⊥ : B) = 0) :
    restrictToB Λ ⊥ = 0 := by
  dsimp [restrictToB]
  simp [hbot]

theorem restrict_mono (Λ : StoneFunctional B) {R : B → B → Prop}
    (hR : AgreesWith Λ R) {a b : B} (hab : R a b) :
    restrictToB Λ a ≤ restrictToB Λ b := by
  have := hR a b hab
  dsimp [restrictToB, preferenceDiff] at this ⊢
  simpa [map_sub, sub_nonneg] using this

end ScottMeasurementTheory

end Course21410
