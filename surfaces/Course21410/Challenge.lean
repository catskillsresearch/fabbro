/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Challenge — Course 21-410 / 21-599
-/

namespace Course21410

/-- Ultrafilters on a Boolean algebra, as used for the Stone space. -/
structure IsUltrafilter {B : Type*} [BooleanAlgebra B] (U : Set B) : Prop where
  mem_top : ⊤ ∈ U
  not_mem_bot : ⊥ ∉ U
  mem_inf : ∀ {a b}, a ∈ U → b ∈ U → a ⊓ b ∈ U
  upward : ∀ {a b}, a ∈ U → a ≤ b → b ∈ U
  mem_or : ∀ a, a ∈ U ∨ aᶜ ∈ U

/-- Points of the Stone space. -/
def Stone (B : Type*) [BooleanAlgebra B] :=
  { U : Set B // IsUltrafilter U }

variable {B : Type*} [BooleanAlgebra B]

open scoped Classical

/-- Indicator of a basic clopen, as a function on the Stone space. -/
noncomputable def stoneIndicator (a : B) : Stone B → ℝ :=
  fun U => if a ∈ U.1 then (1 : ℝ) else 0

/-- Preference difference \(\mathbf{1}_{\widehat{b}} - \mathbf{1}_{\widehat{a}}\). -/
noncomputable def preferenceDiff (a b : B) : Stone B → ℝ :=
  stoneIndicator b - stoneIndicator a

/-- A linear functional on functions on the Stone space. -/
abbrev StoneFunctional (B : Type*) [BooleanAlgebra B] :=
  (Stone B → ℝ) →ₗ[ℝ] ℝ

/-- Positivity of a functional. -/
def IsPositive (Λ : StoneFunctional B) : Prop :=
  ∀ f : Stone B → ℝ, (∀ U, 0 ≤ f U) → 0 ≤ Λ f

/-- Preference agreement: \(a \precsim b\) implies \(\Lambda(\mathbf{1}_{\widehat{b}} - \mathbf{1}_{\widehat{a}}) \ge 0\). -/
def AgreesWith (Λ : StoneFunctional B) (R : B → B → Prop) : Prop :=
  ∀ a b, R a b → 0 ≤ Λ (preferenceDiff a b)

/-- Restriction of a Stone-space functional back to \(B\). -/
noncomputable def restrictToB (Λ : StoneFunctional B) : B → ℝ :=
  fun a => Λ (stoneIndicator a)

/-- Wrap-up of the infinite-algebra extension. -/
theorem representation_on_B (Λ : StoneFunctional B) (hpos : IsPositive Λ)
    {R : B → B → Prop} (hR : AgreesWith Λ R) {a b : B} (hab : R a b) :
    0 ≤ restrictToB Λ a ∧ restrictToB Λ a ≤ restrictToB Λ b := by
  sorry

end Course21410
