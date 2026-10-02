/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Challenge — Course 21-720
-/

namespace Course21720

variable {X : Type*} [TopologicalSpace X]

/-- A linear functional on `C(X, ℝ)` is positive if `(∀ x, 0 ≤ f x) → 0 ≤ Λ f`. -/
class IsPositiveLinearMap {X : Type*} [TopologicalSpace X] (Λ : C(X, ℝ) →ₗ[ℝ] ℝ) : Prop where
  pos : ∀ f : C(X, ℝ), (∀ x : X, 0 ≤ f x) → 0 ≤ Λ f

/-- Outer content of an open set from a positive functional, as in the
    Riesz–Markov construction. -/
noncomputable def openContent [CompactSpace X] (Λ : C(X, ℝ) →ₗ[ℝ] ℝ) (U : Set X) : ℝ :=
  sSup {Λ f | (f : C(X, ℝ)) (_ : ∀ x, 0 ≤ f x) (_ : ∀ x, x ∈ U → f x ≤ 1)
    (_ : ∀ x, x ∉ U → f x = 0)}

/-- A positive functional is monotone. -/
theorem riesz_comparison (Λ : C(X, ℝ) →ₗ[ℝ] ℝ) (hpos : IsPositiveLinearMap Λ)
    (f g : C(X, ℝ)) (h : ∀ x, f x ≤ g x) :
    Λ f ≤ Λ g := by
  sorry

end Course21720
