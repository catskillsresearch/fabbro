/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Basic.Real.Basic

/-!
# Challenge — Course 21-640
-/

namespace Course21640

noncomputable section

/-- A sublinear functional on a real vector space. -/
structure SublinearFunctional (V : Type*) [AddCommGroup V] [Module ℝ V] where
  toFun : V → ℝ
  map_add_le : ∀ x y : V, toFun (x + y) ≤ toFun x + toFun y
  map_smul_nonneg : ∀ (c : ℝ) (x : V), 0 ≤ c → toFun (c • x) = c * toFun x

instance (V : Type*) [AddCommGroup V] [Module ℝ V] :
    CoeFun (SublinearFunctional V) (fun _ => V → ℝ) where
  coe p := p.toFun

/-- Wrap-up of part (b): a dominated extension that fixes the unit is positive. -/
theorem positive_extension
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (φ : V →ₗ[ℝ] ℝ) (one : V) (C : ℝ) (hC : 0 ≤ C)
    (h_one : φ one = C)
    (h_dom : ∀ f : V, φ f ≤ C * ‖f‖)
    (f : V) (hf_norm : ‖‖f‖ • one - f‖ ≤ ‖f‖) :
    0 ≤ φ f := by
  sorry

end

end Course21640
