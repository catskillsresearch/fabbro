import Mathlib.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Real.Basic

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

end

end Course21640
