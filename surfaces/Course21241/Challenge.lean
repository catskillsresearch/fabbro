/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Challenge — Course 21-241
-/

namespace Course21241

abbrev V := Fin 3 → ℝ

/-- The non-negative orthant cone C in V = ℝ³ -/
def C : Set V := {x | ∀ i : Fin 3, 0 ≤ x i}

/-- Standard primal basis vectors of V. -/
def e (i : Fin 3) : V := fun j => if i = j then 1 else 0

/-- The basis vectors \(\{e\,0, e\,1, e\,2\}\) are linearly independent. -/
theorem e_linearIndependent :
    LinearIndependent ℝ e := by
  sorry

end Course21241
