import Mathlib
import BSinMeasurementTheory.Course21651.StoneMap

set_option linter.unusedSectionVars false

open Topology Set

namespace Course21651

namespace StoneRepresentation

abbrev TwoAlgebra := Fin 2 → Bool

def u0_fun : TwoAlgebra → Bool := fun s => s 0
def u1_fun : TwoAlgebra → Bool := fun s => s 1

theorem u0_isHom : IsBooleanHom u0_fun :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem u1_isHom : IsBooleanHom u1_fun :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

def u0 : StoneSpace TwoAlgebra := ⟨u0_fun, u0_isHom⟩
def u1 : StoneSpace TwoAlgebra := ⟨u1_fun, u1_isHom⟩

def elem_bot  : TwoAlgebra := fun _ => false
def elem_zero : TwoAlgebra := fun i => (i == 0)
def elem_one  : TwoAlgebra := fun i => (i == 1)
def elem_top  : TwoAlgebra := fun _ => true

theorem example_bot : stoneMap TwoAlgebra elem_bot = ∅ :=
  stoneMap_bot TwoAlgebra

theorem example_top : stoneMap TwoAlgebra elem_top = univ :=
  stoneMap_top TwoAlgebra

theorem example_u0_in_zero : u0 ∈ stoneMap TwoAlgebra elem_zero := rfl

theorem example_u1_not_in_zero : u1 ∉ stoneMap TwoAlgebra elem_zero := by
  intro h; cases h

theorem example_u1_in_one : u1 ∈ stoneMap TwoAlgebra elem_one := rfl

theorem example_u0_not_in_one : u0 ∉ stoneMap TwoAlgebra elem_one := by
  intro h; cases h

end StoneRepresentation

end Course21651
