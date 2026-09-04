import Mathlib
namespace Course21373Numerical

/-! ### Numerical / Computational Example -/

def orbit1 : Finset (Fin 3) := {0, 1}
def orbit2 : Finset (Fin 3) := {2}

-- Both orbit joins are disjoint and partition the full set of atoms
#eval (orbit1 ∩ orbit2 == (∅ : Finset (Fin 3)))  -- true
#eval (orbit1 ∪ orbit2 == {0, 1, 2})             -- true

-- The 4 fixed points of the action in P({0,1,2})
def fixed_elements : List (Finset (Fin 3)) :=
  [∅, orbit1, orbit2, orbit1 ∪ orbit2]

#eval fixed_elements.length                      -- 4



end Course21373Numerical
