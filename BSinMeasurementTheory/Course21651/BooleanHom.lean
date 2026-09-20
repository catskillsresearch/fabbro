import Mathlib.Data.Set.Basic
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Topology.Basic

set_option linter.unusedSectionVars false

open Topology Set

namespace Course21651

namespace StoneRepresentation

variable (B : Type*) [BooleanAlgebra B]

/-- Predicate characterizing Boolean algebra homomorphisms from `B` to `Bool`. -/
class IsBooleanHom {B : Type*} [BooleanAlgebra B] (f : B → Bool) : Prop where
  map_top : f ⊤ = true
  map_bot : f ⊥ = false
  map_inf : ∀ x y, f (x ⊓ y) = (f x && f y)
  map_sup : ∀ x y, f (x ⊔ y) = (f x || f y)
  map_compl : ∀ x, f (xᶜ) = (!f x)

/-- The Stone space $X = \mathrm{Stone}(B)$ realized as the subtype of homomorphisms in `B → Bool`. -/
@[reducible]
def StoneSpace : Type _ := { f : B → Bool // IsBooleanHom f }

end StoneRepresentation

end Course21651
