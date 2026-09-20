import Mathlib.Order.Atoms
import Mathlib.Order.BooleanAlgebra.Basic

namespace Course21373

/-- An atom in a Boolean algebra is a non-bottom element whose only sub-elements are ⊥ and itself.
    Named `IsBooleanAtom` to avoid collision with Mathlib's order-theoretic `IsAtom`. -/
class IsBooleanAtom {B : Type*} [BooleanAlgebra B] (a : B) : Prop where
  ne_bot : a ≠ ⊥
  le_bot_or_self : ∀ x, x ≤ a → x = ⊥ ∨ x = a

end Course21373
