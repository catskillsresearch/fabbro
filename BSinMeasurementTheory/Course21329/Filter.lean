import Mathlib

universe u

namespace Course21329

variable {B : Type u} [Lattice B] [BoundedOrder B]

/-- A filter on a bounded lattice `B` is a non-empty, upward-closed set closed under meets. -/
class IsFilter (F : Set B) : Prop where
  mem_top : ⊤ ∈ F
  upward : ∀ ⦃x y : B⦄, x ∈ F → x ≤ y → y ∈ F
  inf_closed : ∀ ⦃x y : B⦄, x ∈ F → y ∈ F → x ⊓ y ∈ F

/-- A filter is proper if it does not contain the bottom element `⊥`. -/
class IsProperFilter (F : Set B) : Prop extends IsFilter F where
  not_bot : ⊥ ∉ F

/-- An ultrafilter is a maximal proper filter under subset inclusion. -/
class IsUltrafilter (U : Set B) : Prop extends IsProperFilter U where
  maximal : ∀ ⦃F : Set B⦄, IsProperFilter F → U ⊆ F → U = F

end Course21329
