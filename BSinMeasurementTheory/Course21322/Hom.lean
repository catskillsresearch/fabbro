import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

open scoped BigOperators Classical

namespace Course21322

namespace FiniteStoneCollapse

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Predicate characterizing Boolean algebra homomorphisms from `Set α` to `Bool`. -/
class IsHom {α : Type*} [Fintype α] [DecidableEq α] (f : Set α → Bool) : Prop where
  map_univ : f Set.univ = true
  map_empty : f ∅ = false
  map_inter : ∀ x y, f (x ∩ y) = (f x && f y)
  map_union : ∀ x y, f (x ∪ y) = (f x || f y)
  map_compl : ∀ x, f (xᶜ) = (!f x)

/-- The Stone space $X = \mathrm{Stone}(\mathcal{P}(\alpha))$. -/
def StoneSpace (α : Type*) [Fintype α] [DecidableEq α] : Type _ :=
  { f : Set α → Bool // IsHom f }

/-- The principal evaluation homomorphism associated with an atom `a : α`. -/
noncomputable def principalHom (a : α) : Set α → Bool :=
  fun s => decide (a ∈ s)

/-- Verification that `principalHom a` is a genuine Boolean homomorphism. -/
theorem principalHom_isHom (a : α) : IsHom (principalHom a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [principalHom]; simp
  · dsimp [principalHom]; simp
  · intro x y; dsimp [principalHom]
    by_cases hx : a ∈ x <;> by_cases hy : a ∈ y <;> simp [hx, hy]
  · intro x y; dsimp [principalHom]
    by_cases hx : a ∈ x <;> by_cases hy : a ∈ y <;> simp [hx, hy]
  · intro x; dsimp [principalHom]
    by_cases hx : a ∈ x <;> simp [hx]

/-- Embedding of atoms into the Stone space. -/
noncomputable def atomToStone (a : α) : StoneSpace α :=
  ⟨principalHom a, principalHom_isHom a⟩

end FiniteStoneCollapse

end Course21322
