import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import BSinMeasurementTheory.Course21322.Hom

open scoped BigOperators Classical

namespace Course21322

namespace FiniteStoneCollapse

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The Stone mapping $\widehat{s} = \{u \in X \mid u(s) = \mathrm{true}\}$. -/
def stoneMap (s : Set α) : Set (StoneSpace α) :=
  { u | u.1 s = true }

/-- Preservation of representation: an atom `a` belongs to `s` iff its ultrafilter
    `atomToStone a` belongs to the Stone clopen `stoneMap s`. -/
theorem atom_mem_iff_stone_mem (s : Set α) (a : α) :
    a ∈ s ↔ atomToStone a ∈ stoneMap s := by
  dsimp [atomToStone, principalHom, stoneMap]
  exact decide_eq_true_iff.symm

/-- The preimage of the Stone clopen `stoneMap s` under the atomic isomorphism
    is exactly the original subset `s`. -/
theorem stoneMap_preimage_eq (s : Set α) :
    atomToStone ⁻¹' (stoneMap s) = s := by
  ext a
  rw [Set.mem_preimage]
  exact (atom_mem_iff_stone_mem s a).symm

end FiniteStoneCollapse

end Course21322
