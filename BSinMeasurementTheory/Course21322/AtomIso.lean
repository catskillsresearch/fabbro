import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.ByContra
import BSinMeasurementTheory.Course21322.Hom

open scoped BigOperators Classical

namespace Course21322

namespace FiniteStoneCollapse

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Distinct atoms map to distinct Stone homomorphisms. -/
theorem atomToStone_injective : Function.Injective (atomToStone (α := α)) := by
  intro a b hab
  have hb : b ∈ ({a} : Set α) := by
    have : (atomToStone b).1 ({a} : Set α) = true := by
      rw [← hab]
      simp [atomToStone, principalHom]
    simpa [atomToStone, principalHom] using this
  exact (Set.mem_singleton_iff.mp hb).symm

/-- Every Stone homomorphism on `Set α` is the principal evaluation at some atom. -/
theorem stoneToAtom_surjective (u : StoneSpace α) :
    ∃ a : α, atomToStone a = u := by
  rcases u with ⟨f, hf⟩
  have h_univ : f Set.univ = true := hf.map_univ
  have h_sum : ∃ a : α, f {a} = true := by
    by_contra! hall
    have h_zero : ∀ s : Finset α, f (⋃ a ∈ s, ({a} : Set α)) = false := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        have : (⋃ a ∈ (∅ : Finset α), ({a} : Set α)) = ∅ := by ext; simp
        rw [this, hf.map_empty]
      | @insert x s _ ih =>
        have h_union : (⋃ a ∈ insert x s, ({a} : Set α)) = {x} ∪ (⋃ a ∈ s, ({a} : Set α)) := by
          ext t; simp
        rw [h_union, hf.map_union {x} (⋃ a ∈ s, ({a} : Set α))]
        have hx : f {x} = false := Bool.eq_false_iff.mpr (hall x)
        rw [hx, ih]
        rfl
    have h_all : (⋃ a ∈ (Finset.univ : Finset α), ({a} : Set α)) = Set.univ := by
      ext t; simp
    have h_false := h_zero Finset.univ
    rw [h_all] at h_false
    rw [h_false] at h_univ
    contradiction
  rcases h_sum with ⟨a, ha⟩
  use a
  apply Subtype.ext
  ext s
  dsimp [atomToStone, principalHom]
  by_cases has : a ∈ s
  · have h_le : {a} ⊆ s := Set.singleton_subset_iff.mpr has
    have h_inter : {a} ∩ s = {a} := Set.inter_eq_self_of_subset_left h_le
    have h_f_inter := hf.map_inter {a} s
    rw [h_inter, ha] at h_f_inter
    have : f s = true := by
      cases hfs : f s
      · rw [hfs, Bool.and_false] at h_f_inter; contradiction
      · rfl
    simp [has, this]
  · have h_le : {a} ⊆ sᶜ := Set.singleton_subset_iff.mpr has
    have h_inter : {a} ∩ sᶜ = {a} := Set.inter_eq_self_of_subset_left h_le
    have h_f_inter := hf.map_inter {a} (sᶜ)
    rw [h_inter, ha] at h_f_inter
    have h_compl := hf.map_compl s
    have h_fs_false : f s = false := by
      cases hfs : f s
      · rfl
      · rw [hfs, Bool.not_true] at h_compl
        rw [h_compl, Bool.and_false] at h_f_inter
        contradiction
    simp [has, h_fs_false]

/-- Canonical bijection between the atom set and the Stone space of a finite algebra. -/
noncomputable def atomEquivStone : α ≃ StoneSpace α :=
  Equiv.ofBijective atomToStone ⟨atomToStone_injective, stoneToAtom_surjective⟩

end FiniteStoneCollapse

end Course21322
