import Mathlib

open scoped BigOperators Classical

namespace Course21322

namespace FiniteStoneCollapse

set_option linter.unusedSectionVars false

/-!
### 1. Stone Homomorphisms on a Finite Power Set Algebra
-/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Predicate characterizing Boolean algebra homomorphisms from `Set α` to `Bool`. -/
def isHom (f : Set α → Bool) : Prop :=
  f Set.univ = true ∧
  f ∅ = false ∧
  (∀ x y, f (x ∩ y) = (f x && f y)) ∧
  (∀ x y, f (x ∪ y) = (f x || f y)) ∧
  (∀ x, f (xᶜ) = (!f x))

/-- The Stone space $X = \mathrm{Stone}(\mathcal{P}(\alpha))$. -/
def StoneSpace (α : Type*) [Fintype α] [DecidableEq α] : Type _ :=
  { f : Set α → Bool // isHom f }

/-- The principal evaluation homomorphism associated with an atom `a : α`. -/
noncomputable def principalHom (a : α) : Set α → Bool :=
  fun s => decide (a ∈ s)

/-- Verification that `principalHom a` is a genuine Boolean homomorphism. -/
theorem principalHom_isHom (a : α) : isHom (principalHom a) := by
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

/-!
### 2. Isomorphism: Atoms ≃ Stone Ultrafilters
-/

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
  have h_univ : f Set.univ = true := hf.1
  have h_sum : ∃ a : α, f {a} = true := by
    by_contra! hall
    have h_zero : ∀ s : Finset α, f (⋃ a ∈ s, ({a} : Set α)) = false := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        have : (⋃ a ∈ (∅ : Finset α), ({a} : Set α)) = ∅ := by ext; simp
        rw [this, hf.2.1]
      | @insert x s _ ih =>
        have h_union : (⋃ a ∈ insert x s, ({a} : Set α)) = {x} ∪ (⋃ a ∈ s, ({a} : Set α)) := by
          ext t; simp
        rw [h_union, hf.2.2.2.1 {x} (⋃ a ∈ s, ({a} : Set α))]
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
    have h_f_inter := hf.2.2.1 {a} s
    rw [h_inter, ha] at h_f_inter
    have : f s = true := by
      cases hfs : f s
      · rw [hfs, Bool.and_false] at h_f_inter; contradiction
      · rfl
    simp [has, this]
  · have h_le : {a} ⊆ sᶜ := Set.singleton_subset_iff.mpr has
    have h_inter : {a} ∩ sᶜ = {a} := Set.inter_eq_self_of_subset_left h_le
    have h_f_inter := hf.2.2.1 {a} (sᶜ)
    rw [h_inter, ha] at h_f_inter
    have h_compl := hf.2.2.2.2 s
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

/-!
### 3. Identification of Stone Clopens and Atomic Characteristic Sets
-/

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

/-!
### 4. Measure Reduction: Stone Integration to Discrete Weight Sum
-/

/-- Linear evaluation on step functions over the Stone space with weights `w`. -/
noncomputable def stoneMeasure (w : α → ℝ) (s : Set α) : ℝ :=
  ∑ a : α, if atomToStone a ∈ stoneMap s then w a else 0

/-- Discrete atomic measure sum from Phase 2 / Phase 3. -/
noncomputable def atomicMeasure (w : α → ℝ) (s : Set α) : ℝ :=
  ∑ a : α, if a ∈ s then w a else 0

/-- THE COLLAPSE THEOREM: The Stone space measure evaluation reduces identically
    to the finite atomic characteristic sum with ZERO discrepancy. -/
theorem stone_measure_eq_atomic_measure (w : α → ℝ) (s : Set α) :
    stoneMeasure w s = atomicMeasure w s := by
  dsimp [stoneMeasure, atomicMeasure]
  apply Finset.sum_congr rfl
  intro a _
  rw [← atom_mem_iff_stone_mem]

/-!
### 5. Concrete Numerical Example: 3-Atom Boolean Algebra
-/

def w3 : Fin 3 → ℝ
  | 0 => 0.2
  | 1 => 0.5
  | 2 => 0.3

lemma w3_sum : ∑ x : Fin 3, w3 x = 1 := by
  rw [Fin.sum_univ_three]
  norm_num [w3]

def testSet : Set (Fin 3) := {0, 2}

/-- Direct calculation of the atomic measure on {0, 2}: 0.2 + 0.3 = 0.5 -/
theorem atomic_test_eval : atomicMeasure w3 testSet = 0.5 := by
  dsimp [atomicMeasure, testSet]
  rw [Fin.sum_univ_three]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff]
  norm_num [w3]

/-- Calculation via the Stone representation map on {0, 2}: 0.2 + 0.3 = 0.5 -/
theorem stone_test_eval : stoneMeasure w3 testSet = 0.5 := by
  rw [stone_measure_eq_atomic_measure]
  exact atomic_test_eval

end FiniteStoneCollapse

end Course21322
