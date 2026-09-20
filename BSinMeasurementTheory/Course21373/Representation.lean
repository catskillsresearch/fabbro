import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.BooleanAlgebra.Basic
import BSinMeasurementTheory.Course21373.AtomJoin

open Finset
open Classical

namespace Course21373

variable {B : Type*} [BooleanAlgebra B]

/-- The canonical map sending an element to the atoms below it. -/
noncomputable def repMap (A : Finset B) (x : B) : Finset B :=
  A.filter (fun a => a ≤ x)

theorem repMap_inf (A : Finset B) (x y : B) :
    repMap A (x ⊓ y) = repMap A x ∩ repMap A y := by
  ext a
  simp only [repMap, Finset.mem_filter, Finset.mem_inter, le_inf_iff]
  tauto

theorem repMap_sup {A : Finset B} (hA : ∀ a ∈ A, IsBooleanAtom a) (x y : B) :
    repMap A (x ⊔ y) = repMap A x ∪ repMap A y := by
  ext a
  simp only [repMap, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨haA, hle⟩
    have ha_atom := hA a haA
    rw [isAtom_le_sup_iff ha_atom] at hle
    cases hle with
    | inl h => exact Or.inl ⟨haA, h⟩
    | inr h => exact Or.inr ⟨haA, h⟩
  · rintro (⟨haA, h⟩ | ⟨haA, h⟩)
    · exact ⟨haA, le_trans h le_sup_left⟩
    · exact ⟨haA, le_trans h le_sup_right⟩

theorem repMap_bot {A : Finset B} (hA : ∀ a ∈ A, IsBooleanAtom a) :
    repMap A ⊥ = ∅ := by
  ext a
  simp only [repMap, Finset.mem_filter]
  constructor
  · rintro ⟨haA, hle⟩
    have ha_bot : a = ⊥ := le_bot_iff.mp hle
    exact ((hA a haA).ne_bot ha_bot).elim
  · intro h
    cases h

/-- `repMap` is the inverse of `Finset.sup id` on subsets of atoms. -/
theorem repMap_sup_id {A : Finset B} (hA : ∀ a ∈ A, IsBooleanAtom a) {s : Finset B} (hs : s ⊆ A) :
    repMap A (s.sup id) = s := by
  ext a
  simp only [repMap, Finset.mem_filter]
  constructor
  · rintro ⟨haA, hle⟩
    have ha_atom := hA a haA
    exact (isAtom_le_finset_sup_of_atoms ha_atom (fun b hb => hA b (hs hb))).mp hle
  · intro ha
    have haA := hs ha
    have ha_atom := hA a haA
    refine ⟨haA, ?_⟩
    exact (isAtom_le_finset_sup_of_atoms ha_atom (fun b hb => hA b (hs hb))).mpr ha

/-- Natural equivalence between subsets of `{0, ..., n-1}` and characteristic functions. -/
def finsetToCharFun (n : ℕ) : Finset (Fin n) ≃ (Fin n → Bool) where
  toFun s := fun i => decide (i ∈ s)
  invFun f := Finset.filter (fun i => f i = true) Finset.univ
  left_inv s := by
    ext i
    simp
  right_inv f := by
    ext i
    simp

end Course21373
