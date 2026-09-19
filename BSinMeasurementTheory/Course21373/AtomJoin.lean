import Mathlib
import BSinMeasurementTheory.Course21373.IsBooleanAtom

open Finset
open Classical

namespace Course21373

variable {B : Type*} [BooleanAlgebra B]

/-- Distinct atoms are disjoint. -/
theorem isAtom_inf_eq_bot {a b : B} (ha : IsBooleanAtom a) (hb : IsBooleanAtom b) (hne : a ≠ b) :
    a ⊓ b = ⊥ := by
  have hle : a ⊓ b ≤ a := inf_le_left
  cases ha.le_bot_or_self (a ⊓ b) hle with
  | inl h => exact h
  | inr h =>
    have hle2 : a ≤ b := by
      calc a = a ⊓ b := h.symm
      _ ≤ b := inf_le_right
    cases hb.le_bot_or_self a hle2 with
    | inl hbot => exact (ha.ne_bot hbot).elim
    | inr heq => exact (hne heq).elim

/-- An atom is below a join of two elements iff it is below at least one. -/
theorem isAtom_le_sup_iff {a b c : B} (ha : IsBooleanAtom a) :
    a ≤ b ⊔ c ↔ a ≤ b ∨ a ≤ c := by
  constructor
  · intro h
    have hdist : a = (a ⊓ b) ⊔ (a ⊓ c) := by
      calc a = a ⊓ (b ⊔ c) := (inf_eq_left.mpr h).symm
      _ = (a ⊓ b) ⊔ (a ⊓ c) := inf_sup_left a b c
    cases ha.le_bot_or_self (a ⊓ b) inf_le_left with
    | inr hab =>
      left
      calc a = a ⊓ b := hab.symm
      _ ≤ b := inf_le_right
    | inl hab =>
      right
      have hac : a = a ⊓ c := by
        calc a = (a ⊓ b) ⊔ (a ⊓ c) := hdist
        _ = ⊥ ⊔ (a ⊓ c) := congr_arg (· ⊔ (a ⊓ c)) hab
        _ = a ⊓ c := bot_sup_eq (a ⊓ c)
      calc a = a ⊓ c := hac
      _ ≤ c := inf_le_right
  · rintro (h | h)
    · exact le_trans h le_sup_left
    · exact le_trans h le_sup_right

/-- An atom is below a finite join iff it is below some member. -/
theorem isAtom_le_finset_sup {a : B} (ha : IsBooleanAtom a) (s : Finset B) :
    a ≤ s.sup id ↔ ∃ b ∈ s, a ≤ b := by
  induction s using Finset.induction_on with
  | empty =>
    constructor
    · intro h
      rw [Finset.sup_empty] at h
      exact (ha.ne_bot (le_bot_iff.mp h)).elim
    · rintro ⟨b, hb, _⟩
      cases hb
  | @insert b s _ ih =>
    rw [Finset.sup_insert]
    dsimp only [id]
    rw [isAtom_le_sup_iff ha, ih]
    simp only [Finset.mem_insert]
    constructor
    · rintro (h | ⟨c, hc, hac⟩)
      · exact ⟨b, Or.inl rfl, h⟩
      · exact ⟨c, Or.inr hc, hac⟩
    · rintro ⟨c, rfl | hc, hac⟩
      · exact Or.inl hac
      · exact Or.inr ⟨c, hc, hac⟩

/-- If `s` consists of atoms, an atom `a ≤ s.sup id` iff `a ∈ s`. -/
theorem isAtom_le_finset_sup_of_atoms {a : B} (ha : IsBooleanAtom a) {s : Finset B}
    (hs : ∀ b ∈ s, IsBooleanAtom b) :
    a ≤ s.sup id ↔ a ∈ s := by
  rw [isAtom_le_finset_sup ha]
  constructor
  · rintro ⟨b, hb, hab⟩
    have hb_atom := hs b hb
    cases hb_atom.le_bot_or_self a hab with
    | inl hbot => exact (ha.ne_bot hbot).elim
    | inr heq =>
      rw [heq]
      exact hb
  · intro ha_mem
    exact ⟨a, ha_mem, le_rfl⟩

/-- Uniqueness of representation: two subsets of atoms with equal join must be equal. -/
theorem finset_sup_inj_of_atoms {s t : Finset B}
    (hs : ∀ b ∈ s, IsBooleanAtom b) (ht : ∀ b ∈ t, IsBooleanAtom b)
    (h_eq : s.sup id = t.sup id) : s = t := by
  ext a
  constructor
  · intro ha
    have ha_atom := hs a ha
    have hle : a ≤ s.sup id := (isAtom_le_finset_sup_of_atoms ha_atom hs).mpr ha
    rw [h_eq] at hle
    exact (isAtom_le_finset_sup_of_atoms ha_atom ht).mp hle
  · intro ha
    have ha_atom := ht a ha
    have hle : a ≤ t.sup id := (isAtom_le_finset_sup_of_atoms ha_atom ht).mpr ha
    rw [← h_eq] at hle
    exact (isAtom_le_finset_sup_of_atoms ha_atom hs).mp hle

end Course21373
