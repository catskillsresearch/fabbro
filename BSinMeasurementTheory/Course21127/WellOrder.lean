import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.WellFounded

namespace Course21127

/-- A subset of Q is well-ordered under the usual order if every nonempty
    subset has a least element in the set. -/
class IsWellOrderedSet (S : Set ℚ) : Prop where
  least : ∀ T : Set ℚ, T ⊆ S → T.Nonempty → ∃ m ∈ T, ∀ x ∈ T, m ≤ x

/-- The false claim stated in the prompt using Set.Ici to avoid untyped binder problems. -/
def FalseClaim : Prop :=
  ∀ S : Set ℚ, S ⊆ Set.Ici (0 : ℚ) → S.Nonempty → IsWellOrderedSet S →
    (S = ∅ ∨ Set.Infinite S)

lemma singleton_zero_well_ordered : IsWellOrderedSet {(0 : ℚ)} where
  least T hT hne := by
    rcases hne with ⟨t, ht⟩
    have ht0 : t = 0 := hT ht
    subst ht0
    refine ⟨0, ht, ?_⟩
    intro x hx
    have hx0 : x = 0 := hT hx
    subst hx0
    exact le_rfl

lemma singleton_zero_nonneg : ({(0 : ℚ)} : Set ℚ) ⊆ Set.Ici 0 :=
  Set.singleton_subset_iff.mpr (Set.mem_Ici.mpr le_rfl)

lemma singleton_zero_nonempty : ({(0 : ℚ)} : Set ℚ).Nonempty :=
  ⟨0, rfl⟩

/-- (c) Refutation by contradiction:
    The claim implies that {0} must be empty or infinite, both of which are false. -/
theorem false_claim_is_false : ¬ FalseClaim := by
  intro hclaim
  have h_cases := hclaim {0} singleton_zero_nonneg singleton_zero_nonempty
    singleton_zero_well_ordered
  cases h_cases with
  | inl h_empty =>
    have h0 : (0 : ℚ) ∈ ({(0 : ℚ)} : Set ℚ) := rfl
    rw [h_empty] at h0
    exact h0
  | inr h_inf =>
    exact h_inf (Set.finite_singleton 0)

/-- Correct positive statement proved by induction:
    Every nonempty finite list of rationals contains a least element. -/
lemma list_has_min : ∀ (a : ℚ) (l : List ℚ), ∃ m ∈ a :: l, ∀ x ∈ a :: l, m ≤ x
  | a, [] => by
    refine ⟨a, List.mem_cons.mpr (Or.inl rfl), ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with hxa | hx_nil
    · rw [hxa]
    · cases hx_nil
  | a, b :: l => by
    rcases list_has_min (min a b) l with ⟨m, hm, hle⟩
    have hm_orig : m ∈ a :: b :: l := by
      rcases List.mem_cons.mp hm with hm_eq | h_in
      · rw [hm_eq]
        cases le_total a b with
        | inl hab =>
          rw [min_eq_left hab]
          exact List.mem_cons.mpr (Or.inl rfl)
        | inr hba =>
          rw [min_eq_right hba]
          exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h_in)))
    refine ⟨m, hm_orig, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with hxa | hx1
    · rw [hxa]
      have h_min_in : min a b ∈ (min a b) :: l := List.mem_cons.mpr (Or.inl rfl)
      exact le_trans (hle (min a b) h_min_in) (min_le_left a b)
    · rcases List.mem_cons.mp hx1 with hxb | hx2
      · rw [hxb]
        have h_min_in : min a b ∈ (min a b) :: l := List.mem_cons.mpr (Or.inl rfl)
        exact le_trans (hle (min a b) h_min_in) (min_le_right a b)
      · have hx_in : x ∈ (min a b) :: l := List.mem_cons.mpr (Or.inr hx2)
        exact hle x hx_in

end Course21127
