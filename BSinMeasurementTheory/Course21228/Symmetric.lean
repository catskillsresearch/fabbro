import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Equiv

namespace Course21228

variable {n : ℕ} {α : Type*}

/-- A condition `L` on length-`n` sequences is symmetric if it is invariant
    under any permutation of the sequence. -/
class IsSymmetric (L : (Fin n → α) → Prop) : Prop where
  perm_iff : ∀ (x : Fin n → α) (π : Perm (Fin n)), L (x ∘ π) ↔ L x

/-- If two sequences represent the same multiset (i.e. one is a permutation of the other),
    any symmetric condition `L` yields the same truth value on both. -/
theorem symmetric_depends_only_on_multiset
    (L : (Fin n → α) → Prop) [hL : IsSymmetric L]
    (x y : Fin n → α) (π : Perm (Fin n)) (h : y = x ∘ π) :
    L y ↔ L x := by
  rw [h]
  exact hL.perm_iff x π

/-- For any additive commutative monoid, the total sum is invariant under permutations. -/
theorem sum_perm_invariant {M : Type*} [AddCommMonoid M]
    (x : Fin n → M) (π : Perm (Fin n)) :
    ∑ i : Fin n, (x ∘ π) i = ∑ i : Fin n, x i := by
  exact Equiv.sum_comp π x

end Course21228
