/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod

open Equiv

/-!
# Challenge — Course 21-228
-/

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
  sorry

/-- Two sequences \(x\) and \(y\) agree termwise after permuting by \(p.1\) and \(p.2\). -/
def ValidPair (x y : Fin n → α) (p : Perm (Fin n) × Perm (Fin n)) : Prop :=
  ∀ i : Fin n, x (p.1 i) = y (p.2 i)

instance [DecidableEq α] (x y : Fin n → α) : DecidablePred (ValidPair x y) := by
  intro p
  unfold ValidPair
  infer_instance

/-- Assumption 1: the vectors in \(x\) are pairwise distinct. -/
def PairwiseDistinct (x : Fin n → α) : Prop :=
  Function.Injective x

/-- Assumption 2: \(y\) is a permutation of \(x\), so the multisets agree. -/
def MultisetCompatible (x y : Fin n → α) : Prop :=
  ∃ τ : Perm (Fin n), y = x ∘ τ

/-- The exact number of valid pairs is \(n!\). -/
theorem validPairs_card [DecidableEq α] (x y : Fin n → α)
    (hinj : PairwiseDistinct x) (τ : Perm (Fin n)) (hy : y = x ∘ τ) :
    Fintype.card { p : Perm (Fin n) × Perm (Fin n) // ValidPair x y p } = Nat.factorial n := by
  sorry

end Course21228
