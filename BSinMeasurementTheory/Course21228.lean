import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Equiv

namespace Course21228

/-!
### Part (a): Symmetric Conditions and Multiset Invariance
-/

section PartA

variable {n : ℕ} {α : Type*}

/-- A condition `L` on length-`n` sequences is symmetric if it is invariant
    under any permutation of the sequence. -/
def IsSymmetric (L : (Fin n → α) → Prop) : Prop :=
  ∀ (x : Fin n → α) (π : Perm (Fin n)), L (x ∘ π) ↔ L x

/-- If two sequences represent the same multiset (i.e. one is a permutation of the other),
    any symmetric condition `L` yields the same truth value on both. -/
theorem symmetric_depends_only_on_multiset
    (L : (Fin n → α) → Prop) (hL : IsSymmetric L)
    (x y : Fin n → α) (π : Perm (Fin n)) (h : y = x ∘ π) :
    L y ↔ L x := by
  rw [h]
  exact hL x π

/-- For any additive commutative monoid, the total sum is invariant under permutations. -/
theorem sum_perm_invariant {M : Type*} [AddCommMonoid M]
    (x : Fin n → M) (π : Perm (Fin n)) :
    ∑ i : Fin n, (x ∘ π) i = ∑ i : Fin n, x i := by
  exact Equiv.sum_comp π x

end PartA

/-!
### Part (b): Counting Pairs of Permutations Under Genericity
-/

section PartB

variable {n : ℕ} {α : Type*}

/-- Two sequences `x` and `y` are equal termwise after permuting by `p.1` and `p.2`. -/
def ValidPair (x y : Fin n → α) (p : Perm (Fin n) × Perm (Fin n)) : Prop :=
  ∀ i : Fin n, x (p.1 i) = y (p.2 i)

/-- Synthesis of decidability for `ValidPair` when equality on `α` is decidable.
    This enables typeclass resolution for `Fintype { p // ValidPair x y p }`. -/
instance [DecidableEq α] (x y : Fin n → α) : DecidablePred (ValidPair x y) := by
  intro p
  unfold ValidPair
  infer_instance

/-- Bijection between `Perm (Fin n)` and the valid pairs `(π, σ)`.
    Genericity assumptions:
    1. `hinj`: vectors in `x` are pairwise distinct (`Function.Injective x`).
    2. `hy`: `y` is a permutation of `x` via `τ : Perm (Fin n)`. -/
def validPairsEquiv (x y : Fin n → α) (hinj : Function.Injective x)
    (τ : Perm (Fin n)) (hy : y = x ∘ τ) :
    Perm (Fin n) ≃ { p : Perm (Fin n) × Perm (Fin n) // ValidPair x y p } where
  toFun π := ⟨(π, π.trans τ.symm), by
    intro i
    dsimp [ValidPair]
    rw [hy]
    change x (π i) = x (τ (τ.symm (π i)))
    rw [apply_symm_apply]⟩
  invFun p := p.1.1
  left_inv π := rfl
  right_inv := by
    rintro ⟨⟨π, σ⟩, h_valid⟩
    apply Subtype.ext
    dsimp only
    refine Prod.ext rfl ?_
    apply Equiv.ext
    intro i
    have h : x (π i) = y (σ i) := h_valid i
    rw [hy] at h
    have h_eq : π i = τ (σ i) := hinj h
    exact (symm_apply_eq τ).mpr h_eq

/-- The exact number of valid pairs is `n!`. -/
theorem validPairs_card [DecidableEq α] (x y : Fin n → α)
    (hinj : Function.Injective x) (τ : Perm (Fin n)) (hy : y = x ∘ τ) :
    Fintype.card { p : Perm (Fin n) × Perm (Fin n) // ValidPair x y p } = Nat.factorial n := by
  rw [← Fintype.card_congr (validPairsEquiv x y hinj τ hy)]
  rw [Fintype.card_perm]
  rw [Fintype.card_fin]

end PartB

/-!
### Part (c): Reduction to n = 2 and n = 3
-/

section PartC

variable {α : Type*}

/-- Exact reduction to n = 2: 2! = 2 pairs. -/
theorem validPairs_card_two [DecidableEq α] (x y : Fin 2 → α)
    (hinj : Function.Injective x) (τ : Perm (Fin 2)) (hy : y = x ∘ τ) :
    Fintype.card { p : Perm (Fin 2) × Perm (Fin 2) // ValidPair x y p } = 2 := by
  rw [validPairs_card x y hinj τ hy]
  rfl

/-- Exact reduction to n = 3: 3! = 6 pairs. -/
theorem validPairs_card_three [DecidableEq α] (x y : Fin 3 → α)
    (hinj : Function.Injective x) (τ : Perm (Fin 3)) (hy : y = x ∘ τ) :
    Fintype.card { p : Perm (Fin 3) × Perm (Fin 3) // ValidPair x y p } = 6 := by
  rw [validPairs_card x y hinj τ hy]
  rfl

/-- Direct verification of the underlying symmetric group cardinalities. -/
theorem perm_fin_two_card : Fintype.card (Perm (Fin 2)) = 2 := by decide
theorem perm_fin_three_card : Fintype.card (Perm (Fin 3)) = 6 := by decide

end PartC

/-!
### Numerical Evaluation
-/

#eval Nat.factorial 2   -- 2
#eval Nat.factorial 3   -- 6


end Course21228
