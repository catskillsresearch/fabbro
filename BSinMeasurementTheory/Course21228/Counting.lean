import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Equiv

namespace Course21228

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

end Course21228
