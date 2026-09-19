import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import BSinMeasurementTheory.Course21228.Counting

open Equiv

namespace Course21228

variable {α : Type*}

/-- Exact reduction to $n = 2$: $2! = 2$ pairs. -/
theorem validPairs_card_two [DecidableEq α] (x y : Fin 2 → α)
    (hinj : Function.Injective x) (τ : Perm (Fin 2)) (hy : y = x ∘ τ) :
    Fintype.card { p : Perm (Fin 2) × Perm (Fin 2) // ValidPair x y p } = 2 := by
  rw [validPairs_card x y hinj τ hy]
  rfl

theorem perm_fin_two_card : Fintype.card (Perm (Fin 2)) = 2 := by decide

end Course21228
