import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import BSinMeasurementTheory.Course21228.Counting

open Equiv

namespace Course21228

variable {α : Type*}

/-- Exact reduction to $n = 3$: $3! = 6$ pairs. -/
theorem validPairs_card_three [DecidableEq α] (x y : Fin 3 → α)
    (hinj : Function.Injective x) (τ : Perm (Fin 3)) (hy : y = x ∘ τ) :
    Fintype.card { p : Perm (Fin 3) × Perm (Fin 3) // ValidPair x y p } = 6 := by
  rw [validPairs_card_of_perm x y hinj τ hy]
  rfl

theorem perm_fin_three_card : Fintype.card (Perm (Fin 3)) = 6 := by decide

end Course21228
