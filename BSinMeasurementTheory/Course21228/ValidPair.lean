import Mathlib.Data.Fintype.Perm

open Equiv

namespace Course21228

variable {n : ℕ} {α : Type*}

/-- Two sequences \(x\) and \(y\) agree termwise after permuting by \(p.1\) and \(p.2\). -/
def ValidPair (x y : Fin n → α) (p : Perm (Fin n) × Perm (Fin n)) : Prop :=
  ∀ i : Fin n, x (p.1 i) = y (p.2 i)

instance [DecidableEq α] (x y : Fin n → α) : DecidablePred (ValidPair x y) := by
  intro p
  unfold ValidPair
  infer_instance

end Course21228
