import Mathlib.Data.Int.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic.Ring

namespace Course21127

/-- Integers with a nonzero denominator: the domain of the fraction relation. -/
structure NonzeroDenomInt where
  num : ℤ
  den : ℤ
  den_ne_zero : den ≠ 0

/-- The relation (a, b) ~ (c, d) ↔ a * d = b * c -/
def Rel (x y : NonzeroDenomInt) : Prop :=
  x.num * y.den = x.den * y.num

lemma rel_refl (x : NonzeroDenomInt) : Rel x x := by
  dsimp [Rel]
  ring

lemma rel_symm {x y : NonzeroDenomInt} (h : Rel x y) : Rel y x := by
  dsimp [Rel] at *
  calc
    y.num * x.den = x.den * y.num := by ring
    _ = x.num * y.den := h.symm
    _ = y.den * x.num := by ring

lemma rel_trans {x y z : NonzeroDenomInt} (h1 : Rel x y) (h2 : Rel y z) : Rel x z := by
  dsimp [Rel] at *
  have hd : y.den ≠ 0 := y.den_ne_zero
  have H : (x.num * z.den) * y.den = (x.den * z.num) * y.den := by
    calc
      (x.num * z.den) * y.den = (x.num * y.den) * z.den := by ring
      _ = (x.den * y.num) * z.den := by rw [h1]
      _ = x.den * (y.num * z.den) := by ring
      _ = x.den * (y.den * z.num) := by rw [h2]
      _ = (x.den * z.num) * y.den := by ring
  have H2 : (x.num * z.den - x.den * z.num) * y.den = 0 := by
    calc (x.num * z.den - x.den * z.num) * y.den
      _ = (x.num * z.den) * y.den - (x.den * z.num) * y.den := by ring
      _ = (x.den * z.num) * y.den - (x.den * z.num) * y.den := by rw [H]
      _ = 0 := by ring
  cases mul_eq_zero.mp H2 with
  | inl h => exact sub_eq_zero.mp h
  | inr h => exact False.elim (hd h)

instance nonzeroDenomIntSetoid : Setoid NonzeroDenomInt where
  r := Rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

end Course21127
