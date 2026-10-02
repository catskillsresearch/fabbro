/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.WellFounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Challenge — Course 21-127

Mathlib-only restatement of the Concepts of Mathematics capstone.
-/

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

lemma rat_div_eq_of_mul_eq {a b c d : ℚ} (hb : b ≠ 0) (hd : d ≠ 0) (h : a * d = b * c) :
    a / b = c / d := by
  rw [div_eq_div_iff hb hd]
  linarith

/-- The explicit map from a pair (a, b) to Q. -/
def toRat (p : NonzeroDenomInt) : ℚ := (p.num : ℚ) / (p.den : ℚ)

/-- The map respects the equivalence relation (well-defined). -/
lemma toRat_wellDefined (x y : NonzeroDenomInt) (h : Rel x y) : toRat x = toRat y := by
  dsimp [toRat]
  have hx : ((x.den : ℚ) ≠ 0) := by
    intro hz
    exact x.den_ne_zero (by exact_mod_cast hz)
  have hy : ((y.den : ℚ) ≠ 0) := by
    intro hz
    exact y.den_ne_zero (by exact_mod_cast hz)
  have h_int : x.num * y.den = x.den * y.num := h
  have h_cast : (x.num : ℚ) * (y.den : ℚ) = (x.den : ℚ) * (y.num : ℚ) := by
    exact_mod_cast h_int
  exact rat_div_eq_of_mul_eq hx hy h_cast

/-- The induced map on the quotient set. -/
def toRatQuot : Quotient nonzeroDenomIntSetoid → ℚ :=
  Quotient.lift toRat toRat_wellDefined

/-- (b) Part 3: Bijectivity -/
theorem toRatQuot_bijective : Function.Bijective toRatQuot := by
  sorry

/-- A subset of Q is well-ordered under the usual order if every nonempty
    subset has a least element in the set. -/
class IsWellOrderedSet (S : Set ℚ) : Prop where
  least : ∀ T : Set ℚ, T ⊆ S → T.Nonempty → ∃ m ∈ T, ∀ x ∈ T, m ≤ x

/-- The false claim stated in the prompt using Set.Ici to avoid untyped binder problems. -/
def FalseClaim : Prop :=
  ∀ S : Set ℚ, S ⊆ Set.Ici (0 : ℚ) → S.Nonempty → IsWellOrderedSet S →
    (S = ∅ ∨ Set.Infinite S)

/-- (c) Refutation by contradiction. -/
theorem false_claim_is_false : ¬ FalseClaim := by
  sorry

end Course21127
