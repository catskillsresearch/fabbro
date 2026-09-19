import Mathlib
import BSinMeasurementTheory.Course21127.NonzeroDenomInt

namespace Course21127

lemma rat_div_eq_of_mul_eq {a b c d : ℚ} (hb : b ≠ 0) (hd : d ≠ 0) (h : a * d = b * c) :
    a / b = c / d := by
  rw [div_eq_div_iff hb hd]
  linarith

lemma rat_mul_eq_of_div_eq {a b c d : ℚ} (hb : b ≠ 0) (hd : d ≠ 0) (h : a / b = c / d) :
    a * d = b * c := by
  have := (div_eq_div_iff hb hd).mp h
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

/-- (b) Part 1: Injectivity -/
theorem toRatQuot_injective : Function.Injective toRatQuot := by
  intro q1 q2
  refine Quotient.inductionOn₂ q1 q2 ?_
  intro x y h
  dsimp [toRatQuot, toRat] at h
  have hx : ((x.den : ℚ) ≠ 0) := by
    intro hz
    exact x.den_ne_zero (by exact_mod_cast hz)
  have hy : ((y.den : ℚ) ≠ 0) := by
    intro hz
    exact y.den_ne_zero (by exact_mod_cast hz)
  have h_mul := rat_mul_eq_of_div_eq hx hy h
  have h_int : x.num * y.den = x.den * y.num := by
    exact_mod_cast h_mul
  apply Quotient.sound
  exact h_int

/-- (b) Part 2: Surjectivity -/
theorem toRatQuot_surjective : Function.Surjective toRatQuot := by
  intro q
  have hden : (q.den : ℤ) ≠ 0 := by
    intro hz
    have : q.den = 0 := by exact_mod_cast hz
    exact q.den_nz this
  use Quotient.mk nonzeroDenomIntSetoid ⟨q.num, (q.den : ℤ), hden⟩
  change toRat ⟨q.num, (q.den : ℤ), hden⟩ = q
  dsimp [toRat]
  have : ((q.den : ℤ) : ℚ) = (q.den : ℚ) := by push_cast; rfl
  rw [this]
  exact Rat.num_div_den q

/-- (b) Part 3: Bijectivity -/
theorem toRatQuot_bijective : Function.Bijective toRatQuot :=
  ⟨toRatQuot_injective, toRatQuot_surjective⟩

/-- The induced quotient set is in bijection with Q. -/
noncomputable def quotientEquivRat : Quotient nonzeroDenomIntSetoid ≃ ℚ :=
  Equiv.ofBijective toRatQuot toRatQuot_bijective

end Course21127
