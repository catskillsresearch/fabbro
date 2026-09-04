import Mathlib

namespace Course21127

/-!
# Part (a): Equivalence Relation on ℤ × (ℤ \ {0})
-/

/-- The domain S = ℤ × (ℤ \ {0}) -/
def S : Type := ℤ × { z : ℤ // z ≠ 0 }

/-- The relation (a, b) ~ (c, d) ↔ a * d = b * c -/
def rel (x y : S) : Prop :=
  x.1 * y.2.val = x.2.val * y.1

lemma rel_refl (x : S) : rel x x := by
  dsimp [rel]
  ring

lemma rel_symm {x y : S} (h : rel x y) : rel y x := by
  dsimp [rel] at *
  calc
    y.1 * x.2.val = x.2.val * y.1 := by ring
    _ = x.1 * y.2.val := h.symm
    _ = y.2.val * x.1 := by ring

lemma rel_trans {x y z : S} (h1 : rel x y) (h2 : rel y z) : rel x z := by
  dsimp [rel] at *
  have hd : y.2.val ≠ 0 := y.2.property
  have H : (x.1 * z.2.val) * y.2.val = (x.2.val * z.1) * y.2.val := by
    calc
      (x.1 * z.2.val) * y.2.val = (x.1 * y.2.val) * z.2.val := by ring
      _ = (x.2.val * y.1) * z.2.val := by rw [h1]
      _ = x.2.val * (y.1 * z.2.val) := by ring
      _ = x.2.val * (y.2.val * z.1) := by rw [h2]
      _ = (x.2.val * z.1) * y.2.val := by ring
  have H2 : (x.1 * z.2.val - x.2.val * z.1) * y.2.val = 0 := by
    calc (x.1 * z.2.val - x.2.val * z.1) * y.2.val
      _ = (x.1 * z.2.val) * y.2.val - (x.2.val * z.1) * y.2.val := by ring
      _ = (x.2.val * z.1) * y.2.val - (x.2.val * z.1) * y.2.val := by rw [H]
      _ = 0 := by ring
  cases mul_eq_zero.mp H2 with
  | inl h => exact sub_eq_zero.mp h
  | inr h => exact False.elim (hd h)

/-- (a) `rel` is an equivalence relation on S. -/
def setoid : Setoid S where
  r := rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

instance : Setoid S := setoid

/-!
# Part (b): Bijection between Quotient and ℚ
-/

lemma rat_div_eq_of_mul_eq {a b c d : ℚ} (hb : b ≠ 0) (hd : d ≠ 0) (h : a * d = b * c) :
    a / b = c / d := by
  rw [div_eq_div_iff hb hd]
  linarith

lemma rat_mul_eq_of_div_eq {a b c d : ℚ} (hb : b ≠ 0) (hd : d ≠ 0) (h : a / b = c / d) :
    a * d = b * c := by
  have := (div_eq_div_iff hb hd).mp h
  linarith

/-- The explicit map from a pair (a, b) to ℚ. -/
def toRat (p : S) : ℚ := (p.1 : ℚ) / (p.2.val : ℚ)

/-- The map respects the equivalence relation (well-defined). -/
lemma toRat_wellDefined (x y : S) (h : rel x y) : toRat x = toRat y := by
  dsimp [toRat]
  have hx : ((x.2.val : ℚ) ≠ 0) := by
    intro hz
    exact x.2.property (by exact_mod_cast hz)
  have hy : ((y.2.val : ℚ) ≠ 0) := by
    intro hz
    exact y.2.property (by exact_mod_cast hz)
  have h_int : x.1 * y.2.val = x.2.val * y.1 := h
  have h_cast : (x.1 : ℚ) * (y.2.val : ℚ) = (x.2.val : ℚ) * (y.1 : ℚ) := by
    exact_mod_cast h_int
  exact rat_div_eq_of_mul_eq hx hy h_cast

/-- The induced map on the quotient set. -/
def toRatQuot : Quotient setoid → ℚ :=
  Quotient.lift toRat toRat_wellDefined

/-- (b) Part 1: Injectivity -/
theorem toRatQuot_injective : Function.Injective toRatQuot := by
  intro q1 q2
  refine Quotient.inductionOn₂ q1 q2 ?_
  intro x y h
  dsimp [toRatQuot, toRat] at h
  have hx : ((x.2.val : ℚ) ≠ 0) := by
    intro hz
    exact x.2.property (by exact_mod_cast hz)
  have hy : ((y.2.val : ℚ) ≠ 0) := by
    intro hz
    exact y.2.property (by exact_mod_cast hz)
  have h_mul := rat_mul_eq_of_div_eq hx hy h
  have h_int : x.1 * y.2.val = x.2.val * y.1 := by
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
  use ⟦(q.num, ⟨(q.den : ℤ), hden⟩)⟧
  change toRat (q.num, ⟨(q.den : ℤ), hden⟩) = q
  dsimp [toRat]
  have : ((q.den : ℤ) : ℚ) = (q.den : ℚ) := by push_cast; rfl
  rw [this]
  exact Rat.num_div_den q

/-- (b) Part 3: Bijectivity -/
theorem toRatQuot_bijective : Function.Bijective toRatQuot :=
  ⟨toRatQuot_injective, toRatQuot_surjective⟩

/-- The induced quotient set is in bijection with ℚ. -/
noncomputable def quotientEquivRat : Quotient setoid ≃ ℚ :=
  Equiv.ofBijective toRatQuot toRatQuot_bijective

/-!
# Part (c): Refutation of the False Claim and the Correct Theorem
-/

/-- A subset S ⊆ ℚ is well-ordered under the usual order if every nonempty
    subset has a least element in the set. -/
def IsWellOrderedSet (S : Set ℚ) : Prop :=
  ∀ T : Set ℚ, T ⊆ S → T.Nonempty → ∃ m ∈ T, ∀ x ∈ T, m ≤ x

/-- The false claim stated in the prompt using Set.Ici to avoid untyped binder problems. -/
def FalseClaim : Prop :=
  ∀ S : Set ℚ, S ⊆ Set.Ici (0 : ℚ) → S.Nonempty → IsWellOrderedSet S →
    (S = ∅ ∨ Set.Infinite S)

lemma singleton_zero_well_ordered : IsWellOrderedSet { (0 : ℚ) } := by
  intro T hT ⟨t, ht⟩
  have ht0 : t = 0 := hT ht
  subst ht0
  refine ⟨0, ht, ?_⟩
  intro x hx
  have hx0 : x = 0 := hT hx
  subst hx0
  exact le_rfl

lemma singleton_zero_nonneg : ({ (0 : ℚ) } : Set ℚ) ⊆ Set.Ici 0 :=
  Set.singleton_subset_iff.mpr (Set.mem_Ici.mpr le_rfl)

lemma singleton_zero_nonempty : ({ (0 : ℚ) } : Set ℚ).Nonempty :=
  ⟨0, rfl⟩

/-- (c) Refutation by contradiction:
    The claim implies that {0} must be empty or infinite, both of which are false. -/
theorem false_claim_is_false : ¬ FalseClaim := by
  intro hclaim
  have h_cases := hclaim {0} singleton_zero_nonneg singleton_zero_nonempty singleton_zero_well_ordered
  cases h_cases with
  | inl h_empty =>
    have h0 : (0 : ℚ) ∈ ({ (0 : ℚ) } : Set ℚ) := rfl
    rw [h_empty] at h0
    exact h0
  | inr h_inf =>
    exact h_inf (Set.finite_singleton 0)

/-- Correct positive statement proved by induction:
    Every nonempty finite list of rationals contains a least element. -/
lemma list_has_min : ∀ (a : ℚ) (l : List ℚ), ∃ m ∈ a :: l, ∀ x ∈ a :: l, m ≤ x
  | a, [] => by
    refine ⟨a, List.mem_cons.mpr (Or.inl rfl), ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with hxa | hx_nil
    · rw [hxa]
    · cases hx_nil
  | a, b :: l => by
    rcases list_has_min (min a b) l with ⟨m, hm, hle⟩
    have hm_orig : m ∈ a :: b :: l := by
      rcases List.mem_cons.mp hm with hm_eq | h_in
      · rw [hm_eq]
        cases le_total a b with
        | inl hab =>
          rw [min_eq_left hab]
          exact List.mem_cons.mpr (Or.inl rfl)
        | inr hba =>
          rw [min_eq_right hba]
          exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h_in)))
    refine ⟨m, hm_orig, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with hxa | hx1
    · rw [hxa]
      have h_min_in : min a b ∈ (min a b) :: l := List.mem_cons.mpr (Or.inl rfl)
      exact le_trans (hle (min a b) h_min_in) (min_le_left a b)
    · rcases List.mem_cons.mp hx1 with hxb | hx2
      · rw [hxb]
        have h_min_in : min a b ∈ (min a b) :: l := List.mem_cons.mpr (Or.inl rfl)
        exact le_trans (hle (min a b) h_min_in) (min_le_right a b)
      · have hx_in : x ∈ (min a b) :: l := List.mem_cons.mpr (Or.inr hx2)
        exact hle x hx_in

/-!
# Numerical Examples Reproducing Calculations
-/

-- Example 1: (1, 2) ~ (2, 4) since 1 * 4 = 2 * 2 = 4
def pair1 : S := (1, ⟨2, by decide⟩)
def pair2 : S := (2, ⟨4, by decide⟩)

example : rel pair1 pair2 := by
  dsimp [rel, pair1, pair2]

-- Example 2: Both pairs map to 1/2 in ℚ under toRat
example : toRat pair1 = 1 / 2 := by
  norm_num [toRat, pair1]

example : toRat pair2 = 1 / 2 := by
  norm_num [toRat, pair2]

-- Example 3: Minimal element in the set {1/2, 1/3} is 1/3
example : min (1 / 2 : ℚ) (1 / 3) = 1 / 3 := by
  norm_num


end Course21127
