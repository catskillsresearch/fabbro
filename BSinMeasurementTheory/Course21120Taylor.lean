import Mathlib

namespace Course21120Taylor

/-!
#### Taylor Series Estimation of f(0.5)

Integrand Taylor expansion around t = 0:
  g(t) = sin(t²) / (1 + t²) = t² - t⁴ + (5/6) t⁶ - (5/6) t⁸ + O(t¹⁰)

Integrating term-by-term from 0 to x:
  T₉(x) = x³/3 - x⁵/5 + (5/42) x⁷ - (5/54) x⁹
-/

/-- Degree-9 Taylor polynomial approximation for f(x) -/
def T9 (x : ℚ) : ℚ :=
  x ^ 3 / 3 - x ^ 5 / 5 + 5 * x ^ 7 / 42 - 5 * x ^ 9 / 54

/-! ###### Step 1: Verification of individual terms at x = 1/2 -/

theorem term1_eq : (1 / 2 : ℚ) ^ 3 / 3 = 1 / 24 := by norm_num
theorem term2_eq : (1 / 2 : ℚ) ^ 5 / 5 = 1 / 160 := by norm_num
theorem term3_eq : 5 * (1 / 2 : ℚ) ^ 7 / 42 = 5 / 5376 := by norm_num
theorem term4_eq : 5 * (1 / 2 : ℚ) ^ 9 / 54 = 5 / 27648 := by norm_num

/-! ###### Step 2: Exact sum of the terms -/

/-- The exact rational value of T₉(1/2) is 34997 / 967680 -/
theorem T9_half_eq : T9 (1 / 2) = 34997 / 967680 := by
  dsimp [T9]
  norm_num

/-! ###### Step 3: Four-decimal-place accuracy bounds -/

/-- T₉(1/2) lies strictly between 0.03615 and 0.03625, 
    so it rounds to 0.0362 to 4 decimal places. -/
theorem T9_half_rounds_to_0_0362 :
    (3615 : ℚ) / 100000 < T9 (1 / 2) ∧ T9 (1 / 2) < 3625 / 100000 := by
  rw [T9_half_eq]
  norm_num

/-- Explicit distance to 0.0362 is less than 0.00005 (half of 10⁻⁴) -/
theorem T9_half_close_to_0_0362 :
    T9 (1 / 2) - 362 / 10000 < 5 / 100000 ∧
    362 / 10000 - T9 (1 / 2) < 5 / 100000 := by
  rw [T9_half_eq]
  norm_num

/-! ###### Step 4: Verification of the Truncation Error Bound -/

/-- The next non-zero term in the alternating series bounds the tail error:
    |R(0.5)| ≤ (101 / 1320) * (1/2)¹¹ -/
def truncation_error : ℚ := (101 / 1320) * (1 / 2) ^ 11

theorem truncation_error_eq : truncation_error = 101 / 2703360 := by
  dsimp [truncation_error]
  norm_num

/-- The truncation error is strictly less than 10⁻⁴ (0.0001) -/
theorem truncation_error_lt : truncation_error < 1 / 10000 := by
  rw [truncation_error_eq]
  norm_num

/-! ###### Step 5: Evaluations (Inspect in Lean InfoView) -/

-- Float value of each term:
#eval (1.0 / 24.0 : Float)                -- 0.041666666666666664
#eval (1.0 / 160.0 : Float)               -- 0.00625
#eval (5.0 / 5376.0 : Float)              -- 0.000929985119047619
#eval (5.0 / 27648.0 : Float)             -- 0.0001808449074074074

-- Float value of T₉(0.5):
#eval (34997.0 / 967680.0 : Float)        -- 0.03616588128306879

-- Float value of the truncation error:
#eval (101.0 / 2703360.0 : Float)         -- 0.000037360913825757576


end Course21120Taylor
