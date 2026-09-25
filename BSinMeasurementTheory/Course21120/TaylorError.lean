import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import BSinMeasurementTheory.Course21120.TaylorExpansion

namespace Course21120Taylor

/-! ### Integrand truncation error from the series

Using `sinTrunc10` and `geomTrunc8` from `TaylorExpansion`, extract the
$t^{10}$ coefficient and integrate the resulting bound. -/

/-- The three contributions to the $t^{10}$ coefficient in
$\mathrm{sinTrunc10}\cdot\mathrm{geomTrunc8}$:
$t^2\cdot t^8$, $(-\tfrac16 t^6)\cdot t^4$, and $\tfrac1{120}t^{10}\cdot 1$. -/
theorem t10_coeff_parts : (1 : ℚ) - 1 / 6 + 1 / 120 = 101 / 120 := by
  norm_num

/-- Degree-$\ge 12$ remainder after isolating $g_{\mathrm{trunc}}$ and the
$t^{10}$ term in the extended product. -/
def productHigher (t : ℚ) : ℚ :=
  (19 / 120) * t ^ 12 - (19 / 120) * t ^ 14 - (1 / 120) * t ^ 16 +
    (1 / 120) * t ^ 18

/-- Expanding the extended truncations recovers `gTrunc`, the $t^{10}$
monomial with coefficient $\frac{101}{120}$, and an explicit higher remainder. -/
theorem product_sin10_geom8_eq (t : ℚ) :
    sinTrunc10 t * geomTrunc8 t =
      gTrunc t + (101 / 120) * t ^ 10 + productHigher t := by
  simp [sinTrunc10, sinNextTerm, sinTrunc, geomTrunc8, geomNextTerm, geomTrunc,
    gTrunc, productHigher]
  ring

/-- The $t^{10}$ term extracted from the prior series development. -/
theorem t10_term_from_series (t : ℚ) :
    sinTrunc10 t * geomTrunc8 t - gTrunc t - productHigher t =
      (101 / 120) * t ^ 10 := by
  rw [product_sin10_geom8_eq]
  ring

/-- Same coefficient written as in the note:
$1 - \tfrac16 + \tfrac1{120}$. -/
theorem t10_term_english (t : ℚ) :
    sinTrunc10 t * geomTrunc8 t - gTrunc t - productHigher t =
      ((1 : ℚ) - 1 / 6 + 1 / 120) * t ^ 10 := by
  rw [t10_term_from_series, t10_coeff_parts]

/-- Truncation-error bound for the integrand after degree $8$:
$R_{\mathrm{integrand}}(t) = \frac{101}{120}\,t^{10}$. -/
def Rintegrand (t : ℚ) : ℚ := (101 / 120) * t ^ 10

/-- The bound stated in the note. -/
theorem Rintegrand_le_form (t : ℚ) :
    Rintegrand t = ((1 : ℚ) - 1 / 6 + 1 / 120) * t ^ 10 := by
  simp only [Rintegrand]
  rw [t10_coeff_parts]

/-- The integrand error bound is exactly the extracted $t^{10}$ term. -/
theorem Rintegrand_eq_extracted (t : ℚ) :
    Rintegrand t =
      sinTrunc10 t * geomTrunc8 t - gTrunc t - productHigher t := by
  rw [Rintegrand, ← t10_term_from_series]

/-! ### Integrate the integrand bound from $0$ to $1/2$ -/

/-- Integrating $\frac{101}{120}\,t^{10}$ contributes the factor $\frac{101}{1320}$. -/
theorem integrate_Rintegrand_coeff : (101 / 120 : ℚ) / 11 = 101 / 1320 := by
  norm_num

/-- Alternating-series / integrated remainder bound
$|R_f(1/2)| \le \int_0^{1/2} R_{\mathrm{integrand}}(t)\,dt$. -/
def truncation_error : ℚ := integrateMonomial (101 / 120) 10 (1 / 2)

theorem truncation_error_eq_integral :
    truncation_error = (101 / 120) * ((1 / 2 : ℚ) ^ 11 / 11) := by
  simp [truncation_error, integrateMonomial]
  ring

theorem truncation_error_eq_note :
    truncation_error = (101 / 1320) * (1 / 2 : ℚ) ^ 11 := by
  rw [truncation_error_eq_integral]
  have h : (101 / 120 : ℚ) * ((1 / 2) ^ 11 / 11) =
      ((101 / 120) / 11) * (1 / 2) ^ 11 := by ring
  rw [h, integrate_Rintegrand_coeff]

theorem truncation_error_eq : truncation_error = 101 / 2703360 := by
  rw [truncation_error_eq_note]
  norm_num

/-- The truncation error is strictly less than $10^{-4}$. -/
theorem truncation_error_lt : truncation_error < 1 / 10000 := by
  rw [truncation_error_eq]
  norm_num

#eval ((101 / 2703360 : Float))

end Course21120Taylor
