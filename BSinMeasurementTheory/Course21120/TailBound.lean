import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import BSinMeasurementTheory.Course21120.Existence
import BSinMeasurementTheory.Course21120.FTC

open Real intervalIntegral Filter Topology MeasureTheory
open scoped Interval

namespace Course21120

/-! ### Comparison majorant on a finite interval -/

/-- The comparison majorant integrates to an arctan increment. -/
theorem majorant_integral (M x : ℝ) :
    ∫ t in M..x, (1 : ℝ) / (1 + t ^ 2) = arctan x - arctan M := by
  simp [one_div, integral_inv_one_add_sq]

theorem continuous_majorant : Continuous fun t : ℝ => (1 : ℝ) / (1 + t ^ 2) :=
  continuous_const.div (continuous_const.add (continuous_pow 2)) (fun _ => by positivity)

/-- Absolute value of the integrand on $[0,M]$ is at most $\arctan M$. -/
theorem abs_integral_le_arctan (M : ℝ) (hM : 0 ≤ M) :
    |∫ t in (0 : ℝ)..M, sin (t ^ 2) / (1 + t ^ 2)| ≤ arctan M := by
  have hf := Course21120FTC.continuous_integrand
  have hg := continuous_majorant
  have h1 : |∫ t in (0 : ℝ)..M, sin (t ^ 2) / (1 + t ^ 2)| ≤
      ∫ t in (0 : ℝ)..M, |sin (t ^ 2) / (1 + t ^ 2)| :=
    abs_integral_le_integral_abs hM
  have hintf : IntervalIntegrable (fun t => |sin (t ^ 2) / (1 + t ^ 2)|) volume 0 M :=
    hf.abs.continuousOn.intervalIntegrable
  have hintg : IntervalIntegrable (fun t => (1 : ℝ) / (1 + t ^ 2)) volume 0 M :=
    hg.continuousOn.intervalIntegrable
  have h2 : ∫ t in (0 : ℝ)..M, |sin (t ^ 2) / (1 + t ^ 2)| ≤
      ∫ t in (0 : ℝ)..M, (1 : ℝ) / (1 + t ^ 2) :=
    integral_mono_on hM hintf hintg fun t _ => abs_integrand_le t
  have h3 : ∫ t in (0 : ℝ)..M, (1 : ℝ) / (1 + t ^ 2) = arctan M := by
    rw [majorant_integral 0 M, arctan_zero, sub_zero]
  linarith

/-- Remaining majorant mass on $[M,x]$ is at most the improper tail
$\pi/2 - \arctan M$. -/
theorem tail_mass_le (M x : ℝ) (_hMx : M ≤ x) :
    arctan x - arctan M ≤ Real.pi / 2 - arctan M := by
  nlinarith [arctan_lt_pi_div_two x]

/-! ### Integration-by-parts weight and density

Following the note: rewrite $\sin(t^2)\,dt = \frac1{2t}\,d(-\cos(t^2))$,
integrate by parts with weight $u(t)=\frac1{2t(1+t^2)}$, and bound using
$|\cos|\le 1$ together with $-u'>0$. -/

/-- Boundary weight $u(t) = 1/(2t(1+t^2))$. -/
noncomputable def ibpWeight (t : ℝ) : ℝ := 1 / (2 * t * (1 + t ^ 2))

/-- The positive density $-u'(t) = (1+3t^2)/(2t^2(1+t^2)^2)$. -/
noncomputable def ibpDensity (t : ℝ) : ℝ :=
  (1 + 3 * t ^ 2) / (2 * t ^ 2 * (1 + t ^ 2) ^ 2)

lemma den_deriv (t : ℝ) :
    HasDerivAt (fun s : ℝ => 2 * s * (1 + s ^ 2)) (2 + 6 * t ^ 2) t := by
  have h1 : HasDerivAt (fun s : ℝ => 2 * s) (2 : ℝ) t := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) t).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow (𝕜 := ℝ) 2 t).const_add (1 : ℝ)
  have hprod := h1.mul h2
  have : (2 : ℝ) * (1 + t ^ 2) + 2 * t * (2 * t) = 2 + 6 * t ^ 2 := by ring
  rwa [this] at hprod

/-- Differentiating the weight recovers the density: $u'(t) = -$`ibpDensity`$\,t$. -/
theorem hasDerivAt_ibpWeight (t : ℝ) (ht : 0 < t) :
    HasDerivAt ibpWeight (-ibpDensity t) t := by
  have hden : 2 * t * (1 + t ^ 2) ≠ 0 := by positivity
  have hd := (den_deriv t).inv hden
  have hfun : ibpWeight = fun s : ℝ => (2 * s * (1 + s ^ 2))⁻¹ := by
    ext s; simp [ibpWeight, one_div]
  rw [hfun]
  have hderiv : -(2 + 6 * t ^ 2) / (2 * t * (1 + t ^ 2)) ^ 2 = -ibpDensity t := by
    unfold ibpDensity
    have hsq : (2 * t * (1 + t ^ 2)) ^ 2 = 4 * t ^ 2 * (1 + t ^ 2) ^ 2 := by ring
    rw [hsq]
    have hnum : 2 + 6 * t ^ 2 = 2 * (1 + 3 * t ^ 2) := by ring
    rw [hnum]
    field_simp
    ring
  rwa [hderiv] at hd

theorem ibpDensity_nonneg (t : ℝ) (ht : 0 < t) : 0 ≤ ibpDensity t := by
  unfold ibpDensity
  apply div_nonneg <;> positivity

theorem ibpWeight_pos (t : ℝ) (ht : 0 < t) : 0 < ibpWeight t := by
  simp [ibpWeight]
  positivity

/-- Twice the weight is the stated IBP contribution $1/(M(1+M^2))$. -/
theorem two_ibpWeight (t : ℝ) (_ht : t ≠ 0) :
    2 * ibpWeight t = 1 / (t * (1 + t ^ 2)) := by
  simp [ibpWeight]
  field_simp

theorem continuousOn_ibpDensity {M X : ℝ} (hM : 0 < M) (hMX : M ≤ X) :
    ContinuousOn ibpDensity (Set.uIcc M X) := by
  have hne : ∀ t ∈ Set.uIcc M X, 2 * t ^ 2 * (1 + t ^ 2) ^ 2 ≠ 0 := by
    intro t ht
    have : t ∈ Set.Icc M X := by rwa [Set.uIcc_of_le hMX] at ht
    have ht0 : 0 < t := lt_of_lt_of_le hM this.1
    positivity
  exact ContinuousOn.div
    (continuous_const.add ((continuous_pow 2).const_mul (3 : ℝ))).continuousOn
    ((((continuous_pow 2).const_mul (2 : ℝ)).mul
        ((continuous_const.add (continuous_pow 2)).pow 2))).continuousOn
    hne

/-- On a finite interval, $\int_M^X (-u')\,dt = u(X)-u(M)$, hence
$\int_M^X$ `ibpDensity` $= u(M)-u(X)$. -/
theorem ibpDensity_integral (M X : ℝ) (hM : 0 < M) (hMX : M ≤ X) :
    ∫ t in M..X, ibpDensity t = ibpWeight M - ibpWeight X := by
  have hderiv : ∀ t ∈ Set.Ioo M X, HasDerivAt ibpWeight (-ibpDensity t) t := by
    intro t ht
    exact hasDerivAt_ibpWeight t (lt_trans hM ht.1)
  have hcont : ContinuousOn ibpWeight (Set.Icc M X) := by
    intro t ht
    exact (hasDerivAt_ibpWeight t (lt_of_lt_of_le hM ht.1)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun t => -ibpDensity t) volume M X :=
    (continuousOn_ibpDensity hM hMX).intervalIntegrable.neg
  have hFTC :=
    integral_eq_sub_of_hasDerivAt_of_le (f := ibpWeight) (f' := fun t => -ibpDensity t)
      hMX hcont hderiv hint
  calc
    ∫ t in M..X, ibpDensity t
        = -∫ t in M..X, -ibpDensity t := by
          rw [intervalIntegral.integral_neg]; ring
    _ = -(ibpWeight X - ibpWeight M) := by rw [hFTC]
    _ = ibpWeight M - ibpWeight X := by ring

/-- Boundary term $u(M)$ plus the density integral is at most $2u(M)$,
matching $|\cos|\le 1$ after sending the upper limit to infinity. -/
theorem ibp_tail_mass_le (M X : ℝ) (hM : 0 < M) (hMX : M ≤ X) :
    ibpWeight M + ∫ t in M..X, ibpDensity t ≤ 2 * ibpWeight M := by
  rw [ibpDensity_integral M X hM hMX]
  have : 0 ≤ ibpWeight X := (ibpWeight_pos X (lt_of_lt_of_le hM hMX)).le
  linarith

/-- IBP remainder bound: $|$tail$| \le 1/(M(1+M^2))$. -/
theorem ibp_tail_bound (M X : ℝ) (hM : 0 < M) (hMX : M ≤ X) :
    ibpWeight M + ∫ t in M..X, ibpDensity t ≤ 1 / (M * (1 + M ^ 2)) := by
  calc
    ibpWeight M + ∫ t in M..X, ibpDensity t
        ≤ 2 * ibpWeight M := ibp_tail_mass_le M X hM hMX
    _ = 1 / (M * (1 + M ^ 2)) := two_ibpWeight M hM.ne'

/-! ### Combined cutoff bound -/

/-- Combined comparison + integration-by-parts bound:
$|f(\infty)| \le \arctan M + 1/(M(1+M^2))$. -/
noncomputable def limAbsBound (M : ℝ) : ℝ :=
  arctan M + 1 / (M * (1 + M ^ 2))

theorem limAbsBound_eq (M : ℝ) (hM : 0 < M) :
    limAbsBound M = arctan M + 2 * ibpWeight M := by
  simp [limAbsBound, two_ibpWeight M hM.ne']

/-- Finite-cutoff form of the combined bound from the note. -/
theorem limAbsBound_ge_pieces (M X : ℝ) (hM : 0 < M) (hMX : M ≤ X) :
    |∫ t in (0 : ℝ)..M, sin (t ^ 2) / (1 + t ^ 2)| +
        (ibpWeight M + ∫ t in M..X, ibpDensity t) ≤
      limAbsBound M := by
  have h1 := abs_integral_le_arctan M hM.le
  have h2 := ibp_tail_bound M X hM hMX
  simp only [limAbsBound]
  linarith

/-- At $M = 1$ the bound is exactly $\pi/4 + 1/2$. -/
theorem limAbsBound_one : limAbsBound 1 = π / 4 + 1 / 2 := by
  simp [limAbsBound, arctan_one]
  norm_num

/-- Decimal form of the $M = 1$ bound: $\pi/4 + 1/2 < 1.2854$. -/
theorem limAbsBound_one_lt : limAbsBound 1 < 12854 / 10000 := by
  rw [limAbsBound_one]
  have hπ : π < 31416 / 10000 := by
    convert pi_lt_d4 using 1
    norm_num
  nlinarith

end Course21120
