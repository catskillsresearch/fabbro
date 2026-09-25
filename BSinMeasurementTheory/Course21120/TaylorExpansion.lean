import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Course21120Taylor

/-! ### Truncated expansions of the factors

Following the note: expand $\sin(t^2)$ and $1/(1+t^2)$ around $t=0$,
multiply through degree $8$, then integrate term by term. -/

/-- Truncation of $\sin(t^2) = t^2 - t^6/6 + O(t^{10})$. -/
def sinTrunc (t : ℚ) : ℚ := t ^ 2 - t ^ 6 / 6

/-- Next term in $\sin(t^2)$ after `sinTrunc`: $t^{10}/120$. -/
def sinNextTerm (t : ℚ) : ℚ := t ^ 10 / 120

/-- Sin truncation through the $t^{10}$ term. -/
def sinTrunc10 (t : ℚ) : ℚ := sinTrunc t + sinNextTerm t

/-- Truncation of $1/(1+t^2) = 1 - t^2 + t^4 - t^6 + O(t^8)$. -/
def geomTrunc (t : ℚ) : ℚ := 1 - t ^ 2 + t ^ 4 - t ^ 6

/-- Next geometric term after `geomTrunc`: $t^8$. -/
def geomNextTerm (t : ℚ) : ℚ := t ^ 8

/-- Geometric truncation through degree $8$. -/
def geomTrunc8 (t : ℚ) : ℚ := geomTrunc t + geomNextTerm t

/-- Exact product of the two factor truncations (still includes degree $\ge 10$). -/
def productExact (t : ℚ) : ℚ := sinTrunc t * geomTrunc t

/-- Terms of degree $\ge 10$ in the exact product:
$-\frac16 t^{10} + \frac16 t^{12}$. -/
def productTail (t : ℚ) : ℚ := -(1 / 6) * t ^ 10 + (1 / 6) * t ^ 12

/-- Degree-8 truncation of the product:
$t^2 - t^4 + \frac56 t^6 - \frac56 t^8$. -/
def gTrunc (t : ℚ) : ℚ :=
  t ^ 2 - t ^ 4 + (5 / 6) * t ^ 6 - (5 / 6) * t ^ 8

/-- Expanding the product recovers the claimed degree-8 polynomial plus
an explicit $O(t^{10})$ remainder. -/
theorem productExact_eq (t : ℚ) :
    productExact t = gTrunc t + productTail t := by
  simp [productExact, sinTrunc, geomTrunc, gTrunc, productTail]
  ring

/-- Multiplying truncations and discarding degree $\ge 10$ yields `gTrunc`. -/
theorem product_trunc_eq (t : ℚ) :
    productExact t - productTail t = gTrunc t := by
  rw [productExact_eq]
  ring

/-! ### Term-by-term integration

Each monomial $c\,t^n$ in `gTrunc` integrates from $0$ to $x$ as
$c\,x^{n+1}/(n+1)$. -/

/-- Formal indefinite integral of a monomial $c\,t^n$, evaluated at $x$
(vanishing at $0$). -/
def integrateMonomial (c : ℚ) (n : ℕ) (x : ℚ) : ℚ :=
  c * x ^ (n + 1) / (n + 1)

/-- Degree-9 polynomial obtained by integrating `gTrunc` term by term. -/
def T9 (x : ℚ) : ℚ :=
  integrateMonomial 1 2 x +
    integrateMonomial (-1) 4 x +
    integrateMonomial (5 / 6) 6 x +
    integrateMonomial (-(5 / 6)) 8 x

/-- Unfolded form of the term-by-term integral. -/
theorem T9_eq_sum (x : ℚ) :
    T9 x =
      x ^ 3 / 3 - x ^ 5 / 5 + (5 / 6) * (x ^ 7 / 7) - (5 / 6) * (x ^ 9 / 9) := by
  simp [T9, integrateMonomial]
  ring

/-- Integrating the $t^6$ coefficient: $\frac56 / 7 = \frac5{42}$. -/
theorem integrate_coeff_t6 : (5 / 6 : ℚ) / 7 = 5 / 42 := by norm_num

/-- Integrating the $t^8$ coefficient: $\frac56 / 9 = \frac5{54}$. -/
theorem integrate_coeff_t8 : (5 / 6 : ℚ) / 9 = 5 / 54 := by norm_num

/-- Simplifying the integrated coefficients recovers the form in the note:
$\frac{x^3}{3} - \frac{x^5}{5} + \frac{5}{42}x^7 - \frac{5}{54}x^9$. -/
theorem T9_simplified (x : ℚ) :
    T9 x = x ^ 3 / 3 - x ^ 5 / 5 + 5 * x ^ 7 / 42 - 5 * x ^ 9 / 54 := by
  rw [T9_eq_sum]
  have h6 : (5 / 6 : ℚ) * (x ^ 7 / 7) = 5 * x ^ 7 / 42 := by
    calc
      (5 / 6 : ℚ) * (x ^ 7 / 7) = ((5 / 6) / 7) * x ^ 7 := by ring
      _ = (5 / 42) * x ^ 7 := by rw [integrate_coeff_t6]
      _ = 5 * x ^ 7 / 42 := by ring
  have h8 : (5 / 6 : ℚ) * (x ^ 9 / 9) = 5 * x ^ 9 / 54 := by
    calc
      (5 / 6 : ℚ) * (x ^ 9 / 9) = ((5 / 6) / 9) * x ^ 9 := by ring
      _ = (5 / 54) * x ^ 9 := by rw [integrate_coeff_t8]
      _ = 5 * x ^ 9 / 54 := by ring
  rw [h6, h8]

end Course21120Taylor
