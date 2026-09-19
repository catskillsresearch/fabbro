import Mathlib

namespace Course21120Taylor

/-- Degree-9 Taylor polynomial of the integrated expansion
$t^2 - t^4 + (5/6)t^6 - (5/6)t^8$. -/
def T9 (x : ℚ) : ℚ :=
  x ^ 3 / 3 - x ^ 5 / 5 + 5 * x ^ 7 / 42 - 5 * x ^ 9 / 54

end Course21120Taylor
