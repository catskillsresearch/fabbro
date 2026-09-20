import Mathlib.Data.Int.Basic

namespace Course21355

/-- Computable alternating sequence used to inspect the example of (c). -/
def altSeqZ (n : ℕ) : ℤ := (-1 : ℤ) ^ n

#eval altSeqZ 0
#eval altSeqZ 1
#eval altSeqZ 2
#eval altSeqZ 3

end Course21355
