import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace Course21355

/-- Completeness / least-upper-bound property of \(\mathbb{R}\). -/
theorem completeness_axiom (s : Set ℝ) (hne : s.Nonempty) (hbdd : BddAbove s) :
    ∃ M : ℝ, IsLUB s M :=
  ⟨sSup s, isLUB_csSup hne hbdd⟩

/-- Dual form: a nonempty set bounded below has an infimum. -/
theorem completeness_axiom_inf (s : Set ℝ) (hne : s.Nonempty) (hbdd : BddBelow s) :
    ∃ m : ℝ, IsGLB s m :=
  ⟨sInf s, isGLB_csInf hne hbdd⟩

end Course21355
