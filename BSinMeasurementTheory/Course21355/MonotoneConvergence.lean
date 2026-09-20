import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.UniformSpace.Real
import BSinMeasurementTheory.Course21355.Completeness

open Filter Topology

namespace Course21355

noncomputable section

/-- Monotone Convergence: a nondecreasing sequence bounded above converges
    to the supremum of its range. -/
theorem monotone_convergence_nondec {a : ℕ → ℝ} (hmono : Monotone a)
    (hbdd : BddAbove (Set.range a)) :
    Tendsto a atTop (𝓝 (sSup (Set.range a))) :=
  tendsto_atTop_isLUB hmono (isLUB_csSup (Set.range_nonempty a) hbdd)

/-- A nonincreasing sequence bounded below converges to the infimum of its range. -/
theorem monotone_convergence_noninc {a : ℕ → ℝ} (hanti : Antitone a)
    (hbdd : BddBelow (Set.range a)) :
    Tendsto a atTop (𝓝 (sInf (Set.range a))) :=
  tendsto_atTop_isGLB hanti (isGLB_csInf (Set.range_nonempty a) hbdd)

end

end Course21355
