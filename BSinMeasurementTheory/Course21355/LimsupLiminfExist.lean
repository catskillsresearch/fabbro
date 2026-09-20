import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.UniformSpace.Real
import BSinMeasurementTheory.Course21355.TailExtremes

open Filter Topology

namespace Course21355

noncomputable section

theorem limsup_liminf_exist (x : ℕ → ℝ) (m M : ℝ) (h : ∀ n, m ≤ x n ∧ x n ≤ M) :
    (∃ L_sup : ℝ, Tendsto (tailSup x) atTop (𝓝 L_sup)) ∧
    (∃ L_inf : ℝ, Tendsto (tailInf x) atTop (𝓝 L_inf)) := by
  have h_sup_bdd : BddBelow (Set.range (tailSup x)) := by
    refine ⟨m, fun y ⟨k, hk⟩ => ?_⟩
    subst hk
    have h1 : m ≤ x (0 + k) := (h (0 + k)).1
    have hb : BddAbove (Set.range (fun n : ℕ => x (n + k))) :=
      ⟨M, fun r ⟨i, hi⟩ => hi ▸ (h (i + k)).2⟩
    have h2 : x (0 + k) ≤ tailSup x k := le_ciSup hb 0
    exact le_trans h1 h2
  have h_inf_bdd : BddAbove (Set.range (tailInf x)) := by
    refine ⟨M, fun y ⟨k, hk⟩ => ?_⟩
    subst hk
    have hb : BddBelow (Set.range (fun n : ℕ => x (n + k))) :=
      ⟨m, fun r ⟨i, hi⟩ => hi ▸ (h (i + k)).1⟩
    have h1 : tailInf x k ≤ x (0 + k) := ciInf_le hb 0
    have h2 : x (0 + k) ≤ M := (h (0 + k)).2
    exact le_trans h1 h2
  exact ⟨⟨⨅ k, tailSup x k, tendsto_atTop_ciInf (tailSup_antitone x M (fun n => (h n).2)) h_sup_bdd⟩,
         ⟨⨆ k, tailInf x k, tendsto_atTop_ciSup (tailInf_monotone x m (fun n => (h n).1)) h_inf_bdd⟩⟩

end

end Course21355
