import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Order
import BSinMeasurementTheory.Course21651.BooleanHom

set_option linter.unusedSectionVars false

open Topology Set

namespace Course21651

namespace StoneRepresentation

variable (B : Type*) [BooleanAlgebra B]

/-- The Stone mapping $\hat{b} = \{u \in X \mid u(b) = \mathrm{true}\}$. -/
def stoneMap (b : B) : Set (StoneSpace B) :=
  { u | u.1 b = true }

theorem stoneMap_top : stoneMap B ⊤ = univ := by
  ext ⟨u, hu⟩
  change (u ⊤ = true) ↔ True
  simp [hu.map_top]

theorem stoneMap_bot : stoneMap B ⊥ = ∅ := by
  ext ⟨u, hu⟩
  change (u ⊥ = true) ↔ False
  have h := hu.map_bot
  cases hu_bot : u ⊥
  · simp
  · rw [hu_bot] at h; contradiction

theorem stoneMap_inf (x y : B) :
    stoneMap B (x ⊓ y) = stoneMap B x ∩ stoneMap B y := by
  ext ⟨u, hu⟩
  change (u (x ⊓ y) = true) ↔ (u x = true ∧ u y = true)
  rw [hu.map_inf x y, Bool.and_eq_true]

theorem stoneMap_sup (x y : B) :
    stoneMap B (x ⊔ y) = stoneMap B x ∪ stoneMap B y := by
  ext ⟨u, hu⟩
  change (u (x ⊔ y) = true) ↔ (u x = true ∨ u y = true)
  rw [hu.map_sup x y, Bool.or_eq_true]

theorem stoneMap_compl (x : B) :
    stoneMap B (xᶜ) = (stoneMap B x)ᶜ := by
  ext ⟨u, hu⟩
  change (u (xᶜ) = true) ↔ ¬(u x = true)
  rw [hu.map_compl x]
  cases u x <;> simp

theorem isClopen_stoneMap (b : B) : IsClopen (stoneMap B b) := by
  have h_cont : Continuous (fun (u : StoneSpace B) => u.1 b) :=
    (@continuous_apply B (fun _ => Bool) _ b).comp continuous_subtype_val
  have h_open : IsOpen (stoneMap B b) := by
    change IsOpen ((fun (u : StoneSpace B) => u.1 b) ⁻¹' ({true} : Set Bool))
    exact (isOpen_discrete ({true} : Set Bool)).preimage h_cont
  have h_closed : IsClosed (stoneMap B b) := by
    change IsClosed ((fun (u : StoneSpace B) => u.1 b) ⁻¹' ({true} : Set Bool))
    exact (isClosed_discrete ({true} : Set Bool)).preimage h_cont
  exact ⟨h_closed, h_open⟩

end StoneRepresentation

end Course21651
