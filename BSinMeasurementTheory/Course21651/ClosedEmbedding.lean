import Mathlib
import BSinMeasurementTheory.Course21651.BooleanHom

set_option linter.unusedSectionVars false

open Topology Set

namespace Course21651

namespace StoneRepresentation

variable (B : Type*) [BooleanAlgebra B]

theorem continuous_bool_and (x y : B) :
    Continuous (fun f : B → Bool => f x && f y) := by
  have : (fun f : B → Bool => f x && f y) = (fun p : Bool × Bool => p.1 && p.2) ∘ (fun f => (f x, f y)) := rfl
  rw [this]
  exact continuous_of_discreteTopology.comp
    ((@continuous_apply B (fun _ => Bool) _ x).prodMk (@continuous_apply B (fun _ => Bool) _ y))

theorem continuous_bool_or (x y : B) :
    Continuous (fun f : B → Bool => f x || f y) := by
  have : (fun f : B → Bool => f x || f y) = (fun p : Bool × Bool => p.1 || p.2) ∘ (fun f => (f x, f y)) := rfl
  rw [this]
  exact continuous_of_discreteTopology.comp
    ((@continuous_apply B (fun _ => Bool) _ x).prodMk (@continuous_apply B (fun _ => Bool) _ y))

theorem continuous_bool_not (x : B) :
    Continuous (fun f : B → Bool => !f x) := by
  have : (fun f : B → Bool => !f x) = (! ·) ∘ (fun f => f x) := rfl
  rw [this]
  exact continuous_of_discreteTopology.comp (@continuous_apply B (fun _ => Bool) _ x)

/-- The set of homomorphisms as an explicit intersection of closed equalizer sets in `B → Bool`. -/
def isHomSet : Set (B → Bool) :=
  { f | f ⊤ = true } ∩
  { f | f ⊥ = false } ∩
  (⋂ (x : B) (y : B), { f | f (x ⊓ y) = (f x && f y) }) ∩
  (⋂ (x : B) (y : B), { f | f (x ⊔ y) = (f x || f y) }) ∩
  (⋂ (x : B), { f | f (xᶜ) = (!f x) })

theorem isHomSet_isClosed : IsClosed (isHomSet B) := by
  dsimp [isHomSet]
  refine IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_) ?_
  · exact isClosed_eq (@continuous_apply B (fun _ => Bool) _ ⊤) continuous_const
  · exact isClosed_eq (@continuous_apply B (fun _ => Bool) _ ⊥) continuous_const
  · refine isClosed_iInter (fun x => isClosed_iInter (fun y => ?_))
    exact isClosed_eq (@continuous_apply B (fun _ => Bool) _ (x ⊓ y)) (continuous_bool_and B x y)
  · refine isClosed_iInter (fun x => isClosed_iInter (fun y => ?_))
    exact isClosed_eq (@continuous_apply B (fun _ => Bool) _ (x ⊔ y)) (continuous_bool_or B x y)
  · refine isClosed_iInter (fun x => ?_)
    exact isClosed_eq (@continuous_apply B (fun _ => Bool) _ (xᶜ)) (continuous_bool_not B x)

theorem isBooleanHom_iff_mem_isHomSet (f : B → Bool) :
    IsBooleanHom f ↔ f ∈ isHomSet B := by
  constructor
  · intro hf
    refine ⟨⟨⟨⟨hf.map_top, hf.map_bot⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [Set.mem_iInter]; intro x; rw [Set.mem_iInter]; intro y; exact hf.map_inf x y
    · rw [Set.mem_iInter]; intro x; rw [Set.mem_iInter]; intro y; exact hf.map_sup x y
    · rw [Set.mem_iInter]; intro x; exact hf.map_compl x
  · intro ⟨⟨⟨⟨ht, hb⟩, hi⟩, hs⟩, hc⟩
    exact ⟨ht, hb,
      fun x y => (Set.mem_iInter.mp (Set.mem_iInter.mp hi x)) y,
      fun x y => (Set.mem_iInter.mp (Set.mem_iInter.mp hs x)) y,
      fun x => Set.mem_iInter.mp hc x⟩

end StoneRepresentation

end Course21651
