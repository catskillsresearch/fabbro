import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.BooleanAlgebra.Basic
import BSinMeasurementTheory.Course21373.AtomJoin

open Finset
open Classical

namespace Course21373

variable {B : Type*} [BooleanAlgebra B]
variable {G : Type*} [SMul G B]

/-- The fixed-point set of the action. -/
def fixedPoints (G : Type*) (B : Type*) [SMul G B] : Set B :=
  {x : B | ∀ g : G, g • x = x}

/-- An action of G on B by Boolean algebra automorphisms. -/
class BooleanAction (G : Type*) (B : Type*) [BooleanAlgebra B] [SMul G B] : Prop where
  smul_sup : ∀ (g : G) (x y : B), g • (x ⊔ y) = (g • x) ⊔ (g • y)
  smul_inf : ∀ (g : G) (x y : B), g • (x ⊓ y) = (g • x) ⊓ (g • y)
  smul_compl : ∀ (g : G) (x : B), g • (xᶜ) = (g • x)ᶜ
  smul_bot : ∀ (g : G), g • (⊥ : B) = ⊥
  smul_top : ∀ (g : G), g • (⊤ : B) = ⊤

theorem fixed_bot [BooleanAction G B] : (⊥ : B) ∈ fixedPoints G B := fun g =>
  BooleanAction.smul_bot g

theorem fixed_top [BooleanAction G B] : (⊤ : B) ∈ fixedPoints G B := fun g =>
  BooleanAction.smul_top g

theorem fixed_sup [BooleanAction G B] {x y : B}
    (hx : x ∈ fixedPoints G B) (hy : y ∈ fixedPoints G B) :
    x ⊔ y ∈ fixedPoints G B := by
  intro g
  rw [BooleanAction.smul_sup, hx g, hy g]

theorem fixed_inf [BooleanAction G B] {x y : B}
    (hx : x ∈ fixedPoints G B) (hy : y ∈ fixedPoints G B) :
    x ⊓ y ∈ fixedPoints G B := by
  intro g
  rw [BooleanAction.smul_inf, hx g, hy g]

theorem fixed_compl [BooleanAction G B] {x : B}
    (hx : x ∈ fixedPoints G B) :
    xᶜ ∈ fixedPoints G B := by
  intro g
  rw [BooleanAction.smul_compl, hx g]

/-- An atom of the fixed-point subalgebra. -/
class IsFixedAtom (G : Type*) (B : Type*) [BooleanAlgebra B] [SMul G B] (b : B) : Prop where
  mem_fixed : b ∈ fixedPoints G B
  ne_bot : b ≠ ⊥
  le_bot_or_self : ∀ x ∈ fixedPoints G B, x ≤ b → x = ⊥ ∨ x = b

/-- Distribution of meet over a finite join. -/
theorem inf_finset_sup (x : B) (s : Finset B) :
    x ⊓ s.sup id = s.sup (fun a => x ⊓ a) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sup_empty, inf_bot_eq]
  | @insert b s _ ih =>
    rw [Finset.sup_insert]
    dsimp only [id]
    rw [inf_sup_left, ih, Finset.sup_insert]

theorem sup_congr_bot {s : Finset B} {f : B → B} (h : ∀ a ∈ s, f a = ⊥) :
    s.sup f = ⊥ := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sup_empty]
  | @insert b s _ ih =>
    rw [Finset.sup_insert]
    have hb : f b = ⊥ := h b (Finset.mem_insert_self b s)
    have hs : ∀ a ∈ s, f a = ⊥ := fun a ha => h a (Finset.mem_insert_of_mem ha)
    rw [hb, ih hs, bot_sup_eq]

/-- The join over an orbit of atoms is an atom of the fixed-point subalgebra. -/
theorem orbit_sup_isFixedAtom {O : Finset B}
    (hO_ne : O.Nonempty)
    (hO_atoms : ∀ a ∈ O, IsBooleanAtom a)
    (hO_fixed : O.sup id ∈ fixedPoints G B)
    (hO_min : ∀ x ∈ fixedPoints G B, (∀ a ∈ O, a ≤ x) ∨ (∀ a ∈ O, a ⊓ x = ⊥)) :
    IsFixedAtom G B (O.sup id) where
  mem_fixed := hO_fixed
  ne_bot := by
    rcases hO_ne with ⟨a, ha⟩
    have ha_atom := hO_atoms a ha
    intro hbot
    have hle : a ≤ O.sup id := (isAtom_le_finset_sup_of_atoms ha_atom hO_atoms).mpr ha
    rw [hbot] at hle
    exact ha_atom.ne_bot (le_bot_iff.mp hle)
  le_bot_or_self := by
    intro x hx hle
    rcases hO_min x hx with (hall | hnone)
    · right
      have hsup_le : O.sup id ≤ x := by
        apply Finset.sup_le
        intro a ha
        exact hall a ha
      exact le_antisymm hle hsup_le
    · left
      have hx_eq : x = x ⊓ O.sup id := (inf_eq_left.mpr hle).symm
      rw [hx_eq, inf_finset_sup]
      apply sup_congr_bot
      intro a ha
      rw [inf_comm]
      exact hnone a ha

end Course21373
