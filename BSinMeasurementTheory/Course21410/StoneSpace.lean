import Mathlib

namespace Course21410

namespace ScottMeasurementTheory

/-- Ultrafilters on a Boolean algebra, as used for the Stone space. -/
structure IsUltrafilter {B : Type*} [BooleanAlgebra B] (U : Set B) : Prop where
  mem_top : ⊤ ∈ U
  not_mem_bot : ⊥ ∉ U
  mem_inf : ∀ {a b}, a ∈ U → b ∈ U → a ⊓ b ∈ U
  upward : ∀ {a b}, a ∈ U → a ≤ b → b ∈ U
  mem_or : ∀ a, a ∈ U ∨ aᶜ ∈ U

/-- Points of the Stone space. -/
def Stone (B : Type*) [BooleanAlgebra B] :=
  { U : Set B // IsUltrafilter U }

/-- Basic clopen \(\widehat{a} = \{U \mid a \in U\}\). -/
def stoneClopen {B : Type*} [BooleanAlgebra B] (a : B) : Set (Stone B) :=
  {U | a ∈ U.1}

theorem stoneClopen_top {B : Type*} [BooleanAlgebra B] :
    stoneClopen (⊤ : B) = Set.univ := by
  ext U
  simp [stoneClopen, U.2.mem_top]

theorem stoneClopen_bot {B : Type*} [BooleanAlgebra B] :
    stoneClopen (⊥ : B) = ∅ := by
  ext U
  simp [stoneClopen, U.2.not_mem_bot]

theorem stoneClopen_inf {B : Type*} [BooleanAlgebra B] (a b : B) :
    stoneClopen (a ⊓ b) = stoneClopen a ∩ stoneClopen b := by
  ext U
  constructor
  · intro h
    exact ⟨U.2.upward h inf_le_left, U.2.upward h inf_le_right⟩
  · intro ⟨ha, hb⟩
    exact U.2.mem_inf ha hb

theorem stoneClopen_compl {B : Type*} [BooleanAlgebra B] (a : B) :
    stoneClopen aᶜ = (stoneClopen a)ᶜ := by
  ext U
  constructor
  · intro h ha
    have hab : a ⊓ aᶜ ∈ U.1 := U.2.mem_inf ha h
    rw [inf_compl_eq_bot] at hab
    exact U.2.not_mem_bot hab
  · intro h
    rcases U.2.mem_or a with ha | hc
    · exact (h ha).elim
    · exact hc

end ScottMeasurementTheory

end Course21410
