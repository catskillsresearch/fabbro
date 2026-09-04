import Mathlib

open Finset
open Classical

namespace Course21373

variable {B : Type*} [BooleanAlgebra B]

/-! ### Definitions -/

/-- An atom in a Boolean algebra is a non-bottom element whose only sub-elements are ⊥ and itself.
    Named `IsBooleanAtom` to avoid collision with Mathlib's order-theoretic `IsAtom`. -/
def IsBooleanAtom (a : B) : Prop :=
  a ≠ ⊥ ∧ ∀ x, x ≤ a → x = ⊥ ∨ x = a

/-! ### Part (a): Atoms and Unique Join Representation -/

/-- Distinct atoms are disjoint. -/
theorem isAtom_inf_eq_bot {a b : B} (ha : IsBooleanAtom a) (hb : IsBooleanAtom b) (hne : a ≠ b) :
    a ⊓ b = ⊥ := by
  have hle : a ⊓ b ≤ a := inf_le_left
  cases ha.2 (a ⊓ b) hle with
  | inl h => exact h
  | inr h =>
    have hle2 : a ≤ b := by
      calc a = a ⊓ b := h.symm
      _ ≤ b := inf_le_right
    cases hb.2 a hle2 with
    | inl hbot => exact (ha.1 hbot).elim
    | inr heq => exact (hne heq).elim

/-- An atom is below a join of two elements iff it is below at least one. -/
theorem isAtom_le_sup_iff {a b c : B} (ha : IsBooleanAtom a) :
    a ≤ b ⊔ c ↔ a ≤ b ∨ a ≤ c := by
  constructor
  · intro h
    have hdist : a = (a ⊓ b) ⊔ (a ⊓ c) := by
      calc a = a ⊓ (b ⊔ c) := (inf_eq_left.mpr h).symm
      _ = (a ⊓ b) ⊔ (a ⊓ c) := inf_sup_left a b c
    cases ha.2 (a ⊓ b) inf_le_left with
    | inr hab =>
      left
      calc a = a ⊓ b := hab.symm
      _ ≤ b := inf_le_right
    | inl hab =>
      right
      have hac : a = a ⊓ c := by
        calc a = (a ⊓ b) ⊔ (a ⊓ c) := hdist
        _ = ⊥ ⊔ (a ⊓ c) := congr_arg (· ⊔ (a ⊓ c)) hab
        _ = a ⊓ c := bot_sup_eq (a ⊓ c)
      calc a = a ⊓ c := hac
      _ ≤ c := inf_le_right
  · rintro (h | h)
    · exact le_trans h le_sup_left
    · exact le_trans h le_sup_right

/-- An atom is below a finite join iff it is below some member. -/
theorem isAtom_le_finset_sup {a : B} (ha : IsBooleanAtom a) (s : Finset B) :
    a ≤ s.sup id ↔ ∃ b ∈ s, a ≤ b := by
  induction s using Finset.induction_on with
  | empty =>
    constructor
    · intro h
      rw [Finset.sup_empty] at h
      exact (ha.1 (le_bot_iff.mp h)).elim
    · rintro ⟨b, hb, _⟩
      cases hb
  | @insert b s _ ih =>
    rw [Finset.sup_insert]
    dsimp only [id]
    rw [isAtom_le_sup_iff ha, ih]
    simp only [Finset.mem_insert]
    constructor
    · rintro (h | ⟨c, hc, hac⟩)
      · exact ⟨b, Or.inl rfl, h⟩
      · exact ⟨c, Or.inr hc, hac⟩
    · rintro ⟨c, rfl | hc, hac⟩
      · exact Or.inl hac
      · exact Or.inr ⟨c, hc, hac⟩

/-- If `s` consists of atoms, an atom `a ≤ s.sup id` iff `a ∈ s`. -/
theorem isAtom_le_finset_sup_of_atoms {a : B} (ha : IsBooleanAtom a) {s : Finset B}
    (hs : ∀ b ∈ s, IsBooleanAtom b) :
    a ≤ s.sup id ↔ a ∈ s := by
  rw [isAtom_le_finset_sup ha]
  constructor
  · rintro ⟨b, hb, hab⟩
    have hb_atom := hs b hb
    cases hb_atom.2 a hab with
    | inl hbot => exact (ha.1 hbot).elim
    | inr heq =>
      rw [heq]
      exact hb
  · intro ha_mem
    exact ⟨a, ha_mem, le_rfl⟩

/-- Uniqueness of representation: two subsets of atoms with equal join must be equal. -/
theorem finset_sup_inj_of_atoms {s t : Finset B}
    (hs : ∀ b ∈ s, IsBooleanAtom b) (ht : ∀ b ∈ t, IsBooleanAtom b)
    (h_eq : s.sup id = t.sup id) : s = t := by
  ext a
  constructor
  · intro ha
    have ha_atom := hs a ha
    have hle : a ≤ s.sup id := (isAtom_le_finset_sup_of_atoms ha_atom hs).mpr ha
    rw [h_eq] at hle
    exact (isAtom_le_finset_sup_of_atoms ha_atom ht).mp hle
  · intro ha
    have ha_atom := ht a ha
    have hle : a ≤ t.sup id := (isAtom_le_finset_sup_of_atoms ha_atom ht).mpr ha
    rw [← h_eq] at hle
    exact (isAtom_le_finset_sup_of_atoms ha_atom hs).mp hle

/-! ### Part (b): Representation Map and Characteristic Functions -/

/-- The canonical map sending an element to the atoms below it. -/
noncomputable def repMap (A : Finset B) (x : B) : Finset B :=
  A.filter (fun a => a ≤ x)

theorem repMap_inf (A : Finset B) (x y : B) :
    repMap A (x ⊓ y) = repMap A x ∩ repMap A y := by
  ext a
  simp only [repMap, Finset.mem_filter, Finset.mem_inter, le_inf_iff]
  tauto

theorem repMap_sup {A : Finset B} (hA : ∀ a ∈ A, IsBooleanAtom a) (x y : B) :
    repMap A (x ⊔ y) = repMap A x ∪ repMap A y := by
  ext a
  simp only [repMap, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨haA, hle⟩
    have ha_atom := hA a haA
    rw [isAtom_le_sup_iff ha_atom] at hle
    cases hle with
    | inl h => exact Or.inl ⟨haA, h⟩
    | inr h => exact Or.inr ⟨haA, h⟩
  · rintro (⟨haA, h⟩ | ⟨haA, h⟩)
    · exact ⟨haA, le_trans h le_sup_left⟩
    · exact ⟨haA, le_trans h le_sup_right⟩

theorem repMap_bot {A : Finset B} (hA : ∀ a ∈ A, IsBooleanAtom a) :
    repMap A ⊥ = ∅ := by
  ext a
  simp only [repMap, Finset.mem_filter]
  constructor
  · rintro ⟨haA, hle⟩
    have ha_bot : a = ⊥ := le_bot_iff.mp hle
    exact ((hA a haA).1 ha_bot).elim
  · intro h
    cases h

/-- `repMap` is the inverse of `Finset.sup id` on subsets of atoms. -/
theorem repMap_sup_id {A : Finset B} (hA : ∀ a ∈ A, IsBooleanAtom a) {s : Finset B} (hs : s ⊆ A) :
    repMap A (s.sup id) = s := by
  ext a
  simp only [repMap, Finset.mem_filter]
  constructor
  · rintro ⟨haA, hle⟩
    have ha_atom := hA a haA
    exact (isAtom_le_finset_sup_of_atoms ha_atom (fun b hb => hA b (hs hb))).mp hle
  · intro ha
    have haA := hs ha
    have ha_atom := hA a haA
    refine ⟨haA, ?_⟩
    exact (isAtom_le_finset_sup_of_atoms ha_atom (fun b hb => hA b (hs hb))).mpr ha

/-- Natural equivalence between subsets of `{0, ..., n-1}` and characteristic functions. -/
def finsetToCharFun (n : ℕ) : Finset (Fin n) ≃ (Fin n → Bool) where
  toFun s := fun i => decide (i ∈ s)
  invFun f := Finset.filter (fun i => f i = true) Finset.univ
  left_inv s := by
    ext i
    simp
  right_inv f := by
    ext i
    simp

/-! ### Part (c): Group Action, Fixed Subalgebra, and Orbit Atoms -/

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
def IsFixedAtom (G : Type*) (B : Type*) [BooleanAlgebra B] [SMul G B] (b : B) : Prop :=
  b ∈ fixedPoints G B ∧ b ≠ ⊥ ∧ ∀ x ∈ fixedPoints G B, x ≤ b → x = ⊥ ∨ x = b

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
    IsFixedAtom G B (O.sup id) := by
  refine ⟨hO_fixed, ?_, ?_⟩
  · -- b ≠ ⊥
    rcases hO_ne with ⟨a, ha⟩
    have ha_atom := hO_atoms a ha
    intro hbot
    have hle : a ≤ O.sup id := (isAtom_le_finset_sup_of_atoms ha_atom hO_atoms).mpr ha
    rw [hbot] at hle
    exact ha_atom.1 (le_bot_iff.mp hle)
  · -- x ≤ b → x = ⊥ ∨ x = b
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
