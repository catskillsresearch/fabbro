import Mathlib

set_option linter.unusedSectionVars false

open Topology Set

namespace Course21651

namespace StoneRepresentation

variable (B : Type*) [BooleanAlgebra B]

/-!
### Characterization of Boolean Homomorphisms to Bool
-/

/-- Predicate characterizing Boolean algebra homomorphisms from `B` to `Bool`. -/
def isHom (f : B → Bool) : Prop :=
  f ⊤ = true ∧
  f ⊥ = false ∧
  (∀ x y, f (x ⊓ y) = (f x && f y)) ∧
  (∀ x y, f (x ⊔ y) = (f x || f y)) ∧
  (∀ x, f (xᶜ) = (!f x))

/-- The Stone space $X = \mathrm{Stone}(B)$ realized as the subtype of homomorphisms in `B → Bool`. -/
@[reducible]
def StoneSpace : Type _ := { f : B → Bool // isHom B f }

/-!
### (d) Realization as a Closed Subspace of B → Bool
-/

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

theorem isHom_iff_mem_isHomSet (f : B → Bool) :
    isHom B f ↔ f ∈ isHomSet B := by
  dsimp [isHom, isHomSet]
  constructor
  · intro ⟨ht, hb, hi, hs, hc⟩
    refine ⟨⟨⟨⟨ht, hb⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [Set.mem_iInter]; intro x; rw [Set.mem_iInter]; intro y; exact hi x y
    · rw [Set.mem_iInter]; intro x; rw [Set.mem_iInter]; intro y; exact hs x y
    · rw [Set.mem_iInter]; intro x; exact hc x
  · intro ⟨⟨⟨⟨ht, hb⟩, hi⟩, hs⟩, hc⟩
    refine ⟨ht, hb, ?_, ?_, ?_⟩
    · intro x y; exact (Set.mem_iInter.mp (Set.mem_iInter.mp hi x)) y
    · intro x y; exact (Set.mem_iInter.mp (Set.mem_iInter.mp hs x)) y
    · intro x; exact Set.mem_iInter.mp hc x

/-!
### (a) & (b) Compactness, Hausdorff, and Total Disconnectedness
-/

instance : T2Space (StoneSpace B) := inferInstance

instance : TotallyDisconnectedSpace (StoneSpace B) := inferInstance

instance [Finite B] : CompactSpace (StoneSpace B) := inferInstance

/-!
### (c) Stone Clopen Map and Properties (Stone's Representation Theorem)
-/

/-- The Stone mapping $\hat{b} = \{u \in X \mid u(b) = \mathrm{true}\}$. -/
def stoneMap (b : B) : Set (StoneSpace B) :=
  { u | u.1 b = true }

theorem stoneMap_top : stoneMap B ⊤ = univ := by
  ext ⟨u, hu⟩
  change (u ⊤ = true) ↔ True
  simp [hu.1]

theorem stoneMap_bot : stoneMap B ⊥ = ∅ := by
  ext ⟨u, hu⟩
  change (u ⊥ = true) ↔ False
  have h := hu.2.1
  cases hu_bot : u ⊥
  · simp
  · rw [hu_bot] at h; contradiction

theorem stoneMap_inf (x y : B) :
    stoneMap B (x ⊓ y) = stoneMap B x ∩ stoneMap B y := by
  ext ⟨u, hu⟩
  change (u (x ⊓ y) = true) ↔ (u x = true ∧ u y = true)
  rw [hu.2.2.1 x y, Bool.and_eq_true]

theorem stoneMap_sup (x y : B) :
    stoneMap B (x ⊔ y) = stoneMap B x ∪ stoneMap B y := by
  ext ⟨u, hu⟩
  change (u (x ⊔ y) = true) ↔ (u x = true ∨ u y = true)
  rw [hu.2.2.2.1 x y, Bool.or_eq_true]

theorem stoneMap_compl (x : B) :
    stoneMap B (xᶜ) = (stoneMap B x)ᶜ := by
  ext ⟨u, hu⟩
  change (u (xᶜ) = true) ↔ ¬(u x = true)
  rw [hu.2.2.2.2 x]
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

/-!
### Concrete Numerical Example: B = 𝒫({0, 1}) ≅ (Fin 2 → Bool)
-/

abbrev TwoAlgebra := Fin 2 → Bool

def u0_fun : TwoAlgebra → Bool := fun s => s 0
def u1_fun : TwoAlgebra → Bool := fun s => s 1

theorem u0_isHom : isHom TwoAlgebra u0_fun :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem u1_isHom : isHom TwoAlgebra u1_fun :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

def u0 : StoneSpace TwoAlgebra := ⟨u0_fun, u0_isHom⟩
def u1 : StoneSpace TwoAlgebra := ⟨u1_fun, u1_isHom⟩

def elem_bot  : TwoAlgebra := fun _ => false
def elem_zero : TwoAlgebra := fun i => (i == 0)
def elem_one  : TwoAlgebra := fun i => (i == 1)
def elem_top  : TwoAlgebra := fun _ => true

-- Verifications of the Stone map on the 4 elements of the Boolean algebra
theorem example_bot : stoneMap TwoAlgebra elem_bot = ∅ :=
  stoneMap_bot TwoAlgebra

theorem example_top : stoneMap TwoAlgebra elem_top = univ :=
  stoneMap_top TwoAlgebra

theorem example_u0_in_zero : u0 ∈ stoneMap TwoAlgebra elem_zero := rfl

theorem example_u1_not_in_zero : u1 ∉ stoneMap TwoAlgebra elem_zero := by
  intro h; cases h

theorem example_u1_in_one : u1 ∈ stoneMap TwoAlgebra elem_one := rfl

theorem example_u0_not_in_one : u0 ∉ stoneMap TwoAlgebra elem_one := by
  intro h; cases h

end StoneRepresentation


end Course21651
