/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Basic.Real.Basic

/-!
# Challenge — Course 21-321

Helpers live in a closed `section` so `SeparatingFunctional.noCancellation` gets
the same universe parameter name (`u_1`) as in `Theorem11.lean`.
-/

namespace Course21321

section ScottPairHelpers

variable {K V : Type*}

/-- Finite pair of vectors in a `K`-module: the data of Scott's homogeneous
linear-inequality problem. -/
structure ScottPair (K : Type*) (V : Type*)
    [Semiring K] [AddCommGroup V] [Module K V] where
  X : Finset V
  Y : Finset V

/-- A linear functional that is nonnegative on `X` and strictly positive on `Y`.
This is the witness-carrying enrichment of a `ScottPair`. -/
structure SeparatingFunctional (K : Type*) (V : Type*)
    [Ring K] [LinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup V] [Module K V]
    extends ScottPair K V where
  f : V →ₗ[K] K
  nonneg_X : ∀ x ∈ X, 0 ≤ f x
  pos_Y : ∀ y ∈ Y, 0 < f y

/-- Existence of a separator: a property of an existing `ScottPair`. -/
class Separable [Ring K] [LinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup V] [Module K V] (P : ScottPair K V) : Prop where
  exists_sep : ∃ f : V →ₗ[K] K, (∀ x ∈ P.X, 0 ≤ f x) ∧ (∀ y ∈ P.Y, 0 < f y)

instance [Ring K] [LinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup V] [Module K V]
    (P : SeparatingFunctional K V) : Separable P.toScottPair where
  exists_sep := ⟨P.f, P.nonneg_X, P.pos_Y⟩

/-- Real (or ordered-scalar) non-cancellation: no nontrivial nonnegative
combination of the pair sums to zero. -/
class NoCancellation [Ring K] [LinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup V] [Module K V] (P : ScottPair K V) : Prop where
  no_cancel : ∀ (c d : V → K),
    (∀ x ∈ P.X, 0 ≤ c x) →
    (∀ y ∈ P.Y, 0 ≤ d y) →
    (0 < ∑ y ∈ P.Y, d y) →
    (∑ x ∈ P.X, c x • x) + (∑ y ∈ P.Y, d y • y) ≠ 0

/-- An explicit nonnegative combination that sums to zero with positive mass
on `Y`. This is a property of a `ScottPair`, dual to `NoCancellation`. -/
class CancellationWitness [Ring K] [LinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup V] [Module K V] (P : ScottPair K V) where
  c : V → K
  d : V → K
  c_nonneg : ∀ x ∈ P.X, 0 ≤ c x
  d_nonneg : ∀ y ∈ P.Y, 0 ≤ d y
  d_mass : 0 < ∑ y ∈ P.Y, d y
  sum_zero : (∑ x ∈ P.X, c x • x) + (∑ y ∈ P.Y, d y • y) = 0

end ScottPairHelpers

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Witness form: a separating functional yields non-cancellation. -/
theorem SeparatingFunctional.noCancellation [DecidableEq V]
    (P : SeparatingFunctional ℝ V) : NoCancellation P.toScottPair := by
  sorry

noncomputable section

/-- Kraft–Pratt–Seidenberg difference vectors in `ℝ⁵`. These are data, not a
new class: they assemble into a particular `ScottPair` below. -/
def y1 : Fin 5 → ℝ := ![-1, -1, 1, 1, 0]
def y2 : Fin 5 → ℝ := ![-1, 1, -1, 0, 1]
def y3 : Fin 5 → ℝ := ![1, -1, -1, 1, 0]
def y4 : Fin 5 → ℝ := ![1, 1, 1, -2, -1]

/-- A concrete Scott pair — an inhabitant, like a particular monoid, not a
new typeclass. -/
def KraftPair : ScottPair ℝ (Fin 5 → ℝ) where
  X := ∅
  Y := {y1, y2, y3, y4}

theorem KraftPair.not_separable : ¬ Separable KraftPair := by
  sorry

end

end Course21321
