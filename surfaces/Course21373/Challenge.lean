/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.BooleanAlgebra.Basic

open Finset
open Classical

/-!
# Challenge — Course 21-373
-/

namespace Course21373

/-- An atom in a Boolean algebra is a non-bottom element whose only sub-elements are ⊥ and itself. -/
class IsBooleanAtom {B : Type*} [BooleanAlgebra B] (a : B) : Prop where
  ne_bot : a ≠ ⊥
  le_bot_or_self : ∀ x, x ≤ a → x = ⊥ ∨ x = a

variable {B : Type*} [BooleanAlgebra B]

/-- The canonical map sending an element to the atoms below it. -/
noncomputable def repMap (A : Finset B) (x : B) : Finset B :=
  A.filter (fun a => a ≤ x)

/-- `repMap` is the inverse of `Finset.sup id` on subsets of atoms. -/
theorem repMap_sup_id {A : Finset B} (hA : ∀ a ∈ A, IsBooleanAtom a) {s : Finset B} (hs : s ⊆ A) :
    repMap A (s.sup id) = s := by
  sorry

end Course21373
