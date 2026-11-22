/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Tree.LocallyFinite.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Countable

/-!
# Finite Ulam--Harris trees

A tree is finite when its carrier is a finite set. Finite trees are locally
finite: the children of a node form a subset of the carrier under the
injective map `i ↦ u ++ [i]`.

The type `FiniteTree α` is the subtype of `Tree α` consisting of finite trees.
Its topology, measurable structure, and metric are in `Tree/Finite/Space.lean`.

## Public declarations

- `Tree.finiteTree_countable`: finite rooted trees over a countable
  child-label type form a countable type, by their finite address carriers.

- `Tree.IsFinite T` is `\(T.carrier.Finite\)`, and
  `Tree.FiniteTree α := \{T : Tree\ α \mid T.carrier.Finite\}`.
  `Tree.isFinite_iff` states this equivalence, and
  `Tree.IsFinite.isLocallyFinite` proves `\(T.IsFinite\to T.IsLocallyFinite\)`.
- `Tree.toLocallyFinite α` is the subtype inclusion and
  `Tree.toLocallyFinite_injective` states
  `\(\operatorname{Injective}(Tree.toLocallyFinite\ \alpha)\)`.
-/

@[expose] public section

namespace Combinatorics

namespace UlamHarris

namespace Tree

variable {α : Type*} [LT α]

/-- A tree is finite when its carrier is a finite set. -/
def IsFinite (T : Tree α) : Prop :=
  T.carrier.Finite

/-- The type of finite trees. -/
abbrev FiniteTree (α : Type*) [LT α] :=
  {T : Tree α // T.IsFinite}

theorem isFinite_iff (T : Tree α) :
    T.IsFinite ↔ T.carrier.Finite :=
  Iff.rfl

/-- Every finite tree is locally finite. -/
theorem IsFinite.isLocallyFinite {T : Tree α} (h : T.IsFinite) :
    T.IsLocallyFinite := by
  intro u
  exact h.preimage fun a _ b _ hab => by
    have h' : [a] = [b] := List.append_right_injective u hab
    simpa using h'

/-- Inclusion of finite trees into locally finite trees. -/
def toLocallyFinite (α : Type*) [LT α] (T : FiniteTree α) : LocallyFiniteTree α :=
  ⟨T.1, T.2.isLocallyFinite⟩

theorem toLocallyFinite_injective (α : Type*) [LT α] :
    Function.Injective (toLocallyFinite α) := by
  intro T S h
  apply Subtype.ext
  exact congrArg (fun X : LocallyFiniteTree α => X.1) h

/-- The set of finite trees over countably many labels is countable. -/
theorem finiteTree_countable [Countable α] : Countable (FiniteTree α) := by
  have : Countable {s : Set (List α) // s.Finite} :=
    Set.countable_coe_iff.mpr Set.Countable.ofPred_finite
  apply Function.Injective.countable (f := fun T : FiniteTree α ↦
    (⟨T.1.carrier, T.2⟩ : {s : Set (List α) // s.Finite}))
  intro T S h
  apply Subtype.ext
  exact Tree.ext (congrArg Subtype.val h)

end Tree

end UlamHarris

end Combinatorics

end
