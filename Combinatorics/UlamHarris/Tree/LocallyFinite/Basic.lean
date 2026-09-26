import Combinatorics.UlamHarris.Tree.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Locally finite Ulam--Harris trees

A tree is locally finite if every node has only finitely many children. The
child set at an address `u` is `{i | u ++ [i] ∈ T.carrier}`; for addresses not
in the tree this set is empty, so the definition below does not need to assume
`u ∈ T.carrier`.

The type `LocallyFiniteTree α` is the subtype of `Tree α` consisting of the
locally finite trees. Its topology, measurable structure, and metric are in
`Tree/LocallyFinite/Space.lean`.
-/

open MeasureTheory

namespace Combinatorics

namespace UlamHarris

namespace Tree

variable {α : Type*} [LT α]

/-- A tree is locally finite when every node has finitely many children. -/
def IsLocallyFinite (T : Tree α) : Prop :=
  ∀ u : TreeNode α, {i : α | u ++ [i] ∈ T.carrier}.Finite

/-- The type of locally finite trees. -/
abbrev LocallyFiniteTree (α : Type*) [LT α] :=
  {T : Tree α // T.IsLocallyFinite}

theorem isLocallyFinite_iff (T : Tree α) :
    T.IsLocallyFinite ↔
      ∀ u : TreeNode α, {i : α | u ++ [i] ∈ T.carrier}.Finite :=
  Iff.rfl

theorem children_finite (T : LocallyFiniteTree α) (u : TreeNode α) :
    {i : α | u ++ [i] ∈ T.1.carrier}.Finite :=
  T.2 u

end Tree

end UlamHarris

end Combinatorics
