module

public import Combinatorics.UlamHarris.Tree.LocallyFinite.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finite Ulam--Harris trees

A tree is finite when its carrier is a finite set. Finite trees are locally
finite: the children of a node form a subset of the carrier under the
injective map `i ↦ u ++ [i]`.

The type `FiniteTree α` is the subtype of `Tree α` consisting of finite trees.
Its topology, measurable structure, and metric are in `Tree/Finite/Space.lean`.
-/

@[expose] public section

open MeasureTheory

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

end Tree

end UlamHarris

end Combinatorics

end
