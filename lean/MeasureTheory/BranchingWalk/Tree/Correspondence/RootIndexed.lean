import MeasureTheory.BranchingWalk.Tree.Correspondence.Equiv
import MeasureTheory.UlamHarris.RootIndexedMarkedTree.Basic

/-!
# Root-indexed step fields and root-indexed marked trees

The paper samples one branching step field per initial ancestor, so the field
objects are indexed families. This file lifts the single-root correspondence of
`Correspondence/Equiv.lean` to families: `RootIndexedStandardBranchingWalk` is one
ordered field per root, `RootIndexedMarkedTree` is one marked tree per root, and
`rootIndexedRealizedStandardBranchingWalkEquivMarkedTree` is the bijection between
the normalized fields and the marked families whose every tree has vanishing
root mark and increasing sibling marks.

The projections `toRootIndexedBranchingWalk` and
`toRootIndexedParentClosedBranchingWalk` forget the order condition at every root.
For `α = ℕ` the codomain `RootIndexedBranchingWalk Root ℕ X` is the field of
`Probability/BranchingRandomWalk/Genealogy/RootIndexed/Field.lean`, whose
`RootIndexedBranchingWalk` is the Ulam--Harris case of this one.
-/

namespace MeasureTheory

namespace BranchingWalk

open MeasureTheory.UlamHarris

variable {Root α X : Type*}

/-- A branching step field for every initial ancestor. -/
abbrev RootIndexedBranchingWalk (Root α X : Type*) :=
  Root → BranchingWalk α X

/-- A presence-closed step field for every initial ancestor. -/
abbrev RootIndexedParentClosedBranchingWalk (Root α X : Type*) [LT α] :=
  Root → ParentClosedBranchingWalk α X

/-- An ordered step field for every initial ancestor. -/
abbrev RootIndexedStandardBranchingWalk (Root α X : Type*) [LT α] [LE X] :=
  Root → StandardBranchingWalk α X

/-- The ordered step fields of the root-indexed correspondence: ordered at every
root, and carrying no data below the realized tree of any root. -/
abbrev RootIndexedRealizedStandardBranchingWalk (Root α X : Type*) [LT α] [LE X] :=
  Root → RealizedStandardBranchingWalk α X

/-- The condition on a root-indexed marked family that makes it the marked tree
of an ordered step field: every tree has vanishing root mark and increasing
sibling marks. -/
abbrev IsRootIndexedBranchingMarkedTree (Root α X : Type*) [LT α] [LE X] [Zero X]
    (M : RootIndexedMarkedTree Root α X) : Prop :=
  ∀ r, IsBranchingMarkedTree (M r)

namespace RootIndexedParentClosedBranchingWalk

variable [LT α]

/-- Forget the presence closure of a root-indexed family at every root. -/
def toRootIndexedBranchingWalk
    (step : RootIndexedParentClosedBranchingWalk Root α X) :
    RootIndexedBranchingWalk Root α X :=
  fun r => (step r).toBranchingWalk

@[simp] theorem toRootIndexedBranchingWalk_apply
    (step : RootIndexedParentClosedBranchingWalk Root α X) (r : Root) :
    step.toRootIndexedBranchingWalk r = (step r).toBranchingWalk := rfl

end RootIndexedParentClosedBranchingWalk

namespace RootIndexedStandardBranchingWalk

variable [LT α] [LE X]

/-- Forget the order condition of a root-indexed ordered field. -/
def toRootIndexedBranchingWalk (step : RootIndexedStandardBranchingWalk Root α X) :
    RootIndexedBranchingWalk Root α X :=
  fun r => (step r).toBranchingWalk

@[simp] theorem toRootIndexedBranchingWalk_apply
    (step : RootIndexedStandardBranchingWalk Root α X) (r : Root) :
    step.toRootIndexedBranchingWalk r = (step r).toBranchingWalk := rfl

/-- Forget only the mark order of a root-indexed ordered field. -/
def toRootIndexedParentClosedBranchingWalk
    (step : RootIndexedStandardBranchingWalk Root α X) :
    RootIndexedParentClosedBranchingWalk Root α X :=
  fun r => (step r).toParentClosedBranchingWalk

@[simp] theorem toRootIndexedParentClosedBranchingWalk_toRootIndexedBranchingWalk
    (step : RootIndexedStandardBranchingWalk Root α X) :
    RootIndexedParentClosedBranchingWalk.toRootIndexedBranchingWalk
        (RootIndexedStandardBranchingWalk.toRootIndexedParentClosedBranchingWalk step) =
      RootIndexedStandardBranchingWalk.toRootIndexedBranchingWalk step := rfl

end RootIndexedStandardBranchingWalk

section Bijection

variable [LT α] [AddCommGroup X] [PartialOrder X] [IsOrderedAddMonoid X]

/-- A root-indexed family of ordered step fields with no data below the realized
tree of every root is exactly a root-indexed marked family whose every tree has
vanishing root mark and increasing sibling marks: mark every realized node of
every tree by its displacement, and read the relative displacement of every
realized child off the trees. -/
noncomputable def rootIndexedRealizedStandardBranchingWalkEquivMarkedTree :
    RootIndexedRealizedStandardBranchingWalk Root α X ≃
      {M : RootIndexedMarkedTree Root α X // IsRootIndexedBranchingMarkedTree Root α X M} :=
  (Equiv.piCongrRight fun _ => realizedStandardBranchingWalkEquivMarkedTree).trans
    Equiv.subtypePiEquivPi.symm

@[simp] theorem rootIndexedRealizedStandardBranchingWalkEquivMarkedTree_apply
    (step : RootIndexedRealizedStandardBranchingWalk Root α X) (r : Root) :
    (rootIndexedRealizedStandardBranchingWalkEquivMarkedTree step).1 r =
      (realizedStandardBranchingWalkEquivMarkedTree (step r)).1 := rfl

end Bijection

end BranchingWalk

end MeasureTheory
