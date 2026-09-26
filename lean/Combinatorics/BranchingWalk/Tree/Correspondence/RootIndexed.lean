import Combinatorics.BranchingWalk.Tree.Correspondence.Equiv
import Combinatorics.UlamHarris.RootIndexedMarkedTree.Basic

/-!
# Root-indexed step fields and root-indexed marked trees

The paper samples one branching step field per initial ancestor, so the field
objects are indexed families. This file lifts the single-root correspondence of
`Correspondence/Equiv.lean` to families: `RootIndexedParentClosedBranchingWalk` is one
ordered field per root, `RootIndexedMarkedTree` is one marked tree per root, and
`rootIndexedRealizedParentClosedBranchingWalkEquivMarkedTree` is the bijection between
the normalized fields and the marked families whose every tree has vanishing
root mark and increasing sibling marks.

The projections `toRootIndexedBranchingWalk` and
`toRootIndexedParentClosedBranchingWalk` forget the order condition at every root.
For `α = ℕ` the codomain `RootIndexedStepField Root ℕ X` is the field of
`Probability/BranchingRandomWalk/Genealogy/RootIndexed/Field.lean`, whose
`RootIndexedStepField` is the Ulam--Harris case of this one.
-/

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris

variable {Root α X : Type*}

/-- A branching step field for every initial ancestor. -/
abbrev RootIndexedStepField (Root α X : Type*) :=
  Root → StepField α X

/-- A presence-closed step field for every initial ancestor. -/
abbrev RootIndexedParentClosedBranchingWalk (Root α X : Type*) [LT α] :=
  Root → ParentClosedBranchingWalk α X

/-- An ordered step field for every initial ancestor. -/
abbrev RootIndexedParentClosedBranchingWalk (Root α X : Type*) [LT α] [LE X] :=
  Root → ParentClosedBranchingWalk α X

/-- The ordered step fields of the root-indexed correspondence: ordered at every
root, and carrying no data below the realized tree of any root. -/
abbrev RootIndexedRealizedParentClosedBranchingWalk (Root α X : Type*) [LT α] [LE X] :=
  Root → RealizedParentClosedBranchingWalk α X

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
    RootIndexedStepField Root α X :=
  fun r => (step r).toBranchingWalk

@[simp] theorem toRootIndexedBranchingWalk_apply
    (step : RootIndexedParentClosedBranchingWalk Root α X) (r : Root) :
    step.toRootIndexedBranchingWalk r = (step r).toBranchingWalk := rfl

end RootIndexedParentClosedBranchingWalk

namespace RootIndexedParentClosedBranchingWalk

variable [LT α] [LE X]

/-- Forget the order condition of a root-indexed ordered field. -/
def toRootIndexedBranchingWalk (step : RootIndexedParentClosedBranchingWalk Root α X) :
    RootIndexedStepField Root α X :=
  fun r => (step r).toBranchingWalk

@[simp] theorem toRootIndexedBranchingWalk_apply
    (step : RootIndexedParentClosedBranchingWalk Root α X) (r : Root) :
    step.toRootIndexedBranchingWalk r = (step r).toBranchingWalk := rfl

/-- Forget only the mark order of a root-indexed ordered field. -/
def toRootIndexedParentClosedBranchingWalk
    (step : RootIndexedParentClosedBranchingWalk Root α X) :
    RootIndexedParentClosedBranchingWalk Root α X :=
  fun r => (step r).toParentClosedBranchingWalk

@[simp] theorem toRootIndexedParentClosedBranchingWalk_toRootIndexedBranchingWalk
    (step : RootIndexedParentClosedBranchingWalk Root α X) :
    RootIndexedParentClosedBranchingWalk.toRootIndexedBranchingWalk
        (RootIndexedParentClosedBranchingWalk.toRootIndexedParentClosedBranchingWalk step) =
      RootIndexedParentClosedBranchingWalk.toRootIndexedBranchingWalk step := rfl

end RootIndexedParentClosedBranchingWalk

section Bijection

variable [LT α] [AddCommGroup X] [PartialOrder X] [IsOrderedAddMonoid X]

/-- A root-indexed family of ordered step fields with no data below the realized
tree of every root is exactly a root-indexed marked family whose every tree has
vanishing root mark and increasing sibling marks: mark every realized node of
every tree by its displacement, and read the relative displacement of every
realized child off the trees. -/
noncomputable def rootIndexedRealizedParentClosedBranchingWalkEquivMarkedTree :
    RootIndexedRealizedParentClosedBranchingWalk Root α X ≃
      {M : RootIndexedMarkedTree Root α X // IsRootIndexedBranchingMarkedTree Root α X M} :=
  (Equiv.piCongrRight fun _ => realizedParentClosedBranchingWalkEquivMarkedTree).trans
    Equiv.subtypePiEquivPi.symm

@[simp] theorem rootIndexedRealizedParentClosedBranchingWalkEquivMarkedTree_apply
    (step : RootIndexedRealizedParentClosedBranchingWalk Root α X) (r : Root) :
    (rootIndexedRealizedParentClosedBranchingWalkEquivMarkedTree step).1 r =
      (realizedParentClosedBranchingWalkEquivMarkedTree (step r)).1 := rfl

end Bijection

end Branching

end Combinatorics
