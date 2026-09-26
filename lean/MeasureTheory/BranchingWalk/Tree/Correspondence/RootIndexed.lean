import MeasureTheory.BranchingWalk.Tree.Correspondence.Equiv
import MeasureTheory.UlamHarris.RootIndexedMarkedTree.Basic

/-!
# Root-indexed step fields and root-indexed marked trees

The paper samples one branching step field per initial ancestor, so the field
objects are indexed families. This file lifts the single-root correspondence of
`Correspondence/Equiv.lean` to families: `RootIndexedOrderedStepField` is one
ordered field per root, `RootIndexedMarkedTree` is one marked tree per root, and
`rootIndexedRealizedOrderedStepFieldEquivMarkedTree` is the bijection between
the normalized fields and the marked families whose every tree has vanishing
root mark and increasing sibling marks.

The projections `toRootIndexedStepField` and
`toRootIndexedPresenceClosedStepField` forget the order condition at every root.
For `α = ℕ` the codomain `RootIndexedStepField Root ℕ X` is the field of
`Probability/BranchingRandomWalk/Genealogy/RootIndexed/Field.lean`, whose
`RootIndexedStepField` is the Ulam--Harris case of this one.
-/

namespace MeasureTheory

namespace BranchingWalk

open MeasureTheory.UlamHarris

variable {Root α X : Type*}

/-- A branching step field for every initial ancestor. -/
abbrev RootIndexedStepField (Root α X : Type*) :=
  Root → StepField α X

/-- A presence-closed step field for every initial ancestor. -/
abbrev RootIndexedPresenceClosedStepField (Root α X : Type*) [LT α] :=
  Root → PresenceClosedStepField α X

/-- An ordered step field for every initial ancestor. -/
abbrev RootIndexedOrderedStepField (Root α X : Type*) [LT α] [LE X] :=
  Root → OrderedStepField α X

/-- The ordered step fields of the root-indexed correspondence: ordered at every
root, and carrying no data below the realized tree of any root. -/
abbrev RootIndexedRealizedOrderedStepField (Root α X : Type*) [LT α] [LE X] :=
  Root → RealizedOrderedStepField α X

/-- The condition on a root-indexed marked family that makes it the marked tree
of an ordered step field: every tree has vanishing root mark and increasing
sibling marks. -/
abbrev IsRootIndexedBranchingMarkedTree (Root α X : Type*) [LT α] [LE X] [Zero X]
    (M : RootIndexedMarkedTree Root α X) : Prop :=
  ∀ r, IsBranchingMarkedTree (M r)

namespace RootIndexedPresenceClosedStepField

variable [LT α]

/-- Forget the presence closure of a root-indexed family at every root. -/
def toRootIndexedStepField
    (step : RootIndexedPresenceClosedStepField Root α X) :
    RootIndexedStepField Root α X :=
  fun r => (step r).toStepField

@[simp] theorem toRootIndexedStepField_apply
    (step : RootIndexedPresenceClosedStepField Root α X) (r : Root) :
    step.toRootIndexedStepField r = (step r).toStepField := rfl

end RootIndexedPresenceClosedStepField

namespace RootIndexedOrderedStepField

variable [LT α] [LE X]

/-- Forget the order condition of a root-indexed ordered field. -/
def toRootIndexedStepField (step : RootIndexedOrderedStepField Root α X) :
    RootIndexedStepField Root α X :=
  fun r => (step r).toStepField

@[simp] theorem toRootIndexedStepField_apply
    (step : RootIndexedOrderedStepField Root α X) (r : Root) :
    step.toRootIndexedStepField r = (step r).toStepField := rfl

/-- Forget only the mark order of a root-indexed ordered field. -/
def toRootIndexedPresenceClosedStepField
    (step : RootIndexedOrderedStepField Root α X) :
    RootIndexedPresenceClosedStepField Root α X :=
  fun r => (step r).toPresenceClosedStepField

@[simp] theorem toRootIndexedPresenceClosedStepField_toRootIndexedStepField
    (step : RootIndexedOrderedStepField Root α X) :
    RootIndexedPresenceClosedStepField.toRootIndexedStepField
        (RootIndexedOrderedStepField.toRootIndexedPresenceClosedStepField step) =
      RootIndexedOrderedStepField.toRootIndexedStepField step := rfl

end RootIndexedOrderedStepField

section Bijection

variable [LT α] [AddCommGroup X] [PartialOrder X] [IsOrderedAddMonoid X]

/-- A root-indexed family of ordered step fields with no data below the realized
tree of every root is exactly a root-indexed marked family whose every tree has
vanishing root mark and increasing sibling marks: mark every realized node of
every tree by its displacement, and read the relative displacement of every
realized child off the trees. -/
noncomputable def rootIndexedRealizedOrderedStepFieldEquivMarkedTree :
    RootIndexedRealizedOrderedStepField Root α X ≃
      {M : RootIndexedMarkedTree Root α X // IsRootIndexedBranchingMarkedTree Root α X M} :=
  (Equiv.piCongrRight fun _ => realizedOrderedStepFieldEquivMarkedTree).trans
    Equiv.subtypePiEquivPi.symm

@[simp] theorem rootIndexedRealizedOrderedStepFieldEquivMarkedTree_apply
    (step : RootIndexedRealizedOrderedStepField Root α X) (r : Root) :
    (rootIndexedRealizedOrderedStepFieldEquivMarkedTree step).1 r =
      (realizedOrderedStepFieldEquivMarkedTree (step r)).1 := rfl

end Bijection

end BranchingWalk

end MeasureTheory
