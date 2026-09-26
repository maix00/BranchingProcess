import MeasureTheory.BranchingWalk.Step.Field
import MeasureTheory.BranchingWalk.Step.Ordered.Basic

/-!
# Standard branching walks

`BranchingWalk α X = TreeNode α → Step α X` is the primitive field, and at any
address a field may list an absent slot before a present one. This file lifts
the two slot-level conditions to properties of a whole field and packages the
field-level objects of the thesis:

* `IsParentClosed ω` says every step has its present slots forming an initial
  segment (`presenceParent`). This is exactly the condition under which the
  realized addresses of `ω` form a `Tree`, so the realized tree and the marked
  tree are defined under it.
* `IsOrdered ω` says the present marks increase along the slot order
  (`parentOrdered`) at every address: the thesis's left-to-right enumeration.
* `ParentClosedBranchingWalk α X` is the subtype of fields satisfying only
  `IsParentClosed`.
* `StandardBranchingWalk α X` is the subtype satisfying both `IsOrdered` and
  `IsParentClosed`.

`toBranchingWalk` forgets the condition, and
`StandardBranchingWalk.toParentClosedBranchingWalk` forgets only the mark
order; the two commute. These projections are the field-level connection
layer: results about realized trees and marked trees are stated on the
subtypes, and the projections record which hypothesis a primitive field has to
satisfy.
-/

namespace MeasureTheory

namespace BranchingWalk

open MeasureTheory.UlamHarris

/-- The present marks of every step increase along the slot order. -/
abbrev IsOrdered {α X : Type*} [LT α] [LE X] (ω : BranchingWalk α X) : Prop :=
  ∀ u, parentOrdered (ω u)

/-- Every step lists its present slots from the left; equivalently the
realized addresses are sibling closed and form a tree. -/
abbrev IsParentClosed {α X : Type*} [LT α] (ω : BranchingWalk α X) : Prop :=
  ∀ u, presenceParent (ω u)

/-- A branching walk whose present slots form an initial segment at every
address: the realized addresses form a tree. -/
abbrev ParentClosedBranchingWalk (α X : Type*) [LT α] :=
  {ω : BranchingWalk α X // IsParentClosed ω}

/-- A branching walk with ordered, parent-closed children: the thesis's
standard branching walk. -/
abbrev StandardBranchingWalk (α X : Type*) [LT α] [LE X] :=
  {ω : BranchingWalk α X // IsOrdered ω ∧ IsParentClosed ω}

namespace ParentClosedBranchingWalk

variable {α X : Type*} [LT α]

instance instCoeFun : CoeFun (ParentClosedBranchingWalk α X)
    (fun _ => TreeNode α → Step α X) :=
  ⟨Subtype.val⟩

/-- The primitive field underlying a parent-closed walk. -/
def toBranchingWalk (ω : ParentClosedBranchingWalk α X) : BranchingWalk α X := ω.1

@[simp] theorem toBranchingWalk_apply (ω : ParentClosedBranchingWalk α X)
    (u : TreeNode α) : toBranchingWalk ω u = ω.1 u := rfl

/-- The parent-closure property, at a fixed address. -/
theorem isParentClosed_apply (ω : ParentClosedBranchingWalk α X) (u : TreeNode α) :
    presenceParent (toBranchingWalk ω u) := ω.2 u

end ParentClosedBranchingWalk

namespace StandardBranchingWalk

variable {α X : Type*} [LT α] [LE X]

instance instCoeFun : CoeFun (StandardBranchingWalk α X)
    (fun _ => TreeNode α → Step α X) :=
  ⟨Subtype.val⟩

/-- The primitive field underlying a standard walk. -/
def toBranchingWalk (ω : StandardBranchingWalk α X) : BranchingWalk α X := ω.1

@[simp] theorem toBranchingWalk_apply (ω : StandardBranchingWalk α X)
    (u : TreeNode α) : toBranchingWalk ω u = ω.1 u := rfl

/-- Forget the mark order of a standard walk, keeping parent closure. -/
def toParentClosedBranchingWalk (ω : StandardBranchingWalk α X) :
    ParentClosedBranchingWalk α X :=
  ⟨ω.1, ω.2.2⟩

@[simp] theorem toBranchingWalk_toParentClosedBranchingWalk (ω : StandardBranchingWalk α X) :
    (ω.toParentClosedBranchingWalk).toBranchingWalk = ω.toBranchingWalk := rfl

/-- The order property, at a fixed address. -/
theorem isOrdered_apply (ω : StandardBranchingWalk α X) (u : TreeNode α) :
    parentOrdered (toBranchingWalk ω u) := ω.2.1 u

end StandardBranchingWalk

end BranchingWalk

end MeasureTheory
