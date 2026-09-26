import MeasureTheory.BranchingWalk.Basic
import MeasureTheory.BranchingWalk.Step.Ordered.Basic
import MeasureTheory.BranchingWalk.Relation.Field

/-!
# Standard branching walks

`IsOrdered ω` says the present marks increase along the slot order
(`parentOrdered`) at every address: the thesis's left-to-right enumeration.
Combined with the parent-closure `IsParentClosed` of `Relation/Field.lean` it
gives the field-level object `StandardBranchingWalk α X`, the subtype of fields
satisfying both.

`toBranchingWalk` forgets the condition, and
`StandardBranchingWalk.toParentClosedBranchingWalk` forgets only the mark
order; the two commute.
-/

namespace MeasureTheory

namespace BranchingWalk

open MeasureTheory.UlamHarris

/-- The present marks of every step increase along the slot order. -/
abbrev IsOrdered {α X : Type*} [LT α] [LE X] (ω : StepField α X) : Prop :=
  ∀ u, parentOrdered (ω u)

/-- A branching walk with ordered, parent-closed children: the thesis's
standard branching walk. -/
abbrev StandardBranchingWalk (α X : Type*) [LT α] [LE X] :=
  {ω : StepField α X // IsOrdered ω ∧ IsParentClosed ω}

namespace StandardBranchingWalk

variable {α X : Type*} [LT α] [LE X]

instance instCoeFun : CoeFun (StandardBranchingWalk α X)
    (fun _ => TreeNode α → Step α X) :=
  ⟨Subtype.val⟩

/-- The primitive field underlying a standard walk. -/
def toBranchingWalk (ω : StandardBranchingWalk α X) : StepField α X := ω.1

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
