import MeasureTheory.BranchingWalk.Basic
import MeasureTheory.BranchingWalk.Relation.Basic

/-!
# Parent-closed branching walks

`IsParentClosed β` says every step of the field has its present slots forming
an initial segment (`presenceParent`). This is exactly the condition under
which the realized addresses of `β` form a `Tree`, so the realized tree and the
marked tree are defined under it. `ParentClosedBranchingWalk` is the subtype of
fields satisfying it, and `StandardBranchingWalk` the subtype satisfying both
`IsOrdered` and `IsParentClosed`.
-/

namespace MeasureTheory

namespace BranchingWalk

open MeasureTheory.UlamHarris

/-- Every step lists its present slots from the left; equivalently the
realized addresses are sibling closed and form a tree. -/
abbrev IsParentClosed {α X : Type*} [LT α] (β : StepField α X) : Prop :=
  ∀ u, presenceParent (β u)

/-- A branching walk whose present slots form an initial segment at every
address: the realized addresses form a tree. -/
abbrev ParentClosedBranchingWalk (α X : Type*) [LT α] :=
  {β : StepField α X // IsParentClosed β}

namespace ParentClosedBranchingWalk

variable {α X : Type*} [LT α]

instance instCoeFun : CoeFun (ParentClosedBranchingWalk α X)
    (fun _ => TreeNode α → Step α X) :=
  ⟨Subtype.val⟩

/-- The primitive field underlying a parent-closed walk. -/
def toBranchingWalk (β : ParentClosedBranchingWalk α X) : StepField α X := β.1

@[simp] theorem toBranchingWalk_apply (β : ParentClosedBranchingWalk α X)
    (u : TreeNode α) : toBranchingWalk β u = β.1 u := rfl

/-- The parent-closure property, at a fixed address. -/
theorem isParentClosed_apply (β : ParentClosedBranchingWalk α X) (u : TreeNode α) :
    presenceParent (toBranchingWalk β u) := β.2 u

end ParentClosedBranchingWalk

/-- A branching walk with ordered, parent-closed children: the thesis's
standard branching walk. -/
abbrev StandardBranchingWalk (α X : Type*) [LT α] [LE X] :=
  {β : StepField α X // IsOrdered β ∧ IsParentClosed β}

namespace StandardBranchingWalk

variable {α X : Type*} [LT α] [LE X]

instance instCoeFun : CoeFun (StandardBranchingWalk α X)
    (fun _ => TreeNode α → Step α X) :=
  ⟨Subtype.val⟩

/-- The primitive field underlying a standard walk. -/
def toBranchingWalk (β : StandardBranchingWalk α X) : StepField α X := β.1

@[simp] theorem toBranchingWalk_apply (β : StandardBranchingWalk α X)
    (u : TreeNode α) : toBranchingWalk β u = β.1 u := rfl

/-- Forget the mark order of a standard walk, keeping parent closure. -/
def toParentClosedBranchingWalk (β : StandardBranchingWalk α X) :
    ParentClosedBranchingWalk α X :=
  ⟨β.1, β.2.2⟩

@[simp] theorem toBranchingWalk_toParentClosedBranchingWalk (β : StandardBranchingWalk α X) :
    (β.toParentClosedBranchingWalk).toBranchingWalk = β.toBranchingWalk := rfl

/-- The order property, at a fixed address. -/
theorem isOrdered_apply (β : StandardBranchingWalk α X) (u : TreeNode α) :
    markOrdered (toBranchingWalk β u) := β.2.1 u

end StandardBranchingWalk

end BranchingWalk

end MeasureTheory
