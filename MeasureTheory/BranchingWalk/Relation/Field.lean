import MeasureTheory.BranchingWalk.Basic
import MeasureTheory.BranchingWalk.Relation.Basic

/-!
# Parent-closed branching walks

`IsParentClosed ω` says every step of the field has its present slots forming
an initial segment (`presenceParent`). This is exactly the condition under
which the realized addresses of `ω` form a `Tree`, so the realized tree and the
marked tree are defined under it. `ParentClosedBranchingWalk` is the subtype of
fields satisfying it.
-/

namespace MeasureTheory

namespace BranchingWalk

open MeasureTheory.UlamHarris

/-- Every step lists its present slots from the left; equivalently the
realized addresses are sibling closed and form a tree. -/
abbrev IsParentClosed {α X : Type*} [LT α] (ω : StepField α X) : Prop :=
  ∀ u, presenceParent (ω u)

/-- A branching walk whose present slots form an initial segment at every
address: the realized addresses form a tree. -/
abbrev ParentClosedBranchingWalk (α X : Type*) [LT α] :=
  {ω : StepField α X // IsParentClosed ω}

namespace ParentClosedBranchingWalk

variable {α X : Type*} [LT α]

instance instCoeFun : CoeFun (ParentClosedBranchingWalk α X)
    (fun _ => TreeNode α → Step α X) :=
  ⟨Subtype.val⟩

/-- The primitive field underlying a parent-closed walk. -/
def toBranchingWalk (ω : ParentClosedBranchingWalk α X) : StepField α X := ω.1

@[simp] theorem toBranchingWalk_apply (ω : ParentClosedBranchingWalk α X)
    (u : TreeNode α) : toBranchingWalk ω u = ω.1 u := rfl

/-- The parent-closure property, at a fixed address. -/
theorem isParentClosed_apply (ω : ParentClosedBranchingWalk α X) (u : TreeNode α) :
    presenceParent (toBranchingWalk ω u) := ω.2 u

end ParentClosedBranchingWalk

end BranchingWalk

end MeasureTheory
