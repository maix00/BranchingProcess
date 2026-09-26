import MeasureTheory.BranchingWalk.Step.Field
import MeasureTheory.BranchingWalk.Step.Ordered.Basic

/-!
# Step fields with ordered children

`StepField α X = TreeNode α → Step α X` is the primitive field, and at any
address a field may list an absent slot before a present one. This file isolates
the two conditions under which a field is the field of a tree:

* `PresenceClosedStepField α X` requires every step to have its present slots
  forming an initial segment (`presenceParent`). This is exactly the condition
  under which the realized addresses of the field form a `Tree`, so the realized
  tree and the marked tree are defined on this subtype.
* `OrderedStepField α X` additionally requires the present marks to increase
  along the slot order (`parentOrdered`). This is the thesis's left-to-right
  enumeration of the children.

Both are subtypes of the primitive field. `toStepField` forgets the condition,
and `OrderedStepField.toPresenceClosedStepField` forgets only the mark order;
the two commute. These projections are the field-level connection layer:
results about realized trees and marked trees are stated on the subtypes, and
the projections record which hypothesis a primitive field has to satisfy.
-/

namespace MeasureTheory

namespace BranchingWalk

open MeasureTheory.UlamHarris

/-- A step field in which every step lists its present slots from the left. The
realized addresses of such a field are sibling closed, so they form a tree. -/
abbrev PresenceClosedStepField (α X : Type*) [LT α] :=
  {step : StepField α X // ∀ u, presenceParent (step u)}

/-- A presence-closed step field whose present marks increase along the slot
order: the thesis's ordered enumeration of the children of every node. -/
abbrev OrderedStepField (α X : Type*) [LT α] [LE X] :=
  {step : StepField α X // ∀ u, OrderedStep (step u)}

namespace PresenceClosedStepField

variable {α X : Type*} [LT α]

instance instCoeFun : CoeFun (PresenceClosedStepField α X)
    (fun _ => TreeNode α → Step α X) :=
  ⟨Subtype.val⟩

/-- The primitive field underlying a presence-closed field. -/
def toStepField (step : PresenceClosedStepField α X) : StepField α X := step.1

@[simp] theorem toStepField_apply (step : PresenceClosedStepField α X)
    (u : TreeNode α) : toStepField step u = step.1 u := rfl

end PresenceClosedStepField

namespace OrderedStepField

variable {α X : Type*} [LT α] [LE X]

instance instCoeFun : CoeFun (OrderedStepField α X)
    (fun _ => TreeNode α → Step α X) :=
  ⟨Subtype.val⟩

/-- The primitive field underlying an ordered field. -/
def toStepField (step : OrderedStepField α X) : StepField α X := step.1

@[simp] theorem toStepField_apply (step : OrderedStepField α X) (u : TreeNode α) :
    toStepField step u = step.1 u := rfl

/-- Forget the mark order of an ordered field, keeping presence closure. -/
def toPresenceClosedStepField (step : OrderedStepField α X) :
    PresenceClosedStepField α X :=
  ⟨step.1, fun u => (step.2 u).1⟩

@[simp] theorem toStepField_toPresenceClosedStepField (step : OrderedStepField α X) :
    (step.toPresenceClosedStepField).toStepField = step.toStepField := rfl

end OrderedStepField

end BranchingWalk

end MeasureTheory
