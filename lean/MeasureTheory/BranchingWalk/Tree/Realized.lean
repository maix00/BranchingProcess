import MeasureTheory.BranchingWalk.Displace.Basic
import MeasureTheory.BranchingWalk.Step.Ordered.Field
import MeasureTheory.BranchingWalk.Relation.Field
import MeasureTheory.BranchingWalk.Tree.Realization
import MeasureTheory.UlamHarris.MarkedTree.Basic

/-!
# The realized tree of a presence-closed step field

`realizedTree step hordered` is the deterministic tree whose carrier
is exactly the realized addresses; the ordered-sibling axiom is exactly a
pointwise `presenceParent` condition on the field, so that is the hypothesis
under which a field is the field of a tree. `markedTree` then marks every
realized node by its displacement, which is the bridge from the step field to
the `MarkedTree` object of the paper.

The subtypes carry the condition: `ParentClosedBranchingWalk.toTree` and
`ParentClosedBranchingWalk.toMarkedTree` are the tree-valued readings of such a
field, and the ordered versions are their specializations. The converse
reading, from a marked tree back to a field, is in `Tree/Correspondence/`.
-/

namespace MeasureTheory

namespace BranchingWalk

open MeasureTheory.UlamHarris



/-- The deterministic tree realized by a step field whose present slots form an
initial segment at every address. -/
def realizedTree {α X : Type*} [LT α]
    (step : StepField α X)
    (hpresence : ∀ u, presenceParent (step u)) : UlamHarris.Tree α where
  carrier := {u | realizedNode step u}
  root_mem := realizedNode_nil step
  parent_closed := by
    intro u v huv
    change realizedNode step (u ++ v) at huv
    exact (realizedNode_append_iff step u v).1 huv |>.1
  sibling_closed := by
    intro u i j hj hij
    change realizedNode step (u ++ [j]) at hj
    rw [realizedNode_append_singleton_iff] at hj
    exact (realizedNode_append_singleton_iff step u i).2
      ⟨hj.1, present_of_later (step u) (hpresence u) hij hj.2⟩

@[simp] theorem realizedTree_carrier {α X : Type*} [LT α]
    (step : StepField α X)
    (hpresence : ∀ u, presenceParent (step u)) :
    (realizedTree step hpresence).carrier =
      {u | realizedNode step u} := rfl

@[simp] theorem mem_realizedTree_iff {α X : Type*} [LT α]
    (step : StepField α X)
    (hpresence : ∀ u, presenceParent (step u)) (u : TreeNode α) :
    u ∈ (realizedTree step hpresence).carrier ↔
      realizedNode step u := Iff.rfl

/-- The marked tree of a presence-closed step field: the realized addresses carry
their displacements. This is the bridge from the step field to the
tree-with-marks object; both the realized tree and the marks are derived from
the field. -/
def markedTree {α X : Type*} [AddCommMonoid X] [LT α]
    (step : StepField α X)
    (hpresence : ∀ u, presenceParent (step u)) : MarkedTree α X where
  tree := realizedTree step hpresence
  mark := fun u _ => displaceRoot step u

@[simp] theorem markedTree_tree {α X : Type*} [AddCommMonoid X]
    [LT α] (step : StepField α X)
    (hpresence : ∀ u, presenceParent (step u)) :
    (markedTree step hpresence).tree =
      realizedTree step hpresence := rfl

@[simp] theorem markedTree_mark {α X : Type*} [AddCommMonoid X]
    [LT α] (step : StepField α X)
    (hpresence : ∀ u, presenceParent (step u))
    (u : TreeNode α) (hu : u ∈ (realizedTree step hpresence).carrier) :
    (markedTree step hpresence).mark u hu =
      displaceRoot step u := rfl

namespace ParentClosedBranchingWalk

variable {α X : Type*} [LT α]

/-- The realized tree of a presence-closed step field. -/
def toTree (step : ParentClosedBranchingWalk α X) : UlamHarris.Tree α :=
  realizedTree step.1 step.2

@[simp] theorem toTree_carrier (step : ParentClosedBranchingWalk α X) :
    step.toTree.carrier = {u | realizedNode step.1 u} := rfl

@[simp] theorem mem_toTree_iff (step : ParentClosedBranchingWalk α X)
    (u : TreeNode α) :
    u ∈ step.toTree.carrier ↔ realizedNode step.1 u := Iff.rfl

/-- The marked tree of a presence-closed step field: every realized address
carries its displacement. -/
def toMarkedTree [AddCommMonoid X] (step : ParentClosedBranchingWalk α X) :
    MarkedTree α X :=
  markedTree step.1 step.2

@[simp] theorem toMarkedTree_tree [AddCommMonoid X]
    (step : ParentClosedBranchingWalk α X) :
    step.toMarkedTree.tree = step.toTree := rfl

@[simp] theorem toMarkedTree_mark [AddCommMonoid X]
    (step : ParentClosedBranchingWalk α X) (u : TreeNode α)
    (hu : u ∈ step.toTree.carrier) :
    step.toMarkedTree.mark u hu = displaceRoot step.1 u := rfl

end ParentClosedBranchingWalk

namespace StandardBranchingWalk

variable {α X : Type*} [LT α] [LE X]

/-- The realized tree of a standard branching walk. -/
def toTree (step : StandardBranchingWalk α X) : UlamHarris.Tree α :=
  realizedTree step.1 step.2.2

@[simp] theorem toTree_carrier (step : StandardBranchingWalk α X) :
    step.toTree.carrier = {u | realizedNode step.1 u} := rfl

@[simp] theorem mem_toTree_iff (step : StandardBranchingWalk α X) (u : TreeNode α) :
    u ∈ step.toTree.carrier ↔ realizedNode step.1 u := Iff.rfl

/-- The marked tree of a standard branching walk. -/
def toMarkedTree [AddCommMonoid X] (step : StandardBranchingWalk α X) :
    MarkedTree α X :=
  markedTree step.1 step.2.2

@[simp] theorem toMarkedTree_tree [AddCommMonoid X] (step : StandardBranchingWalk α X) :
    step.toMarkedTree.tree = step.toTree := rfl

@[simp] theorem toMarkedTree_mark [AddCommMonoid X] (step : StandardBranchingWalk α X)
    (u : TreeNode α) (hu : u ∈ step.toTree.carrier) :
    step.toMarkedTree.mark u hu = displaceRoot step.1 u := rfl

end StandardBranchingWalk

end BranchingWalk

end MeasureTheory
