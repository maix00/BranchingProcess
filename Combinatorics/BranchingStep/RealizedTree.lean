import Combinatorics.BranchingStep.AccumulatedMark
import Combinatorics.BranchingStep.Prefix
import Combinatorics.BranchingStep.Realization

/-!
# The realized tree of an ordered step field

`branchingRealizedTree step hordered` is the deterministic tree whose carrier
is exactly the realized addresses; the ordered-sibling axiom follows from the
presence-prefix half of `OrderedBranchingStep`. `branchingStepMarkedTree` then
marks every realized node by its accumulated mark, which is the bridge from
the step field to the `MarkedTree` object of the paper.
-/

namespace BranchingStep

open UlamHarris



/-- The deterministic tree realized by an ordered step field. -/
def branchingRealizedTree {α X : Type*} [LT α] [LE X]
    (step : BranchingStepField α X)
    (hordered : ∀ u, OrderedBranchingStep (step u)) : GenealogicalTree α where
  carrier := {u | branchingRealizedNode step u}
  root_mem := branchingRealizedNode_nil step
  prefix_closed := by
    intro u v huv
    change branchingRealizedNode step (u ++ v) at huv
    exact (branchingRealizedNode_append_iff step u v).1 huv |>.1
  sibling_closed := by
    intro u i j hj hij
    change branchingRealizedNode step (u ++ [j]) at hj
    rw [branchingRealizedNode_append_singleton_iff] at hj
    exact (branchingRealizedNode_append_singleton_iff step u i).2
      ⟨hj.1, branchingStep_present_of_later (step u) (hordered u).1 hij hj.2⟩

@[simp] theorem branchingRealizedTree_carrier {α X : Type*} [LT α] [LE X]
    (step : BranchingStepField α X)
    (hordered : ∀ u, OrderedBranchingStep (step u)) :
    (branchingRealizedTree step hordered).carrier =
      {u | branchingRealizedNode step u} := rfl

@[simp] theorem mem_branchingRealizedTree_iff {α X : Type*} [LT α] [LE X]
    (step : BranchingStepField α X)
    (hordered : ∀ u, OrderedBranchingStep (step u)) (u : TreeNode α) :
    u ∈ (branchingRealizedTree step hordered).carrier ↔
      branchingRealizedNode step u := Iff.rfl

/-- The marked tree of an ordered step field: the realized addresses carry
their accumulated marks. This is the bridge from the step field to the
tree-with-marks object; both the realized tree and the marks are derived from
the field. -/
def branchingStepMarkedTree {α X : Type*} [AddCommMonoid X] [LT α] [LE X]
    (step : BranchingStepField α X)
    (hordered : ∀ u, OrderedBranchingStep (step u)) : MarkedTree α X where
  tree := branchingRealizedTree step hordered
  mark := fun u _ => branchingStepAccumulatedMark step u

@[simp] theorem branchingStepMarkedTree_tree {α X : Type*} [AddCommMonoid X]
    [LT α] [LE X] (step : BranchingStepField α X)
    (hordered : ∀ u, OrderedBranchingStep (step u)) :
    (branchingStepMarkedTree step hordered).tree =
      branchingRealizedTree step hordered := rfl

@[simp] theorem branchingStepMarkedTree_mark {α X : Type*} [AddCommMonoid X]
    [LT α] [LE X] (step : BranchingStepField α X)
    (hordered : ∀ u, OrderedBranchingStep (step u))
    (u : TreeNode α) (hu : u ∈ (branchingRealizedTree step hordered).carrier) :
    (branchingStepMarkedTree step hordered).mark u hu =
      branchingStepAccumulatedMark step u := rfl

end BranchingStep
