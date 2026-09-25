import ThesisSpeed.Probability.Genealogy.MarkedTree

/-!
# Positions induced by abstract branching steps

This file is the abstract replacement for the old weighted-slot position
definitions.  A node position is the sum of the step increments along its
root path; no point-process or survival convention is involved here.
-/

namespace ThesisSpeed

def branchingNodePosition {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) (u : TreeNode) : X :=
  branchingTreePathSum step u

@[simp] theorem branchingNodePosition_eq_pathSum
    {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) (u : TreeNode) :
    branchingNodePosition step u = branchingTreePathSum step u := rfl

theorem branchingNodePosition_nil
    {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) :
  branchingNodePosition step [] = 0 := by
  exact branchingTreePathSum_nil step

theorem branchingNodePosition_append_singleton
    {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) (u : TreeNode) (i : ℕ) :
    branchingNodePosition step (u ++ [i]) =
      branchingNodePosition step u +
        branchingStepIncrement (step u) i := by
  exact branchingTreePathSum_append_singleton step u i

def branchingRealizedNode {X : Type*}
    (step : TreeNode → BranchingStep ℕ X) (u : TreeNode) : Prop :=
  ∀ j ∈ Finset.range u.length,
    branchingStepPresent (step (u.take j)) (u[j]!)

theorem branchingRealizedNode_nil {X : Type*}
    (step : TreeNode → BranchingStep ℕ X) :
    branchingRealizedNode step [] := by
  simp [branchingRealizedNode]

end ThesisSpeed
