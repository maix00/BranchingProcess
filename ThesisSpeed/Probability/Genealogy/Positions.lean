import ThesisSpeed.Probability.Genealogy.BranchingPositions

/-!
# Abstract genealogical positions

The position of a node is the cumulative displacement supplied by the
branching-step field along its address.  Concrete weighted-slot or point-
process realizations live under `PointProcess/Legacy` until migrated.
-/

namespace ThesisSpeed

abbrev PositionTree (X : Type*) := TreeNode → X

def positionTreeOfSteps {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) : PositionTree X :=
  fun u => branchingNodePosition step u

@[simp] theorem positionTreeOfSteps_apply {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) (u : TreeNode) :
    positionTreeOfSteps step u = branchingNodePosition step u := rfl

end ThesisSpeed
