import ThesisSpeed.Probability.Genealogy.BranchingPositions

/-!
# Abstract genealogical positions

The position of a node is the cumulative displacement supplied by the
branching-step field along its address.  Concrete weighted-slot or point-
process realizations live under `PointProcess/Legacy` until migrated.
-/

namespace ThesisSpeed

abbrev DisplacementTree (X : Type*) := TreeNode → X

def displacementTreeOfSteps {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) : DisplacementTree X :=
  fun u => branchingNodeDisplacement step u

@[simp] theorem displacementTreeOfSteps_apply {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) (u : TreeNode) :
    displacementTreeOfSteps step u = branchingNodeDisplacement step u := rfl

end ThesisSpeed
