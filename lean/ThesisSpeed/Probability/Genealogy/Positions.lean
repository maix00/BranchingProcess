import ThesisSpeed.Probability.Genealogy.BranchingPositions

/-!
# Abstract genealogical positions

The position of a node is the cumulative displacement supplied by the
branching-step field along its address.  Concrete weighted-slot or point-
process realizations live under `PointProcess/Legacy` until migrated.
-/

namespace ThesisSpeed

abbrev DisplacementField (X : Type*) := TreeNode → X

def displacementFieldOfSteps {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) : DisplacementField X :=
  fun u => branchingStepAccumulatedMark step u

@[simp] theorem displacementFieldOfSteps_apply {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) (u : TreeNode) :
    displacementFieldOfSteps step u = branchingStepAccumulatedMark step u := rfl

end ThesisSpeed
