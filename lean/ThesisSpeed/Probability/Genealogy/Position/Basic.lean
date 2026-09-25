import ThesisSpeed.Probability.Genealogy.Position.Measurability

/-!
# Abstract genealogical positions

The position of a node is the cumulative displacement supplied by the
branching-step field along its address. Concrete slot realizations of an
offspring point process live under `Probability/PointProcess/Slot`.
-/

namespace ThesisSpeed

abbrev DisplacementField (X : Type*) := 𝕍 → X

def displacementFieldOfSteps {X : Type*} [AddCommMonoid X]
    (step : 𝕍 → BranchingStep ℕ X) : DisplacementField X :=
  fun u => branchingStepAccumulatedMark step u

@[simp] theorem displacementFieldOfSteps_apply {X : Type*} [AddCommMonoid X]
    (step : 𝕍 → BranchingStep ℕ X) (u : 𝕍) :
    displacementFieldOfSteps step u = branchingStepAccumulatedMark step u := rfl

end ThesisSpeed
