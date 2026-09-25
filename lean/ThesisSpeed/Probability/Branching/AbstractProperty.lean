import ThesisSpeed.Probability.Genealogy.BranchingStepTree

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

def subtreeStepField {X : Type*} (u : TreeNode)
    (ω : TreeNode → BranchingStep ℕ X) :
    TreeNode → BranchingStep ℕ X :=
  fun v => ω (u ++ v)

theorem subtreeStepField_measurable
    {X : Type*} [MeasurableSpace X] (u : TreeNode) :
    Measurable (subtreeStepField (X := X) u) := by
  apply measurable_pi_iff.mpr
  intro v
  exact measurable_pi_apply (u ++ v)

theorem subtreeStepField_law
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (u : TreeNode) :
    (branchingStepFieldLaw μ).map (subtreeStepField (X := X) u) =
      branchingStepFieldLaw μ := by
  change (Measure.infinitePi (fun _ : TreeNode => μ)).map
    (fun ω v => ω (u ++ v)) = Measure.infinitePi (fun _ : TreeNode => μ)
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : TreeNode => μ)
    (f := fun v : TreeNode => u ++ v)
    (fun _ _ h => List.append_cancel_left h)

theorem subtreeStepField_position_decomposition
    {X : Type*} [AddCommMonoid X]
    (ω : TreeNode → BranchingStep ℕ X) (u v : TreeNode) :
    branchingStepAccumulatedMark ω (u ++ v) =
      branchingStepAccumulatedMark ω u +
        branchingStepAccumulatedMark (subtreeStepField u ω) v := by
  exact branchingStepAccumulatedMark_append ω u v

end ThesisSpeed
