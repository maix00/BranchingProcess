import Probability.BranchingRandomWalk.Step.Law
import Combinatorics.BranchingWalk.Basic.Displace
import Probability.BranchingRandomWalk.Tree.Filtration

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



def subtreeStepField {α X : Type*} (u : TreeNode α)
    (ω : TreeNode α → Step α X) :
    TreeNode α → Step α X :=
  fun v => ω (u ++ v)

theorem subtreeStepField_measurable
    {α X : Type*} [MeasurableSpace X] (u : TreeNode α) :
    Measurable (subtreeStepField (X := X) u) := by
  apply measurable_pi_iff.mpr
  intro v
  exact measurable_pi_apply (u ++ v)

theorem subtreeStepField_law
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (u : TreeNode α) :
    (stepFieldLaw μ).map (subtreeStepField (X := X) u) =
      stepFieldLaw μ := by
  change (Measure.infinitePi (fun _ : TreeNode α => μ)).map
    (fun ω v => ω (u ++ v)) =
      Measure.infinitePi (fun _ : TreeNode α => μ)
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : TreeNode α => μ)
    (f := fun v : TreeNode α => u ++ v)
    (fun _ _ h => List.append_cancel_left h)

theorem subtreeStepField_position_decomposition
    {α X : Type*} [AddCommMonoid X]
    (ω : TreeNode α → Step α X) (u v : TreeNode α) :
    displace ω [] (u ++ v) =
      displace ω [] u +
        displace (subtreeStepField u ω) [] v := by
  rw [displace_append, List.nil_append]
  congr 1
  rw [show subtreeStepField u ω = (fun x => ω (u ++ x)) from rfl]
  simpa only [List.append_nil] using
    (displace_rebase ω u ([] : TreeNode α) v).symm

end ProbabilityTheory.BranchingRandomWalk
