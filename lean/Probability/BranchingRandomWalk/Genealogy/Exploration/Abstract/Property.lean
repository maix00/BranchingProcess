import Probability.BranchingRandomWalk.Step.Law
import Combinatorics.BranchingStep.Position.Accumulate
import Probability.BranchingRandomWalk.Tree.Filtration

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory



def subtreeStepField {X : Type*} (u : 𝕍)
    (ω : 𝕍 → Step ℕ X) :
    𝕍 → Step ℕ X :=
  fun v => ω (u ++ v)

theorem subtreeStepField_measurable
    {X : Type*} [MeasurableSpace X] (u : 𝕍) :
    Measurable (subtreeStepField (X := X) u) := by
  apply measurable_pi_iff.mpr
  intro v
  exact measurable_pi_apply (u ++ v)

theorem subtreeStepField_law
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (u : 𝕍) :
    (stepFieldLaw μ).map (subtreeStepField (X := X) u) =
      stepFieldLaw μ := by
  change (Measure.infinitePi (fun _ : 𝕍 => μ)).map
    (fun ω v => ω (u ++ v)) = Measure.infinitePi (fun _ : 𝕍 => μ)
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : 𝕍 => μ)
    (f := fun v : 𝕍 => u ++ v)
    (fun _ _ h => List.append_cancel_left h)

theorem subtreeStepField_position_decomposition
    {X : Type*} [AddCommMonoid X]
    (ω : 𝕍 → Step ℕ X) (u v : 𝕍) :
    accumulateRoot ω (u ++ v) =
      accumulateRoot ω u +
        accumulateRoot (subtreeStepField u ω) v := by
  exact accumulateRoot_append ω u v

end ProbabilityTheory.BranchingRandomWalk
