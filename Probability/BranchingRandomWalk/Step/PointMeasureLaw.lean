import Probability.BranchingRandomWalk.Step.Basic

/-!
# Laws of deterministic point-measure observations

These are pushforward identities for the point measure of `S`. They are kept
separate from the branching-random-walk many-to-one theorem, which concerns a
size-biased spine path across generations.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching

theorem stepPointMeasureLaw_forward
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι] [Zero X] (S : Step Ω ι X) (P : Measure Ω) :
    (S.indexedLaw P).map stepPointMeasure = S.branchingLaw P :=
  S.indexedLaw_map_pointMeasure P

theorem stepPointMeasureLaw_backward
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι] [Zero X] (S : Step Ω ι X) (P : Measure Ω) :
    S.branchingLaw P = (S.indexedLaw P).map stepPointMeasure :=
  (S.indexedLaw_map_pointMeasure P).symm

theorem lintegral_stepPointMeasure
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι] [Zero X] (S : Step Ω ι X) (P : Measure Ω)
    (F : Measure X → ENNReal) (hF : Measurable F) :
    ∫⁻ η, F η ∂(S.branchingLaw P) =
      ∫⁻ ω, F (stepPointMeasure (S ω)) ∂P := by
  unfold Step.branchingLaw
  exact MeasureTheory.lintegral_map
    hF S.pointMeasure_measurable

end ProbabilityTheory.BranchingRandomWalk
