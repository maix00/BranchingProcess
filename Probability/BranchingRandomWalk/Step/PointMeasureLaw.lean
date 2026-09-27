import Probability.BranchingRandomWalk.Step.Basic

/-!
# Laws of deterministic point-measure observations

These are pushforward identities for the point measure of `Ξ`. They are kept
separate from the branching-random-walk many-to-one theorem, which concerns a
size-biased spine path across generations.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching

theorem stepPointMeasureLaw_forward
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι] [Zero X] (Ξ : Step Ω ι X) (P : Measure Ω) :
    (Ξ.law P).map stepPointMeasure = P.map Ξ.pointMeasure :=
  Ξ.map_pointMeasure_law P

theorem stepPointMeasureLaw_backward
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι] [Zero X] (Ξ : Step Ω ι X) (P : Measure Ω) :
    P.map Ξ.pointMeasure = (Ξ.law P).map stepPointMeasure :=
  (Ξ.map_pointMeasure_law P).symm

theorem lintegral_stepPointMeasure
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι] [Zero X] (Ξ : Step Ω ι X) (P : Measure Ω)
    (F : Measure X → ENNReal) (hF : Measurable F) :
    ∫⁻ η, F η ∂(P.map Ξ.pointMeasure) =
      ∫⁻ ω, F (stepPointMeasure (Ξ ω)) ∂P := by
  exact MeasureTheory.lintegral_map
    hF Ξ.pointMeasure_measurable

end ProbabilityTheory.BranchingRandomWalk
