import Probability.BranchingRandomWalk.Walk.FunctionalLimit.NormalizedStep
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Stable.Scale

/-!
# Stable functional-limit adapter

The functional-limit predicate and its corridor consequences are generic.
This module keeps the stable route's historical name as a thin specialization
so stable-law files can state their input without duplicating the interface.
-/

open Filter MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk

abbrev IsStableFunctionalLimit {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (normalization : ℕ → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (limit : Ω → CadlagPath unitInterval ℝ) : Prop :=
  IsNormalizedStepFunctionalLimit (Ω := Ω) ν normalization P limit

end ProbabilityTheory.RandomWalk
