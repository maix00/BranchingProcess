import Probability.BranchingRandomWalk.Walk.FunctionalLimit.Donsker.Skorokhod
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.FunctionalLimit.Endpoint

/-!
# Brownian corridor bounds with an endpoint constraint

This file specializes the open endpoint-constrained Portmanteau bound to the
verified Donsker theorem for centered unit-variance increments.
-/

open Filter MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- Brownian mass in a centered open corridor ending in an open interval
bounds the matching finite random-walk events from below in the limit. -/
theorem brownian_centeredSkorokhodCorridorEndsIn_le_liminf_strictTubeEndsIn
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {width endpointLower endpointUpper : ℝ} (hwidth : 0 < width) :
    P.map (Skorokhod.ofContinuousMap ∘
        continuousUnitIntervalPath B hcontinuous)
        (Skorokhod.rangeInOpenIntervalEndsIn
          (-(width / 2)) (width / 2) endpointLower endpointUpper) ≤
      atTop.liminf (fun n : ℕ =>
        independentIncrementLaw ν {increment |
          InOpenHorizontalTube (1 / 2) (width * Real.sqrt n) n increment ∧
            partialSum n increment / Real.sqrt n ∈
              Set.Ioo endpointLower endpointUpper}) := by
  apply measure_centeredSkorokhodCorridorEndsIn_le_liminf_strictTubeEndsIn_of_functionalLimit
    P ν (fun n => Real.sqrt n)
    (limit := Skorokhod.ofContinuousMap ∘
      continuousUnitIntervalPath B hcontinuous)
    (width := width)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  · exact tendstoInDistribution_normalizedStepCadlagPath_brownian
      ν hν.1 hν.2 hB hcontinuous hmeasurable
  · exact hwidth

end ProbabilityTheory.RandomWalk
