import Combinatorics.BranchingWalk.Walk.Path.Skorokhod.Corridor.Endpoint
import Probability.BranchingRandomWalk.Walk.Path.Skorokhod

/-!
# Laws of endpoint-constrained walk corridors

The normalized path law of an open Skorokhod corridor with a terminal
constraint is identified with the corresponding finite strict-tube event.
-/

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

theorem normalizedStepPathLaw_apply_centeredOpenIntervalEndsIn
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (hscale : 0 < scale n)
    {width endpointLower endpointUpper : ℝ} (hwidth : 0 < width) :
    normalizedStepPathLaw ν scale n
        (Skorokhod.rangeInOpenIntervalEndsIn
          (-(width / 2)) (width / 2) endpointLower endpointUpper) =
      independentIncrementLaw ν {increment |
        InOpenHorizontalTube (1 / 2) (width * scale n) n increment ∧
          partialSum n increment / scale n ∈
            Set.Ioo endpointLower endpointUpper} := by
  rw [normalizedStepPathLaw, Measure.map_apply]
  · congr 1
    ext increment
    exact normalizedStepCadlagPathIcc_mem_centeredOpenIntervalEndsIn_iff
      scale hn hscale hwidth increment
  · exact measurable_normalizedStepCadlagPathIcc scale n
  · exact Skorokhod.measurableSet_rangeInOpenIntervalEndsIn
      (-(width / 2)) (width / 2) endpointLower endpointUpper

theorem normalizedStepPathLaw_apply_centeredClosedIntervalEndsIn
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (hscale : 0 < scale n)
    {width endpointLower endpointUpper : ℝ} (hwidth : 0 ≤ width) :
    normalizedStepPathLaw ν scale n
        (Skorokhod.rangeInClosedIntervalEndsIn
          (-(width / 2)) (width / 2) endpointLower endpointUpper) =
      independentIncrementLaw ν {increment |
        InHorizontalTube (1 / 2) (width * scale n) n increment ∧
          partialSum n increment / scale n ∈
            Set.Icc endpointLower endpointUpper} := by
  rw [normalizedStepPathLaw, Measure.map_apply]
  · congr 1
    ext increment
    exact normalizedStepCadlagPathIcc_mem_centeredClosedIntervalEndsIn_iff
      scale hn hscale hwidth increment
  · exact measurable_normalizedStepCadlagPathIcc scale n
  · exact Skorokhod.measurableSet_rangeInClosedIntervalEndsIn
      (-(width / 2)) (width / 2) endpointLower endpointUpper

end ProbabilityTheory.RandomWalk
