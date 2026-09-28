import Combinatorics.BranchingWalk.Walk.Path.Skorokhod.Corridor
import Probability.BranchingRandomWalk.Walk.Path.Skorokhod

/-!
# Corridor laws for càdlàg random-walk paths

This file lifts the deterministic identification of a positive-margin
Skorokhod corridor with a strict finite tube to the canonical IID path law.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching.Walk

theorem normalizedStepPathLaw_apply_rangeInOpenInterval
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (hscale : 0 < scale n)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    normalizedStepPathLaw nu scale n
        (Skorokhod.rangeInOpenInterval (-a) (1 - a)) =
      independentIncrementLaw nu
        {increment | InOpenHorizontalTube a (scale n) n increment} := by
  rw [normalizedStepPathLaw, Measure.map_apply]
  · congr 1
    ext increment
    exact normalizedStepCadlagPathIcc_mem_rangeInOpenInterval_iff
      scale hn hscale ha haOne increment
  · exact measurable_normalizedStepCadlagPathIcc scale n
  · exact Skorokhod.measurableSet_rangeInOpenInterval (-a) (1 - a)

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
