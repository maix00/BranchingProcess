import Combinatorics.BranchingWalk.Walk.Path.Interpolation.Corridor
import Probability.BranchingRandomWalk.Walk.Path.Interpolation

/-!
# Corridor laws for polygonally interpolated random walks

This file lifts the deterministic grid/corridor equivalence to the canonical
IID path law.  It introduces no second probability notion for tubes: the
right-hand side is simply the measure of the strict finite tube event.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching.Walk

/-- The mass assigned by the polygonal path law to an open horizontal
corridor is exactly the IID increment probability of the corresponding
strict grid tube. -/
theorem normalizedLinearPathLaw_apply_rangeInOpenInterval
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (hscale : 0 < scale n)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    normalizedLinearPathLaw nu scale n
        (ContinuousMap.rangeInOpenInterval (-a) (1 - a)) =
      independentIncrementLaw nu
        {increment | InOpenHorizontalTube a (scale n) n increment} := by
  rw [normalizedLinearPathLaw, Measure.map_apply]
  · congr 1
    ext increment
    exact normalizedLinearContinuousPathIcc_mem_horizontalCorridor_iff
      scale hn hscale ha haOne increment
  · exact measurable_normalizedLinearContinuousPathIcc scale n
  · exact ContinuousMap.measurableSet_rangeInOpenInterval (by linarith)

/-- The mass assigned by the polygonal path law to a closed horizontal
corridor is exactly the IID increment probability of the corresponding weak
grid tube. -/
theorem normalizedLinearPathLaw_apply_rangeInClosedInterval
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (hscale : 0 < scale n)
    {a : ℝ} (ha : 0 ≤ a) (haOne : a ≤ 1) :
    normalizedLinearPathLaw nu scale n
        (ContinuousMap.rangeInClosedInterval (-a) (1 - a)) =
      independentIncrementLaw nu
        {increment | InHorizontalTube a (scale n) n increment} := by
  rw [normalizedLinearPathLaw, Measure.map_apply]
  · congr 1
    ext increment
    exact normalizedLinearContinuousPathIcc_mem_closedHorizontalCorridor_iff
      scale hn hscale ha haOne increment
  · exact measurable_normalizedLinearContinuousPathIcc scale n
  · exact ContinuousMap.measurableSet_rangeInClosedInterval (-a) (1 - a)

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
