import Probability.BranchingRandomWalk.Walk.Path.Corridor.Horizontal
import Probability.Distributions.Moments.Real

/-!
# Variance scaling for horizontal-tube rates

A centered increment law with second moment `sigma²` is reduced to unit second
moment by dividing every increment by `sigma`.  This file records the exact
probability identity and transports any normalized logarithmic limit back to
the original spatial scale.
-/

open Filter MeasureTheory Topology

namespace ProbabilityTheory.RandomWalk

/-- A normalized logarithmic tube limit for standardized increments becomes
`sigma²` times that limit at the original spatial scale. -/
theorem tendsto_scaledLog_horizontalTubeProbability_of_map_div
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (a sigma constant : ℝ) (hsigma : 0 < sigma)
    (scale : ℕ → ℝ) (time : ℕ → ℕ)
    (hlimit : Tendsto (fun n =>
      (scale n / sigma) ^ 2 / (time n : ℝ) *
        Real.log (horizontalTubeProbability
          (independentIncrementLaw (ν.map fun x => x / sigma))
          a (scale n / sigma) (time n)).toReal)
      atTop (nhds constant)) :
    Tendsto (fun n =>
      scale n ^ 2 / (time n : ℝ) *
        Real.log (horizontalTubeProbability
          (independentIncrementLaw ν) a (scale n) (time n)).toReal)
      atTop (nhds (sigma ^ 2 * constant)) := by
  have hconstant : Tendsto (fun _ : ℕ => sigma ^ 2) atTop
      (nhds (sigma ^ 2)) := tendsto_const_nhds
  have hscaled := hconstant.mul hlimit
  convert hscaled using 1
  · funext n
    rw [horizontalTubeProbability_map_div ν a (scale n) (time n) hsigma]
    field_simp [hsigma.ne']


end ProbabilityTheory.RandomWalk
